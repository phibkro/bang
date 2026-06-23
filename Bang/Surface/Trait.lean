/-
  Bang/Surface/Trait.lean — first-class, enforced, algebraic-interface LAWS.
  ─────────────────────────────────────────────────────────────────────────
  THE surface for traits-with-laws (design-space #5; ADR-0026/0027). A trait is
  OPS + LAWS — "structure, not content" (an algebraic theory). A type is an
  instance iff it provides the operations AND satisfies the equations. The
  hierarchy `eq → preorder → order` composes by EXTENSION: each rung carries the
  prior rung's laws.

      trait Order : Preorder { fn le(a,b)->Bool; law antisym: le a b & le b a => a==b }
      impl Order for Int     { fn le(a,b) = a <= b }

  Monomorphic (ADR-0027 stage 1): concrete instances, DIRECT dispatch — an op is
  an ordinary Lean function producing a kernel `Comp`/`Val`, run through
  `Source.eval` (the verified reference). No vtable, no polymorphism (next phase).

  ── The discharge ladder (ADR-0026, proof-first amendment) ───────────────────
  A `law` lowers to a PROOF OBLIGATION. Discharge is PROOF-FIRST:

      verified  a PROOF  (`rfl`/`simp`/`grind`/`decide` on the lowered defs)   ← DEFAULT
      tested    an explicit DESCENT (`Descend.test` / `Descend.assert`), a      ← marked
                `plausible` property test — used when a proof is not (yet) spent

  This REVERSES ADR-0026's test-DEFAULT (the main loop is amending the ADR for
  the laws surface: proof is cheap for simple algebraic laws on lowered defs, so
  it is the default; descent is the marked, deliberate step down). The "no silent
  pass" rule is enforced BY CONSTRUCTION: a `Law` carries its evidence as data —
  a proof term XOR a descent marker. A law with neither cannot be *constructed*,
  so an unproven, un-descended law is a TYPE error at elaboration, not a runtime
  check (SOUL: make the bad state unrepresentable). `lawHolds`/`#guard` then
  surface a descended (tested-rung) law VISIBLY, so descent is never silent.

  This module is ADDITIVE surface sugar over the existing kernel — zero kernel
  edits. Direct dispatch = a direct call; a `law` = a discharged `Prop`.
-/

import Bang.Surface

namespace Bang.Surface.Trait

open Bang
open Bang.Surface

/-! ## 1. The discharge ladder as DATA (correctness by construction)

A `law`'s evidence is a value of `Evidence P` for the law's proposition `P`.
There are exactly two rungs, and BOTH carry their justification:

  * `Evidence.proof  (h : P)`     — the verified rung (proof-first DEFAULT).
  * `Evidence.descend (d : Descend P)` — the tested rung, an EXPLICIT marked descent.

There is NO third constructor — no "trust me" rung — so a law with no evidence
is unrepresentable. That is the "no silent pass" rule, made structural. -/

/-- An explicit, MARKED descent off the verified rung (ADR-0026 §5: descent is
never silent). `test`/`assert` mirror the surface keywords: `test` descends to a
`plausible` property test, `assert` to a runtime assertion. Carries `reason` so a
reader sees WHY the proof was not spent — the descent is documented at its site. -/
inductive Descend (P : Prop) where
  | test   (reason : String) : Descend P     -- descend to a `plausible` property test
  | assert (reason : String) : Descend P     -- descend to a runtime assertion
  deriving Inhabited

/-- The evidence a `law` carries. Proof-first: `proof` is the verified rung (the
DEFAULT); `descend` is the marked tested rung. No silent third rung. -/
inductive Evidence (P : Prop) where
  | proof   (h : P)          : Evidence P     -- VERIFIED rung — the default
  | descend (d : Descend P)  : Evidence P     -- TESTED rung — explicit marked descent

/-- A first-class `law`: its proposition together with its discharge evidence.
Bundling `prop` with `evidence` is the enforcement — you cannot have a `Law`
without discharging it one way or the other. -/
structure Law where
  name     : String
  {prop    : Prop}
  evidence : Evidence prop

/-- Is this law on the VERIFIED rung (discharged by a proof)? Used by the harness
to REPORT the rung of each law (so a tested-rung descent is visible, not silent). -/
def Law.isVerified (l : Law) : Bool :=
  match l.evidence with
  | .proof _   => true
  | .descend _ => false

/-- The descent reason, if this law descended (else `none`). Surfaces the marked
descent for the harness's visibility report. -/
def Law.descentReason (l : Law) : Option String :=
  match l.evidence with
  | .proof _              => none
  | .descend (.test r)    => some s!"test: {r}"
  | .descend (.assert r)  => some s!"assert: {r}"

/-- Smart constructor: a law discharged PROOF-FIRST. `mkVerified "antisym" h`
records the proof `h : P` on the verified rung. This is the default path. -/
def mkVerified (name : String) {P : Prop} (h : P) : Law :=
  { name := name, prop := P, evidence := .proof h }

/-- Smart constructor: a law that EXPLICITLY DESCENDS to the tested rung. The
descent is MARKED (the `Descend` value) and documented (`reason`) — never silent.
The accompanying `#test`/property check lives at the use site (see §4). -/
def mkTested (name : String) (P : Prop) (reason : String) : Law :=
  { name := name, prop := P, evidence := .descend (.test reason) }


/-! ## 2. The interface hierarchy `eq → preorder → order` (ops + laws)

Each trait is a structure bundling its OPERATIONS (monomorphic — concrete `Int`
in/out, lowered to run through the kernel) and its LAWS (`Law` values, so every
instance MUST discharge them). The hierarchy composes by EXTENSION: `Preorder`
contains an `Eq`, `Order` contains a `Preorder` — the sub-trait's laws ride along.

The operations are `Int → Int → Bool` at the META level here (the monomorphic
instance is concrete), but each op is BACKED by a kernel computation we RUN
through `Source.eval` (§3) — so "the instance satisfies the law" is checked
against the verified reference interpreter, not just Lean's `Int` `≤`. -/

/-- `trait Eq { fn eq(a,b)->Bool; law refl: eq a a; law sym: eq a b => eq b a }`.
The base of the hierarchy: an equivalence-ish equality (refl + sym; trans folds in
at `Preorder` to keep the demo small). `op` is the concrete monomorphic operation. -/
structure EqT where
  op    : Int → Int → Bool
  refl  : Law              -- ∀ a, op a a = true
  sym   : Law              -- ∀ a b, op a b = true → op b a = true

/-- `trait Preorder : Eq { fn le(a,b)->Bool; law refl; law trans }`. EXTENDS `Eq`
(carries the `EqT` field, so an `Preorder` instance discharges `Eq`'s laws too).
Adds `le` with reflexivity + transitivity. -/
structure PreorderT where
  toEqT : EqT
  le    : Int → Int → Bool
  leRefl  : Law            -- ∀ a, le a a = true
  leTrans : Law            -- ∀ a b c, le a b → le b c → le a c

/-- `trait Order : Preorder { law antisym }`. EXTENDS `Preorder`; adds the
antisymmetry law that promotes a preorder to a (partial) order: `le a b ∧ le b a
→ eq a b`. The full hierarchy's laws are all in scope on an `OrderT`. -/
structure OrderT where
  toPreorderT : PreorderT
  antisym : Law            -- ∀ a b, le a b → le b a → eq a b


/-! ## 3. Operations BACKED by kernel computations (run via `Source.eval`)

The whole point of "interpreted-verified" (the brief's RUN requirement): an
operation is not just a Lean `Bool` — it is a kernel program. We encode an op's
result as a `Comp` returning `vint 1` (true) / `vint 0` (false), RUN it through
`Source.eval`, and read the verdict back. The laws (§4) are then stated over
THESE runs — the verified reference interpreter is the oracle.

We keep the concrete comparison delegated to Lean's `Int` order (the monomorphic
instance's *content*), but the op is REIFIED into the kernel and EXECUTED, so the
demo genuinely exercises `Source.eval`, not just host arithmetic. -/

/-- Reify a boolean into a kernel value: `true ↦ vint 1`, `false ↦ vint 0`.
(The kernel has no `Bool` type — five primitives — so `Int` is the carrier.) -/
def reifyBool (b : Bool) : Val := .vint (if b then 1 else 0)

/-- A kernel computation that simply returns the reified boolean. Trivial as a
`Comp`, but it makes the op's result FLOW THROUGH `Source.eval` (the RUN seam):
`runBoolComp (b) = done (vint (if b then 1 else 0))`. -/
def boolComp (b : Bool) : Comp := .ret (reifyBool b)

/-- `boolComp` runs to its reified value through the interpreter. PROVEN by `rfl`:
`Source.eval _ (.ret v) = .done v` definitionally (same shape as `Surface.pureComp`).
This is the RUN seam pinned as a lemma — the op's result genuinely flows through
`Source.eval`. -/
theorem boolComp_runs (b : Bool) : Source.eval 10 (boolComp b) = .done (reifyBool b) := by
  rfl

/-- RUN a boolean through the verified interpreter and read it back as a `Bool`.
`some true`/`some false` on a clean run; `none` if the kernel got stuck (never,
for `boolComp`). This is the op's executed verdict — the oracle's answer. -/
def runBool (b : Bool) : Option Bool :=
  match Source.eval 10 (boolComp b) with
  | .done (.vint 1) => some true
  | .done (.vint 0) => some false
  | _               => none

/-- `runBool` round-trips any boolean: running the reified value gives the boolean
back. PROVEN via `boolComp_runs` + a case split on `b`. This is the bridge that
lets the laws be stated over `Source.eval` (`runBool`) yet proven on the lowered
`Bool` defs. -/
theorem runBool_roundtrip (b : Bool) : runBool b = some b := by
  unfold runBool
  rw [boolComp_runs]
  cases b <;> rfl

/-- The op's verdict AS RUN THROUGH THE KERNEL. `intLeRun a b` reifies `a ≤ b`,
runs it via `Source.eval`, and returns the verdict. The `Int` instance's `le` is
`intLe`, and every law about it is checked against THIS run (interpreted-verified). -/
def intLe (a b : Int) : Bool := a ≤ b
def intEq (a b : Int) : Bool := a == b

/-- `intLe` agrees with its kernel RUN — the bridge lemma that lets the laws be
stated over `Source.eval` yet proven by `rfl`/`decide` on `intLe`. -/
theorem intLe_run (a b : Int) : runBool (intLe a b) = some (intLe a b) :=
  runBool_roundtrip _

theorem intEq_run (a b : Int) : runBool (intEq a b) = some (intEq a b) :=
  runBool_roundtrip _


/-! ## 4. `impl Order for Int` — the instance, laws discharged PROOF-FIRST

Every law is discharged on the VERIFIED rung by a Lean proof (`decide`/`simp`/
`omega`) over the lowered `intLe`/`intEq` defs. Because the ops agree with their
kernel runs (`intLe_run`/`intEq_run`), proving the law on the lowered def IS
proving it over `Source.eval` — interpreted-verified, no descent needed.

This is the proof-first default in action: simple algebraic laws on lowered defs
discharge by `decide`/`omega`, so NONE of these descends. -/

/-- `refl: ∀ a, eq a a` — proven by `simp` (`a == a` is `true`). -/
def intEqRefl : Law := mkVerified "eq.refl" (P := ∀ a : Int, intEq a a = true) (by
  intro a; simp [intEq])

/-- `sym: ∀ a b, eq a b → eq b a` — proven; `==` is symmetric on `Int`. -/
def intEqSym : Law := mkVerified "eq.sym"
    (P := ∀ a b : Int, intEq a b = true → intEq b a = true) (by
  intro a b h; simp_all [intEq])

/-- `le.refl: ∀ a, le a a` — `a ≤ a`, by `decide`-style `omega`. -/
def intLeRefl : Law := mkVerified "le.refl" (P := ∀ a : Int, intLe a a = true) (by
  intro a; simp [intLe])

/-- `le.trans: ∀ a b c, le a b → le b c → le a c` — transitivity of `≤`. -/
def intLeTrans : Law := mkVerified "le.trans"
    (P := ∀ a b c : Int, intLe a b = true → intLe b c = true → intLe a c = true) (by
  intro a b c hab hbc; simp_all [intLe]; omega)

/-- `antisym: ∀ a b, le a b → le b a → eq a b` — THE order law, by `omega`. -/
def intAntisym : Law := mkVerified "order.antisym"
    (P := ∀ a b : Int, intLe a b = true → intLe b a = true → intEq a b = true) (by
  intro a b hab hba; simp_all [intLe, intEq]; omega)

/-- The assembled instance: `Int` is an `Order`, every rung's laws discharged
proof-first. The hierarchy is visible — `intOrder.toPreorderT.toEqT` is the `Eq`
sub-instance, and its laws came along. -/
def intOrder : OrderT where
  toPreorderT := {
    toEqT := { op := intEq, refl := intEqRefl, sym := intEqSym }
    le := intLe
    leRefl := intLeRefl
    leTrans := intLeTrans
  }
  antisym := intAntisym

/-- Collect every law of an `OrderT` (the whole hierarchy, sub-traits included).
Used by the harness to REPORT the discharge rung of each — so a descent is visible. -/
def OrderT.laws (o : OrderT) : List Law :=
  [ o.toPreorderT.toEqT.refl, o.toPreorderT.toEqT.sym,
    o.toPreorderT.leRefl, o.toPreorderT.leTrans, o.antisym ]


/-! ## 5. The discharge HARNESS — proof-first, no silent pass

`allVerified` reports whether EVERY law is on the verified rung. `dischargeReport`
lists each law's rung (proof vs marked descent) so the tested rung is VISIBLE. The
`#guard`s below are the GREEN CHECK: `Int`'s order is fully proof-discharged, so
`allVerified intOrder.laws` is `true` and the build pins it. -/

/-- Are ALL these laws on the verified rung (proof-discharged)? `true` iff no law
descended. (A law with no evidence is unrepresentable, so this only distinguishes
proof from marked descent — never "unchecked".) -/
def allVerified (laws : List Law) : Bool := laws.all Law.isVerified

/-- A human-readable rung report: one line per law (`✓ proof` or `↓ <reason>`).
Makes the descent of any tested-rung law VISIBLE — the "no silent pass" guarantee
at the reporting layer (the construction layer already forbids "no evidence"). -/
def dischargeReport (laws : List Law) : List String :=
  laws.map fun l =>
    match l.descentReason with
    | none   => s!"✓ {l.name}: proof (verified)"
    | some r => s!"↓ {l.name}: DESCENT [{r}] (tested)"

-- GREEN CHECK: every law of `Int : Order` discharges PROOF-FIRST (verified rung).
#guard allVerified intOrder.laws
-- And there are exactly five laws across the eq→preorder→order hierarchy.
#guard intOrder.laws.length == 5


/-! ## 6. A small DATA STRUCTURE as a trait instance with ≥1 law (run via eval)

`OrderedPair` — a pair `(lo, hi)` with the INVARIANT `lo ≤ hi`, smart-constructed
by `mkPair` which orders its two inputs. It is an `Order` instance whose ≥1 law we
state OVER `Source.eval`: the pair is built as a kernel `pair` value, run through
the interpreter, and the law inspects the RESULT. THE interpreted-verified loop.

`leP (lo₁,hi₁) (lo₂,hi₂) := lo₁ ≤ lo₂` — lexicographic-ish order by the low element
(enough to carry a real law). The structure's moat law: `mkPair` always produces an
ORDERED pair (`lo ≤ hi`), proven over the value that `Source.eval` returns. -/

/-- Build the ordered pair `(min a b, max a b)` as a KERNEL value, and RUN it
through `Source.eval` so the result is the interpreter's output (not host-built).
`Comp` is `ret (pair (vint lo) (vint hi))`; the demo reads it back. -/
def mkPairComp (a b : Int) : Comp :=
  .ret (.pair (.vint (min a b)) (.vint (max a b)))

/-- Run `mkPairComp` and read back `(lo, hi)` (or `none` if stuck — never here). -/
def runPair (a b : Int) : Option (Int × Int) :=
  match Source.eval 10 (mkPairComp a b) with
  | .done (.pair (.vint lo) (.vint hi)) => some (lo, hi)
  | _                                   => none

/-- **The moat law (run via eval):** `mkPair` always yields an ORDERED pair —
for ALL `a b`, the pair `Source.eval` returns has `lo ≤ hi`. Stated over the
interpreter's output (`runPair`), discharged PROOF-FIRST by `omega` on `min`/`max`.
This is a real rep-invariant law on a data structure, checked against the verified
reference. -/
def orderedPairLaw : Law := mkVerified "OrderedPair.invariant"
    (P := ∀ a b : Int, ∃ lo hi, runPair a b = some (lo, hi) ∧ lo ≤ hi) (by
  intro a b
  refine ⟨min a b, max a b, ?_, ?_⟩
  · unfold runPair mkPairComp; rfl
  · omega)

-- GREEN CHECK: the data-structure law is on the VERIFIED rung (proof-first).
#guard orderedPairLaw.isVerified
-- RUN the structure through eval and pin a concrete result: mkPair 5 2 = (2, 5).
#guard (match runPair 5 2 with | some (2, 5) => true | _ => false)
#guard (match runPair 2 5 with | some (2, 5) => true | _ => false)
-- The invariant holds on the run output for a sampled input (lo ≤ hi).
#guard (match runPair 9 1 with | some (lo, hi) => decide (lo ≤ hi) | _ => false)


/-! ## 7. ONE explicit DESCENT — proving the marked tested rung WORKS + is visible

To validate that the descent path is real (not just the proof path), we state one
law via `mkTested` — an EXPLICIT, MARKED descent to the tested rung — and back it
with a `plausible` `#test`. This is the SAME law as `intLeTrans` (transitivity),
deliberately re-discharged by sampling to exercise the descent machinery. In real
use you'd descend only when a proof is genuinely out of reach; here it demonstrates
the seam. The descent is VISIBLE in `dischargeReport` (it prints `↓ … DESCENT`). -/

open Plausible

/-- The transitivity law, DESCENDED to the tested rung (marked, with a reason).
`isVerified` is `false`; `dischargeReport` prints it as a descent — never silent. -/
def intLeTransTested : Law :=
  mkTested "le.trans (descended)"
    (∀ a b c : Int, intLe a b = true → intLe b c = true → intLe a c = true)
    "demonstrates the explicit tested-rung descent seam"

-- The descent is VISIBLE: this law reports as tested, not verified.
#guard !intLeTransTested.isVerified
#guard (match intLeTransTested.descentReason with | some _ => true | none => false)

-- The `plausible` property test that BACKS the descent (the tested-rung check).
-- `#test` samples and throws at elaboration on a counter-example (build-fail).
#test ∀ a b c : Int, !(intLe a b && intLe b c) || intLe a c

/-! ## 8. The discharge report — the loop's VISIBLE output

A mixed bag: the five proof-discharged `Int : Order` laws plus the one descended
law, so `dischargeReport` shows BOTH rungs. `#eval` prints it at build for a human;
the `#guard`s pin the rung counts so a regression (e.g. a law silently changing
rung) fails the build. -/

/-- The full report over `Int`'s order laws + the one descended law. -/
def fullReport : List String :=
  dischargeReport (intOrder.laws ++ [intLeTransTested])

#eval fullReport  -- prints the per-law rung lines at build (human-visible)

-- Pin the rung split: 5 verified (proof-first default), 1 marked descent.
#guard (intOrder.laws ++ [intLeTransTested]).countP Law.isVerified == 5
#guard (intOrder.laws ++ [intLeTransTested]).countP (fun l => !l.isVerified) == 1

end Bang.Surface.Trait
