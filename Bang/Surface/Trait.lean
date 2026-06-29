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

module

-- Trait's #guards/#eval run the law checkers (`runPair`, `Law.isVerified`, `fullReport`),
-- which execute `Source.eval` (compiled Operational) at the META phase → meta import it
-- (transitive dep via Surface).
meta import Bang.Operational
public import Bang.Surface

namespace Bang.Surface.Trait

open Bang
open Bang.Surface

/-! ## 1. The discharge ladder as DATA (correctness by construction)

A `law` is a UNIVERSAL claim `∀ x, pred x` over a predicate `pred : α → Prop`.
Its evidence is a value of `Evidence pred` — and BOTH rungs carry a KERNEL-CHECKED
justification, so neither can be constructed for a predicate that fails:

  * `Evidence.proof  (h : ∀ x, pred x)` — the VERIFIED rung (proof-first DEFAULT):
    a proof of the whole claim.
  * `Evidence.tested reason sample (holds : ∀ x ∈ sample, pred x)` — the TESTED
    rung: a FINITE sample together with a kernel-checked proof the predicate holds
    on every element of it. There is NO "trust me" rung.

This is the binding the brief demands: the tested rung's `holds` is real evidence,
discharged at the call site (by `decide` on a decidable `pred`). A law FALSE on
its sample makes `holds` unprovable ⇒ the `Law` is UNREPRESENTABLE. The check is
not a detached `#test` command beside the law — it is a field of the law's value.
That is the "no silent pass" rule, made structural at BOTH rungs. -/

/-- The evidence a `law` carries, over its predicate `pred : α → Prop`. Proof-first:
`proof` is the verified rung (proves the universal claim outright); `tested` is the
marked tested rung — it carries a finite `sample` AND a proof the predicate holds on
every element of it, so the descent is checked, not asserted. No silent third rung. -/
inductive Evidence {α : Type} (pred : α → Prop) where
  | proof  (h : ∀ x, pred x)                            : Evidence pred  -- VERIFIED rung — the default
  | tested (reason : String) (sample : List α)
           (holds : ∀ x ∈ sample, pred x)               : Evidence pred  -- TESTED rung — carries its check

/-- A first-class `law`: its predicate together with its discharge evidence.
Bundling `pred` with `evidence` is the enforcement — you cannot have a `Law`
without discharging it (proof of the claim, or a checked sample) one way or the
other. The universal CLAIM the law makes is `Law.prop` (`∀ x, pred x`). -/
structure Law where
  name     : String
  {α       : Type}
  pred     : α → Prop
  evidence : Evidence pred

/-- The universal CLAIM a law makes, regardless of rung: `∀ x, pred x`. On the
verified rung this is fully proven; on the tested rung it is sampled (the `holds`
field proves only the finite sample). -/
def Law.prop (l : Law) : Prop := ∀ x, l.pred x

/-- Is this law on the VERIFIED rung (discharged by a proof of the whole claim)?
Used by the harness to REPORT the rung of each law (so a tested descent is visible,
not silent). -/
def Law.isVerified (l : Law) : Bool :=
  match l.evidence with
  | .proof _      => true
  | .tested ..    => false

/-- The descent reason + sample size, if this law is on the tested rung (else
`none`). Surfaces the marked descent for the harness's visibility report. -/
def Law.descentReason (l : Law) : Option String :=
  match l.evidence with
  | .proof _                  => none
  | .tested reason sample _   => some s!"test ({sample.length} samples): {reason}"

/-- Smart constructor: a law discharged PROOF-FIRST. `mkVerified "antisym" pred h`
records the proof `h : ∀ x, pred x` on the verified rung. This is the default path. -/
def mkVerified (name : String) {α : Type} (pred : α → Prop) (h : ∀ x, pred x) : Law :=
  { name := name, pred := pred, evidence := .proof h }

/-- Smart constructor: a law that EXPLICITLY DESCENDS to the tested rung. The
descent is MARKED (a `reason`) AND CHECKED: `holds` proves the predicate on every
element of `sample`, so a law false on its sample cannot be constructed (the
`holds` obligation is unprovable). At the call site `holds` is discharged by
`by decide` on a decidable `pred`. The check is a FIELD of the law, not a detached
command beside it — the binding the brief demands. -/
def mkTested (name : String) {α : Type} (pred : α → Prop)
    (reason : String) (sample : List α) (holds : ∀ x ∈ sample, pred x) : Law :=
  { name := name, pred := pred, evidence := .tested reason sample holds }


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
def intEqRefl : Law := mkVerified "eq.refl"
    (fun a : Int => intEq a a = true) (by
  intro a; simp [intEq])

/-- `sym: ∀ a b, eq a b → eq b a` — proven; `==` is symmetric on `Int`. The
predicate ranges over a PAIR `(a, b)` so the law is a single `∀ x, pred x` claim. -/
def intEqSym : Law := mkVerified "eq.sym"
    (fun p : Int × Int => intEq p.1 p.2 = true → intEq p.2 p.1 = true) (by
  rintro ⟨a, b⟩ h; simp_all [intEq])

/-- `le.refl: ∀ a, le a a` — `a ≤ a`, by `simp` on `intLe`. -/
def intLeRefl : Law := mkVerified "le.refl"
    (fun a : Int => intLe a a = true) (by
  intro a; simp [intLe])

/-- `le.trans: ∀ a b c, le a b → le b c → le a c` — transitivity of `≤`, over a
TRIPLE `(a, b, c)`. -/
def intLeTrans : Law := mkVerified "le.trans"
    (fun t : Int × Int × Int =>
      intLe t.1 t.2.1 = true → intLe t.2.1 t.2.2 = true → intLe t.1 t.2.2 = true) (by
  rintro ⟨a, b, c⟩ hab hbc; simp_all [intLe]; omega)

/-- `antisym: ∀ a b, le a b → le b a → eq a b` — THE order law, by `omega`, over a
PAIR `(a, b)`. -/
def intAntisym : Law := mkVerified "order.antisym"
    (fun p : Int × Int =>
      intLe p.1 p.2 = true → intLe p.2 p.1 = true → intEq p.1 p.2 = true) (by
  rintro ⟨a, b⟩ hab hba; simp_all [intLe, intEq]; omega)

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
    (fun p : Int × Int =>
      match runPair p.1 p.2 with
      | some (lo, hi) => lo ≤ hi
      | none          => False) (by
  rintro ⟨a, b⟩
  show (match runPair a b with | some (lo, hi) => lo ≤ hi | none => False)
  have hrun : runPair a b = some (min a b, max a b) := by
    unfold runPair mkPairComp; rfl
  rw [hrun]
  omega)

-- GREEN CHECK: the data-structure law is on the VERIFIED rung (proof-first).
#guard orderedPairLaw.isVerified
-- RUN the structure through eval and pin a concrete result: mkPair 5 2 = (2, 5).
#guard (match runPair 5 2 with | some (2, 5) => true | _ => false)
#guard (match runPair 2 5 with | some (2, 5) => true | _ => false)
-- The invariant holds on the run output for a sampled input (lo ≤ hi).
#guard (match runPair 9 1 with | some (lo, hi) => decide (lo ≤ hi) | _ => false)


/-! ## 7. ONE explicit DESCENT — proving the marked tested rung WORKS + is visible

To validate that the descent path is real (not just the proof path), we state one
law via `mkTested` — an EXPLICIT, MARKED descent to the tested rung. This is the
SAME predicate as `intLeTrans` (transitivity), deliberately re-discharged by a
FINITE SAMPLE to exercise the descent machinery. In real use you'd descend only
when a proof is genuinely out of reach; here it demonstrates the seam.

The tested rung's check is BOUND to the law BY CONSTRUCTION: `mkTested` demands a
`holds : ∀ x ∈ sample, pred x`, discharged here by `by decide` over the concrete
sample. A law false on this sample could not be constructed (see §7-TEETH). The
descent is VISIBLE in `dischargeReport` (it prints `↓ … DESCENT`). -/

/-- The transitivity predicate, DESCENDED to the tested rung (marked, with a reason)
and CHECKED on a real sample of triples. `isVerified` is `false`; `dischargeReport`
prints it as a descent — never silent — and the `holds` field (by `decide`) is the
binding that makes the tested verdict real, not asserted. -/
def intLeTransTested : Law :=
  mkTested "le.trans (descended)"
    (fun t : Int × Int × Int =>
      intLe t.1 t.2.1 = true → intLe t.2.1 t.2.2 = true → intLe t.1 t.2.2 = true)
    "demonstrates the explicit tested-rung descent seam"
    [(0, 1, 2), (-3, 0, 7), (5, 5, 9), (2, 2, 2)]
    (by decide)

-- The descent is VISIBLE: this law reports as tested, not verified.
#guard !intLeTransTested.isVerified
#guard (match intLeTransTested.descentReason with | some _ => true | none => false)

/-! ### §7-TEETH — the binding has teeth (real-journey gate)

The headline deliverable: demonstrate that a law FALSE on its sample genuinely
CANNOT reach the tested rung. `mkTested` requires `holds : ∀ x ∈ sample, pred x`;
if that obligation is REFUTABLE, `mkTested … (by decide)` cannot elaborate — the
tested rung is unreachable for a false-on-sample law. We prove the refutation
directly: the predicate `fun x => x < 0` is false on the sample `[3]`, so its
`holds` obligation is `¬ (∀ x ∈ [3], x < 0)` — provable, hence the obligation it
negates is UNPROVABLE, hence `mkTested` would reject it. -/

/-- TEETH: a law FALSE on its sample cannot reach the tested rung — its `holds`
obligation `∀ x ∈ [3], x < 0` is refutable, so `mkTested … (by decide)` for this
predicate+sample would NOT elaborate. The bad state is unrepresentable. -/
example : ¬ (∀ x ∈ [(3 : Int)], x < 0) := by decide

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
