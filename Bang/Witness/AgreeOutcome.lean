module

-- `#guard` runs at the META phase (same seam Fuzz.lean's header documents), so the
-- runtime `public import` needs a matching `meta import` for the constructors used
-- inside `#guard` terms to be visible there too.
meta import Bang.Backend.AbstractMachine
public import Bang.Backend.AbstractMachine

/-!
  Bang/Witness/AgreeOutcome.lean — differential-over-OUTCOMES (#54, ⭐ half).

  `Agree` (AbstractMachine.lean) and `FuzzAgree`/`fuzzAgree` (Fuzz.lean) both compare the
  two-hop oracle at the VALUE level: they only assert something when `Source.eval` reaches
  `.done v`, and treat `escapedCap ↔ none` as a single admitted disjunct (`fuzzAgree`'s
  `.escapedCap, none => true` arm). That makes a genuine divergence in the OTHER THREE
  outcomes structurally invisible: if `Source.eval` said `.oom` but `exec ∘ compile` said
  `none` for a reason that ISN'T fuel exhaustion (a real stuck/escape the machine masks as
  "just needs more fuel"), no existing `#guard` would ever catch it — both sides silently
  fall through their disjunction's "good enough" arm.

  This module makes the comparison TOTAL: every one of the kernel's four `Result` outcomes
  (`done`/`oom`/`escapedCap`/`stuck`) is compared against an EXPLICIT machine-side outcome,
  with no residual "either side, whatever" disjunct. The mapping `exec = none ↦ {oom, stuck,
  escapedCap}` is resolved the same way `Config.run` resolves it: `Result Val` (not a new
  machine-side ADT) is the single shared outcome type — `Bang.Core.Semantics.Eval` already
  names exactly these four cases (`done`/`oom`/`escapedCap`/`stuck`), so this module reuses
  it rather than inventing a parallel copy (single-source-of-truth). What's NEW is the
  OBSERVATION: classifying which of the three `none`-causing outcomes a given `(fuel, M)`
  falls into, purely by comparing `exec` at TWO fuel values (see `§1`) — never by reading a
  new tag out of `exec`'s recursion (that would be DESIGNING a machine arm, forbidden by
  invariant #4). This is diff-testing, not a proof: gated by compiled `#guard` only.

  Scope: OBSERVING the calculated machine, never patching it. Zero edits to
  AbstractMachine.lean/Fuzz.lean/Core/Frontend/TypeCheck (out of this lane's remit).
-/

namespace Bang.AgreeOutcome

open Bang
open Bang.CalcVM

@[expose] public section

/-! ## 1. The machine-side outcome classifier — by FUEL-DOUBLING, not new exec internals.

`exec`'s recursion returns a bare `none` from several distinct causes (fuel hits `0`; a
`SUBST`/`APP`/`CASE`/`SPLIT` stack-shape mismatch; an uncaught `THROW`/`OP` via
`unwindFind`) with no self-reported tag distinguishing them (`Bang.Backend.AbstractMachine`
confirms this: every existing `exec … = none` example in that file's ◊3 battery asserts
raw `none`, never a reason). Rather than adding a machine-side tag (a NEW exec arm — the
invariant-#4 trap this lane must not fall into), the classifier below OBSERVES: does more
fuel change the answer? `exec_mono` (AbstractMachine.lean) already proves fuel-monotonicity
for the `some` case, so "still `none` at generously-more fuel" is a legitimate structural
signal that the `none` at the ORIGINAL fuel was not fuel exhaustion.

FAILURE POLARITY of the `slack` bound: `slack` is finite, so this classifier is an
APPROXIMATION, not a proof — a program that genuinely needs more than `fuel + slack` extra
steps to reach `.done` would be MISCLASSIFIED as escape-or-stuck (`.inr false`) instead of
`.oom`. This is fail-LOUD, never fail-silent: `agreeOutcome` would then compare that
misclassification against the kernel's OWN `Source.eval fuel M` (also under-fueled, so also
NOT `.done`) — the mismatch is between "genuinely oom" and "looks stuck", both non-`done`,
so the worst case is a `#guard` FAILING on a case that should have passed with more slack
(a red build demanding a bigger `slack`), never a `#guard` PASSING on a real divergence. A
false negative here is loud and actionable; there is no false-positive path. -/

/-- Fuel headroom for the "is it just under-fueled?" re-check — an order of magnitude past
any `#guard` case's own `fuel` below, well past what any curated/generated program in this
module's battery needs to settle (kernel-side confirmed by the paired `Source.eval` calls).
See the FAILURE POLARITY note above: too small a `slack` fails loud, never silently. -/
def slack : Nat := 2000

/-- The machine-side outcome, computed OBSERVATIONALLY (no new `exec` tag):
    - `some [.ret v]` at the given fuel            ⇒ `.done v`  (the value was reached)
    - `none` at the given fuel, `some _` at `+slack` ⇒ `.oom`     (fuel-exhaustion — needed more)
    - `none` at both                                ⇒ escape-or-stuck, NOT resolved here —
      the machine alone cannot tell these apart (both are `none`); see `§2`. -/
def machineOutcome (fuel : Nat) (M : Comp) : Option Val ⊕ Bool :=
  match exec fuel 0 (compile M []) [] [] with
  | some [.ret v] => .inl (some v)
  | _ =>
    match exec (fuel + slack) 0 (compile M []) [] [] with
    | some [.ret _] => .inr true   -- settles with more fuel ⇒ was oom at `fuel`
    | _             => .inr false  -- still stuck even generously re-fueled ⇒ escape-or-stuck

/-! ## 2. The shared outcome type — `Result Val` (`Bang.Core.Semantics.Eval`), reused, not
re-declared. Escape vs genuine-stuck is a distinction the MACHINE'S OWN STATE cannot make
(both are `none`); this module resolves it by trusting the KERNEL's classification
(`Source.eval`'s own `.escapedCap`/`.stuck` split, `Config.run`'s `IsDefinedEscape` check,
ADR-0063) as the referee for that one bit, and holds the MACHINE side to agreeing with
"some non-value outcome happened", exactly mirroring the shape of the existing ◊3 battery's
lone escape example (`exec … = none` + `Source.eval … = .escapedCap`, AbstractMachine.lean)
— just made TOTAL across all three non-`done` cases instead of asserted once by hand. -/

/-- The TOTAL differential predicate. Every one of the kernel's four `Result` outcomes has
an explicit, DISTINCT machine-side signature — no admitted "either of these" disjunct:
  - `.done v`     ⇔ machine reaches `some [.ret v]` at `fuel`, SAME value (`valEq`, ported).
  - `.oom`        ⇔ machine is `none` at `fuel` but `some _` at `fuel + slack` (needed fuel).
  - `.escapedCap` ⇔ machine is `none` at BOTH fuels (kernel says: a capability escaped).
  - `.stuck`      ⇔ machine is `none` at BOTH fuels (kernel says: genuinely stuck).
`escapedCap` and `stuck` share a machine signature (`none`/`none`) BY CONSTRUCTION — the
machine's `Option Stack` has no third value to split them, so the total agreement this
predicate checks is: "the machine says none/some exactly when the kernel's OWN four-way
classification says a non-done/some outcome should occur", with the kernel's `Result` doing
the fine-grained escape-vs-stuck naming. This is what makes the comparison worth more than
`fuzzAgree`'s disjunction: `.oom`-vs-`.stuck` (fuel-exhaustion vs genuine-stuck) — the pair
`fuzzAgree` could NOT tell apart (both value-invisible) — is now a DISTINCT, checked case. -/
def valEq : Val → Val → Bool
  | .vunit,       .vunit       => true
  | .vint a,      .vint b      => a == b
  | .vvar i,      .vvar j      => i == j
  | .vcap n l,    .vcap m k    => n == m && l == k
  | .inl a,       .inl b       => valEq a b
  | .inr a,       .inr b       => valEq a b
  | .pair a b,    .pair c d    => valEq a c && valEq b d
  | .fold a,      .fold b      => valEq a b
  | _,            _            => false

/-- The TOTAL outcome-differential oracle. `true` = the two hops agree at the OUTCOME level
(all four `Result` cases distinguished — no admitted disjunct). -/
def agreeOutcome (fuel : Nat) (M : Comp) : Bool :=
  match Source.eval fuel M, machineOutcome fuel M with
  | .done v,     .inl (some v') => valEq v v'
  | .done _,     _              => false          -- kernel done, machine disagrees ⇒ DIVERGENCE
  | .oom,        .inr true      => true           -- both: needed more fuel
  | .oom,        _              => false          -- kernel oom, machine already settled/genuinely-stuck ⇒ DIVERGENCE
  | .escapedCap, .inr false     => true           -- both: a defined escape (machine: genuinely none, not just under-fueled)
  | .escapedCap, _              => false          -- DIVERGENCE
  | .stuck,      .inr false     => true           -- both: genuinely stuck (machine: none, not just under-fueled)
  | .stuck,      _              => false          -- DIVERGENCE

/-! ## 3. The ◊3 battery, PORTED to outcome-level — every case from AbstractMachine.lean's
curated `Agree` battery, re-asserted here as `agreeOutcome` (a pure strengthening: each was
already a `.done` case, `agreeOutcome` requires exactly what `Agree` required PLUS nothing
new for these — the port is a regression check that outcome-comparison doesn't reject what
value-comparison accepted). -/

-- PURE axis
#guard agreeOutcome 12 (.app (.lam (.ret (.vvar 0))) (.vint 5))
#guard agreeOutcome 16 (.letC (.app (.lam (.ret (.vvar 0))) (.vint 5)) (.ret (.vvar 0)))
#guard agreeOutcome 12 (.force (.vthunk (.ret (.vint 9))))

-- THROWS axis (caught)
#guard agreeOutcome 20 (.handle (.throws 0) (.perform (.vvar 0) "raise" (.vint 7)))
#guard agreeOutcome 24 (.handle (.throws 0) (.letC (.perform (.vvar 0) "raise" (.vint 7)) (.ret (.vint 99))))

-- THROWS axis (UNCAUGHT) — the ◊3 battery's lone hand-asserted escape example, now via the
-- TOTAL oracle instead of two separate `by rfl`s.
#guard agreeOutcome 20 (Comp.perform (.vcap 0 0) "raise" (.vint 7))

-- STATE axis
#guard agreeOutcome 40 (.handle (.state 1 (.vint 5)) (.perform (.vvar 0) "get" .vunit))
#guard agreeOutcome 80
  (.handle (.state 1 (.vint 0)) (.letC (.perform (.vvar 0) "put" (.vint 7)) (.perform (.vvar 1) "get" .vunit)))
#guard agreeOutcome 100
  (.handle (.state 1 (.vint 0))
    (.letC (.perform (.vvar 0) "put" (.vint 7))
      (.letC (.handle (.throws 0) (.perform (.vvar 0) "raise" .vunit))
        (.perform (.vvar 2) "get" .vunit))))

-- TRANSACTION axis
#guard agreeOutcome 40
  (.handle (.transaction 2 []) (.letC (.perform (.vvar 0) "newTVar" (.vint 9)) (.perform (.vvar 1) "readTVar" (.vvar 0))))
#guard agreeOutcome 80
  (.handle (.throws 0)
    (.handle (.transaction 2 [])
      (.letC (.perform (.vvar 0) "newTVar" (.vint 100))
        (.letC (.perform (.vvar 1) "writeTVar" (.pair (.vint 0) (.vint 70)))
          (.perform (.vvar 3) "raise" (.vint 100))))))

-- ADT axis
#guard agreeOutcome 12 (.case (.inl (.vint 5)) (.ret (.vvar 0)) (.ret (.vint 99)))
#guard agreeOutcome 12 (.case (.inr (.vint 7)) (.ret (.vint 99)) (.ret (.vvar 0)))
#guard agreeOutcome 14 (.split (.pair (.vint 3) (.vint 4)) (.ret (.vvar 1)))
#guard agreeOutcome 12 (.unfold (.fold (.vint 8)))

/-! ## 4. NEW cases — only visible at the OUTCOME level (a value-only oracle admits these
by construction, so no prior battery exercises them). -/

-- ─── FUEL-EXHAUSTION (`.oom` both sides) ─────────────────────────────────────
-- A trivial value at fuel `0`: `Config.run 0 _ = .oom` unconditionally (no step taken);
-- `exec 0 _ _ _ _ = none` unconditionally too — the CHEAPEST possible oom witness, and the
-- one case every prior value-only battery had NO reason to ever construct (an oom outcome
-- carries no value, so `Agree`'s `∃ v` shape can't even STATE it).
#guard agreeOutcome 0 (.ret (.vint 5))
#guard agreeOutcome 0 (.app (.lam (.ret (.vvar 0))) (.vint 5))

-- A slightly-larger program under-fueled by exactly one step short of `.done`: `exec`/
-- `Source.eval` both still need one more `step`/instruction than they're given.
#guard agreeOutcome 1 (.app (.lam (.ret (.vvar 0))) (.vint 5))
#guard agreeOutcome 2 (.letC (.app (.lam (.ret (.vvar 0))) (.vint 5)) (.ret (.vvar 0)))

-- ─── ESCAPE cases (thunk-captured cap forced past its handler) ───────────────
-- A capability minted by `handle`, THUNKED inside the handler's own body (so the thunk
-- closes over the fresh `vcap`), then the handler returns and the thunk is FORCED
-- afterward — the cap's handler has already popped. `force (vthunk (perform (vcap …) …))`
-- inside a `letC` whose SECOND leg forces the captured thunk once the `handle` has exited:
-- `handle (state 0 5) (let bound = (thunk (perform #0 "get" unit)) in ret bound)`, followed by
-- an OUTER `force` on the returned thunk — the outer force happens with NO handler in scope.
#guard agreeOutcome 30
  (.letC
    (.handle (.state 1 (.vint 5)) (.ret (.vthunk (.perform (.vvar 0) "get" .vunit))))
    (.force (.vvar 0)))

-- Same shape, THROWS handler (the ADR-0063 canonical escape kind): mint via `throws`,
-- thunk a `raise` naming the cap, return the thunk out of the (already-exited) handler,
-- then force it in the outer scope — `idDispatch` finds no frame (popped), `Config.run`
-- routes it to `.escapedCap` (NOT `.stuck`) per ADR-0063's defined-escape terminal.
#guard agreeOutcome 30
  (.letC
    (.handle (.throws 1) (.ret (.vthunk (.perform (.vvar 0) "raise" (.vint 42)))))
    (.force (.vvar 0)))

-- ─── GENUINELY-STUCK cases (constructible from closed, non-perform terms) ────
-- `Comp.oom`/`Comp.wrong` are dedicated catch-all leaves in `Source.step`'s final `| _ =>
-- none` arm (Bang/Core/Semantics/Eval.lean) — neither reduces under ANY context, so a
-- closed program built from one is stuck immediately (fuel ≥ 1), independent of handlers/
-- capabilities. This is the "genuinely stuck, not just an unhandled effect" case the
-- ADR-0063 split names but the existing batteries never construct (every prior stuck-shaped
-- example in this repo is actually an escape). `.oom`/`.wrong` are the DIRECT witness: no
-- `perform (vcap …)` focus is involved, so `IsDefinedEscape` is trivially false ⇒ `Config.run`
-- takes the `.stuck` arm, not `.escapedCap`.
#guard agreeOutcome 5 Comp.oom
#guard agreeOutcome 5 (Comp.wrong "deliberately stuck")

-- A bare unapplied `lam` at empty stack/context: `Source.step`'s only rule touching a
-- top-level `.lam` focus is the `appF`-REDUCE rule, which requires an ENCLOSING `appF`
-- frame — with none, `Source.step (_, [], .lam M) = none` (falls to the catch-all), and
-- `Config.run`'s classifier (focus is not `perform (vcap …)`) routes it `.stuck`, matching
-- `Bang.Fuzz`'s own header comment on why a bare top-level `lam` is excluded from that
-- generator (genuinely stuck on both sides, independently confirmed here).
#guard agreeOutcome 5 (.lam (.ret (.vint 1)))

end -- @[expose] public section

end Bang.AgreeOutcome
