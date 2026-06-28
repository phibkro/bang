/-
  Bang/LWRegress.lean — ADR-0054 behavioral regression suite (NonEscape's operational oracle).
  ─────────────────────────────────────────────────────────────────────────────────
  Carries the cap-assignment witnesses forward onto the IDENTITY-dispatch kernel (ADR-0054). The old
  positional `LWT`/`CapResolvesKind` are DELETED; the structural escape-rejection re-keys onto `NonEscape`
  (Operational.lean). The behavioural claims are COMPILED `#guard`s (a failing build = a false `#guard`;
  the project oracle — `lean-eval-reliable-only-compiled`); never `lake env lean`.

    1. case A (capMigrate) — a `{get}`-thunk captures its handler's cap and migrates INTO the enclosing
       state handler (legal); reads its own state → `done 5`/`done 9`.
    2. case B (escape) — a `{get}`-thunk RETURNED out of its handler and forced with NO same-depth
       handler is STUCK (fail-loud) and `¬ NonEscape` (the structural rejection).

  ADR-0054 BEHAVIORAL NOTE: the escape's RE-HANDLED form (progB, scratch/IdentityCollisionProbe.lean) is
  NO LONGER the stuck oracle — under depth-based identities it COLLIDES with a fresh same-depth handler
  and resolves (the WC keystone-2c gap, pending an operator design call). The robust escape oracle is the
  DIRECT-FORCE form `escapeB` here: stuck + `¬ NonEscape`, independent of that design call.

  Imports ONLY `Bang.Operational` + `Bang.Mult`.
-/
import Bang.Operational
import Bang.Mult

namespace Bang.LWRegress

open Bang
open Bang.EffectRow (Label EffRow)

/-! ### 1. case A — migration INTO an enclosing handler terminates reading its own state.

ADR-0054: the `{get}`-thunk performs on the handle-bound capability `vvar 0` (the `state` handler's cap).
Returned by the `letC` and forced under a fresh `throws` (which binder-shifts the bound thunk to `vvar 1`
/ `vvar 2`), the cap travels WITH the thunk and resolves to the SAME state handler still on the stack —
migration, not escape. -/

private def capMigrate1 : Comp :=
  .handle (.state 1 (.vint 5))
    (.letC (.ret (.vthunk (.perform (.vvar 0) "get" .vunit)))
      (.handle (.throws 2) (.force (.vvar 1))))
private def capMigrate1_done5 : Bool :=
  match Source.eval 200 capMigrate1 with | .done (.vint n) => n == 5 | _ => false
#guard capMigrate1_done5

private def capMigrate2 : Comp :=
  .handle (.state 1 (.vint 9))
    (.letC (.ret (.vthunk (.perform (.vvar 0) "get" .vunit)))
      (.handle (.throws 2) (.handle (.throws 3) (.force (.vvar 2)))))
private def capMigrate2_done9 : Bool :=
  match Source.eval 300 capMigrate2 with | .done (.vint n) => n == 9 | _ => false
#guard capMigrate2_done9

/-! ### 2. case B — the DIRECT-FORCE escape: STUCK + `¬ NonEscape` (the structural rejection). -/

/-- The escape: a `{get}`-thunk capturing the inner `state 1` handler's cap (`vvar 0`) is RETURNED out
and forced at top level (no re-handler). The cap names the popped handler's identity `0`; `splitAtId []
0 = none` → fail-loud STUCK. (= `scratch/NonEscapeProbe.escapeWitness` at `unit` state.) -/
def escapeB : Comp :=
  .letC (.handle (.state 1 .vunit) (.ret (.vthunk (.perform (.vvar 0) "get" .vunit))))
        (.force (.vvar 0))
-- ADR-0063: the escape now lands in the DEFINED `.escapedCap` terminal (was `.stuck` before the
-- reclassification) — the cap names the popped handler `0`, `idDispatch` finds no frame, fail-loud.
private def escapeB_escaped : Bool :=
  match Source.eval 300 escapeB with | .escapedCap => true | _ => false
#guard escapeB_escaped

/-- `¬ CapResolves [] 0 1 "get"` — the escaped cap names handler `0`, but the stack is empty
(`splitAtId [] 0 = none`). The Prop-level twin of the `#guard` above. -/
theorem escape_site_unresolved : ¬ CapResolves ([] : EvalCtx) 0 1 "get" := by
  rintro ⟨Kᵢ, h, Kₒ, hsp, _⟩
  simp [splitAtId] at hsp

/-- **ADR-0063: `escapeB` REACHES the unresolved escape — now a DEFINED capability-escape.** The escape
config `(1, [], perform (vcap 0 1) "get" unit)` is reachable (5 steps: PUSH · MINT(g 0→1) · POP · REDUCE ·
force), and its focus does NOT resolve (`escape_site_unresolved`: `splitAtId [] 0 = none`). 3-tuple Config
(ADR-0055; the old 2-tuple `([], …)` was stale — this restate clears that pre-red). -/
theorem escapeB_reaches_escape :
    StepStar (0, [], escapeB) (1, [], Comp.perform (Val.vcap 0 1) "get" .vunit) :=
  StepStar.head rfl (StepStar.head rfl (StepStar.head rfl (StepStar.head rfl
    (StepStar.head rfl StepStar.refl))))

/-- **The ADR-0063 reclassification turns the old `¬ NonEscape` into a `NonEscape'` witness.** `escapeB`
reaches an unresolved perform-vcap (`escapeB_reaches_escape` + `escape_site_unresolved`), but that is a
DEFINED capability-escape (`Source.eval escapeB = .escapedCap`, the `#guard` above) — `FocusResolves'`
holds there via its escape disjunct, so `escapeB` SATISFIES the defined-escape-tolerant `NonEscape'`. -/
theorem escapeB_nonEscape' : NonEscape' (0, [], escapeB) := nonEscape'_all _

end Bang.LWRegress
