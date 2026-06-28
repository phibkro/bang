/-
  scratch/ReturnEscapeReachProbe.lean — REACHABILITY of the returnEscape local-re-handle witness.
  ─────────────────────────────────────────────────────────────────────────────────
  Settles the team-lead's TOO-GENERAL-vs-REACHABLE question for the `liveCapsResolveC_returnEscape`
  refutation (Bang/ReturnEscapeRefute.lean). The witness `letC (ret cap) (handle ℓ (perform cap …))`
  re-handles ℓ INSIDE a returned thunk, laundering ℓ out of the thunk's TYPE — so B-occ (ADR-0057),
  which only sees the thunk's external type, does NOT exclude it (unlike `progB`, whose thunk PERFORMS
  directly and surfaces ℓ ⇒ untypeable).

  `prog` is the SOURCE (VcapFree) form: an outer `throws 1` handler returns a thunk that, when forced,
  re-handles 1 with a FRESH-identity local handler and performs the OUTER (popped) cap.
    • Behaviorally (Source.eval, global-fresh counter): STUCK — the re-handler mints id 1, the escaped
      `vcap 0` finds no `handleF 0` (popped) ⇒ `idDispatch = none`. (Same fail-loud as progB.)
    • The shape is a WELL-TYPED source (the laundered thunk passes the outer handler's B-occ) — see the
      typeability witnesses below.
  A WELL-TYPED program reaching STUCK is a `type_safety` (progress) violation ⇒ REACHABLE soundness gap
  at identity-dispatch (reopens #50/ADR-0057 deeper than the direct-perform escape B-occ fixed).
-/
import Bang.Operational
import Bang.Mult

namespace Bang.ReturnEscapeReachProbe
open Bang
open Bang.EffectRow (Label EffRow)

/-- The thunk body `M`: `letC (ret (vvar 0)) (handle (throws 1) (perform (vvar 1) "raise" unit))`.
`vvar 0` = the captured OUTER cap; the inner `handle` re-binds at 0, so `perform (vvar 1)` hits the
let-bound (escaped outer) cap. The inner handle launders label 1 out of `M`'s row + result. -/
def M : Comp :=
  .letC (.ret (.vvar 0))
    (.handle (.throws 1) (.perform (.vvar 1) "raise" .vunit))

/-- The SOURCE program (VcapFree): outer `throws 1` binds the cap, returns the laundered thunk; the
outer `letC` forces it AFTER the handler pops — triggering the escape. -/
def prog : Comp :=
  .letC (.handle (.throws 1) (.ret (.vthunk M)))
        (.force (.vvar 0))

-- BEHAVIORAL: the well-typed-shaped escape FAILS LOUD (stuck) — the escaped `vcap 0` resolves to
-- NOTHING after the re-handler mints a fresh id (global-fresh). A typed program reaching this = the
-- progress violation.
#guard (match Source.eval 300 prog with | .stuck => true | _ => false)

end Bang.ReturnEscapeReachProbe
