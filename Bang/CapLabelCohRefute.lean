/-
  Bang/CapLabelCohRefute.lean — DO-NOT-WEAKEN REGRESSION WITNESS (inc-6 U3, route-B bridge).
  ─────────────────────────────────────────────────────────────────────────────────
  GATED: `refute_frame_present_but_no_capResolves` is listed in `Bang/Audit.lean`'s
  `#print axioms` block, so weakening `run_evalD`'s cap-label-coherence premise (e.g.
  dropping `CapResolves` / simplifying the perform-term arm) fails the axiom gate
  (`lake env lean Bang/Audit.lean`), not just this file. Axiom-clean: [propext].
  (Promoted from `scratch/CapLabelCohRefute.lean`, banked at e4f6b5a.)

Documents WHY `run_evalD` must carry a cap-label-coherence premise — the identity-vs-label
asymmetry that bites the perform-TERM arm where the raised arm's `labelOf` trick cannot save it.

`evalD`'s perform arm (CalcVM.lean `perform (.vcap n _ℓ)`) dispatches BY IDENTITY and IGNORES the
cap's label `_ℓ` — it reads `σ.get? n`. The kernel `idDispatch` (Operational) is FAIL-LOUD on the
label: `if handlesOp h ℓ op then dispatchOn … else none`, with `handlesOp (.state ℓ' _) ℓ op`
requiring `ℓ' = ℓ`. So a live state frame at identity `n` with label `ℓ' ≠ ℓ2` makes:
  evalD  →  resumes `ret s`     (label-oblivious)
  kernel →  idDispatch = none → `.escapedCap`   (fail-loud)
They DISAGREE. Hence the bridge term-success arm needs `CapResolves K n ℓ2 op`, which is NOT
derivable from the arm's locals (`CtxCorr`/`CtxTxnCorr` + a store hit). The witness below pins the
exact gap: a frame is PRESENT at identity 0, yet `CapResolves` at the cap's label 2 is FALSE.

Within the bridge's VcapFree scope this never fires (cap-label = frame-label by the gensym mint),
which is precisely what the route-A label-coherence forward-invariant must establish & thread.
Axiom-clean: [propext].
-/
import Bang.Operational
open Bang

theorem refute_frame_present_but_no_capResolves :
    ¬ CapResolves [Frame.handleF 0 (Handler.state 1 (Val.vint 0))] 0 2 "get" := by
  rintro ⟨Ki, h, Ko, hsp, hho⟩
  have hval : splitAtId [Frame.handleF 0 (Handler.state 1 (Val.vint 0))] 0
                = some ([], Handler.state 1 (Val.vint 0), []) := rfl
  rw [hval] at hsp
  simp only [Option.some.injEq, Prod.mk.injEq] at hsp
  obtain ⟨_, rfl, _⟩ := hsp
  revert hho
  decide
