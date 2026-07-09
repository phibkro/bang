import Bang.Core.Soundness

/-! # PROBE (ADR-0092 D4 option B): ret-shape clause closes the resume at the PERFORM's FREE grade.

The wall: the reinstated stack plugs the resume focus at the perform's FREE returner grade `q_perf`
(`C = F q_perf opR`), but a general clause body has a FIXED grade. Option (B): v1 clause bodies are the
RETURN shape `ret w`. Then the resume focus is `ret (w[p,v])` with a CLOSED payload, and `HasCTy.ret`
re-derives `F q_perf opR` for ANY `q_perf` — the SAME grade-freedom the state/throws arms already use.

This probe closes that step end-to-end (no `sorry`), taking the ret-shape clause typing as a hypothesis
`H : HasCTy … (Comp.ret w) e_op (F q opR)`. Proving it axiom-clean confirms (B) is the closeable v1. -/

namespace Bang.CustomRetGradeProbe

open Bang

variable {Eff  : Type} [Lattice Eff] [OrderBot Eff]
variable {Mult : Type} [CommSemiring Mult] [DecidableEq Mult]
variable [EffSig Eff Mult]

theorem custom_ret_resume_any_grade
    {P opA opR : VTy Eff Mult} {e_op : Eff} {q q_perf qa qp : Mult} {p v w : Val}
    (hp : HasVTy (Eff := Eff) (Mult := Mult) [] [] p P)
    (hv : HasVTy (Eff := Eff) (Mult := Mult) [] [] v opA)
    -- (B)-shaped clause: the body is `ret w`, typed under [opArg, P] at F q opR.
    (H : HasCTy (qa :: qp :: []) (opA :: P :: []) (Comp.ret w) e_op (CTy.F q opR)) :
    -- the resume focus re-types at the PERFORM's ARBITRARY grade q_perf.
    HasCTy (Eff := Eff) (Mult := Mult) [] []
      (Comp.subst p (Comp.subst (Val.shift v) (Comp.ret w))) ⊥ (CTy.F q_perf opR) := by
  -- 1. double subst_value_proof gives the closed `ret (w[p,v]) : F q opR` (the probe's existing lemma).
  have hvw : HasVTy (Eff := Eff) (Mult := Mult) [0] (P :: []) (Val.shift v) opA := by
    have := hv.weaken 0 (Nat.zero_le _) P
    simpa [Val.shift, insT, insG, GradeVec.zeros] using this
  have hinner := subst_value_proof qa hvw H
  simp only [hsmul_eq_smul, GradeVec.smul_cons, GradeVec.smul_nil, hadd_eq_add,
    GradeVec.add_cons, GradeVec.add_nil_left, mul_zero, add_zero] at hinner
  have houter := subst_value_proof qp hp hinner
  simp only [hsmul_eq_smul, GradeVec.smul_nil, hadd_eq_add,
    GradeVec.add_nil_left, GradeVec.add_nil_right] at houter
  -- houter : HasCTy [] [] (subst p (subst (shift v) (ret w))) e_op (F q opR).
  -- subst commutes into `ret`, so the focus IS `ret (closed payload)`.
  -- 2. invert the ret to get the CLOSED payload value, then re-`ret` at q_perf (grade-free).
  obtain ⟨γ', A0, q0, heff, hCeq, hγ0, hval⟩ := houter.ret_inv
  obtain ⟨hq0, hA0⟩ := CTy.F.injEq .. ▸ hCeq
  subst hA0
  -- the payload is closed (grade []), so `ret payload : F q_perf opR` for ANY q_perf.
  have hγ'nil : γ' = [] := by have := hval.length_eq; simpa using this
  subst hγ'nil
  exact HasCTy.ret hval (by simp [hsmul_eq_smul, GradeVec.smul, GradeVec.zeros])

#print axioms custom_ret_resume_any_grade

end Bang.CustomRetGradeProbe
