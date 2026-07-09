import Bang.Core.Soundness

/-! # PROBE (ADR-0092 D4): preservation-of-dispatch for the CUSTOM resume — mono clause typing

The ADR names the bet: does the one-shot custom clause's resume step type-check under the
MONOMORPHIC system, or does it need answer-type polymorphism the mono elaborator can't express?

The resume dynamics (`Dispatch.dispatchOn`, custom arm): the focus becomes
`Comp.subst p (Comp.subst (Val.shift v) clause.2)` = `clause.2[param@1 := p, arg@0 := v]`,
over the reinstalled stack `Kᵢ ++ handleF n (custom ℓ p clauses) :: Kₒ`.

For that reinstalled stack to plug, the captured continuation `Kᵢ` (which expected the ORIGINAL
`perform c op v : F q (opRes ℓ op)` focus) must receive a focus of the SAME returner type
`F q (opRes ℓ op)`. So the D3 clause-body typing obligation is:

    body : F q (opRes ℓ op)   under   [opArg ℓ op (idx0), P (idx1)]  at effect φ'

and the resume step is: substitute the two CLOSED values (`p : P`, `v : opArg ℓ op`) and land at
`F q (opRes ℓ op)` over the EMPTY context (closed focus) — exactly what `Kᵢ` plugs.

This probe proves that reduction step STANDALONE, taking the D3 clause typing as a HYPOTHESIS `H`
(so it is independent of any in-file `sorry` and of the not-yet-added `customF` frame). If it closes
axiom-clean, the mono system suffices and the transplant is a GO; the double-`subst_value_proof`
pattern is exactly `split`'s (Soundness.lean:2378). -/

namespace Bang.CustomResumeProbe

open Bang

variable {Eff  : Type} [Lattice Eff] [OrderBot Eff]
variable {Mult : Type} [CommSemiring Mult] [DecidableEq Mult]
variable [EffSig Eff Mult]

/-- **The custom resume focus re-types (mono).** Given the D3-shaped clause typing `H` (body under
`[opArg, P]` at `F q opRes`, effect `φ'`) and the two CLOSED substituends (`p : P`, `v : opArg`),
the resumed focus `clause.2[param@1 := p, arg@0 := v]` types at `F q opRes` over the EMPTY context —
the returner type + closed context the captured continuation `Kᵢ` expects. NO answer-type
polymorphism: `q`, `opRes`, `φ'` are the clause's own fixed data, threaded verbatim. -/
theorem custom_resume_focus_types
    {Γ : TyCtx Eff Mult} {P opArg opRes : VTy Eff Mult} {φ' : Eff} {q qp qa : Mult}
    {p v : Val} {body : Comp}
    (hP : HasVTy (Eff := Eff) (Mult := Mult) [] [] p P)
    (hv : HasVTy (Eff := Eff) (Mult := Mult) [] [] v opArg)
    -- D3 clause typing: body under [opArg@0, P@1], returner F q opRes, effect φ'. (Γ empty for the
    -- closed focus; the general Γ carries no free vars once both binders are substituted closed.)
    (H : HasCTy (Eff := Eff) (Mult := Mult) (qa :: qp :: []) (opArg :: P :: []) body φ' (CTy.F q opRes)) :
    HasCTy (Eff := Eff) (Mult := Mult) [] [] (Comp.subst p (Comp.subst (Val.shift v) body)) φ' (CTy.F q opRes) := by
  -- inner subst: substitute the ARG (idx 0, type opArg) first — but the OUTER binder to eliminate is
  -- idx0=arg. Mirror `split` (Soundness.lean:2378): weaken the deeper closed value under the near binder.
  -- Here we substitute arg@0 first (v closed), then param@1 (p closed).
  -- Step 1: shift v under the P binder so it types over [P] (graded [0]).
  have hvw : HasVTy (Eff := Eff) (Mult := Mult) [0] (P :: []) (Val.shift v) opArg := by
    have := hv.weaken 0 (Nat.zero_le _) P
    simpa [Val.shift, insT, insG, GradeVec.zeros] using this
  -- Step 2: subst arg@0 := shift v into body ⇒ over [P], focus `subst (shift v) body`.
  have hinner := subst_value_proof qa hvw H
  simp only [hsmul_eq_smul, GradeVec.smul_cons, GradeVec.smul_nil, hadd_eq_add,
    GradeVec.add_cons, GradeVec.add_nil_left, mul_zero, add_zero] at hinner
  -- Step 3: subst param@0 := p (p closed, graded []) ⇒ over [], focus `subst p (subst (shift v) body)`.
  have houter := subst_value_proof qp hP hinner
  simp only [hsmul_eq_smul, GradeVec.smul_nil, hadd_eq_add,
    GradeVec.add_nil_left, GradeVec.add_nil_right] at houter
  exact houter

#print axioms custom_resume_focus_types

end Bang.CustomResumeProbe
