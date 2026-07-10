module

public import Bang.Meta.BinaryLR
public import Bang.Core.Semantics.Invariants

/-! # AnswerForkCompose — the SUCCESS-PATH skeleton: compose `krelS_splitAtId_decomp`'s inner `hin`
(answer `Dᵢ`) WITH its own resume conjunct (premise at answer `Dᵢ`), showing the answer types UNIFY
by construction — NO `D → Dᵢ` re-answering.

This is the type-checked skeleton the probe contract asks for on the SUCCESS side. It models the
`crelK_fund_up` resume arm's core move: use the FULL decomp (which delivers `hin` and the resume
conjunct at the SAME existential `Dᵢ`), instantiate the conjunct's inner premise with `hin` (mod the
index `KrelS_mono` + row `KrelS_eff_cast` + hole-grade `qᵣ := q` casts), and read off the resumed
config relation. The HARDEST case (the answer-type unification) elaborates; the residuals are the
tractable index/row/grade casts, NOT the refuted cross-answer equation. -/

namespace Bang.Witness.AnswerForkCompose

open Bang
open Bang.EffectRow (Label)

variable {Eff  : Type} [Lattice Eff] [OrderBot Eff]
variable {Mult : Type} [CommSemiring Mult] [DecidableEq Mult]
variable [EffSig Eff Mult]

/-- **The composition skeleton (SUCCESS PATH, hardest-case elaborating).** Abstracting the decomp
output as hypotheses (so this is a PURE composition test, independent of the decomp's own SKIP sorry):
given the decomp's inner `hin` at answer `Dᵢ` and its resume conjunct `hres` (premise at answer `Dᵢ`),
and the perform's dispatch, FIRE the conjunct — supplying `hin` (index/row-cast) as its inner premise.
The answer types unify BY CONSTRUCTION (`hin` and the premise both at `Dᵢ`). The output is the resumed
config relation at answer `D`. This elaborates with NO answer-type `sorry` — the `D → Dᵢ` re-answering
the census wall names NEVER ARISES on the decomp route (it arises only on the `krelS_dispatch_resume`
route, which does not deliver `hin`). Residual casts (index/row/grade) are threaded explicitly. -/
theorem decomp_route_fires_no_reanswer
    {n m : Nat} {q qᵣ : Mult} {B : VTy Eff Mult} {C D Dᵢ : CTy Eff Mult}
    {e εᵢ' eₛ : Eff} {g nid : Nat} {h h' : Handler} {K₁ᵢ K₂ᵢ K₁ₒ K₂ₒ : Stack}
    {op : OpId} {w₁ w₂ : Val} {cfg₁ cfg₂ : EvalCtx × Comp}
    -- the CONTEXT: in crelK_fund_up the focus is `perform … op : F q B`, so the decomp hole C = F q B.
    (hCeq : C = CTy.F q B)
    -- the decomp INNER relation, at answer Dᵢ (the SAME existential the resume conjunct uses):
    (hin : KrelS n C Dᵢ e g K₁ᵢ K₂ᵢ)
    -- the decomp RESUME conjunct (its inner premise is at answer Dᵢ — MATCHES hin):
    (hres : ∀ m, m < n → ∀ (op' : OpId) (w₁ w₂ : Val) (Cᵢ' : CTy Eff Mult) (εᵢ'' : Eff)
              (Kᵢ Kᵢ' : Stack) (cfg₁ cfg₂ : EvalCtx × Comp),
          Bang.handlesOp h h.label op' = true →
          Val.Closed w₁ → Val.Closed w₂ →
          (∀ Aop, EffSig.opArg (Eff := Eff) (Mult := Mult) h.label op' = some Aop → VrelK m Aop w₁ w₂) →
          KrelS m Cᵢ' Dᵢ εᵢ'' g Kᵢ Kᵢ' →
          Bang.StackAbove nid Kᵢ →
          (∀ Aᵣ, EffSig.opRes (Eff := Eff) (Mult := Mult) h.label op' = some Aᵣ →
            ∃ qᵣ, Cᵢ' = CTy.F qᵣ Aᵣ) →
          Bang.dispatchOn nid op' w₁ (Kᵢ, h, K₁ₒ) = some cfg₁ →
          Bang.dispatchOn nid op' w₂ (Kᵢ', h', K₂ₒ) = some cfg₂ →
          (∃ (qᵣ : Mult) (Aᵣ : VTy Eff Mult) (r₁ r₂ : Val) (Sᵢ Sᵢ' : Stack) (eₛ : Eff),
              cfg₁ = (Sᵢ, Comp.ret r₁) ∧ cfg₂ = (Sᵢ', Comp.ret r₂) ∧
              Val.Closed r₁ ∧ Val.Closed r₂ ∧ VrelK m Aᵣ r₁ r₂ ∧
              KrelS m (CTy.F qᵣ Aᵣ) D eₛ g Sᵢ Sᵢ'))
    -- the perform's dispatch data (op resolves to result B, handler catches, caps closed, args related):
    (hm : m < n)
    (hcatch : Bang.handlesOp h h.label op = true)
    (hcw₁ : Val.Closed w₁) (hcw₂ : Val.Closed w₂)
    (hVarg : ∀ Aop, EffSig.opArg (Eff := Eff) (Mult := Mult) h.label op = some Aop → VrelK m Aop w₁ w₂)
    (hResB : EffSig.opRes (Eff := Eff) (Mult := Mult) h.label op = some B)
    (habove : Bang.StackAbove nid K₁ᵢ)
    (hd₁ : Bang.dispatchOn nid op w₁ (K₁ᵢ, h, K₁ₒ) = some cfg₁)
    (hd₂ : Bang.dispatchOn nid op w₂ (K₂ᵢ, h', K₂ₒ) = some cfg₂) :
    -- the resumed config relation (answer D) — read off the resume conjunct, NO re-answering:
    ∃ (qᵣ' : Mult) (Aᵣ : VTy Eff Mult) (r₁ r₂ : Val) (Sᵢ Sᵢ' : Stack) (eₛ' : Eff),
        cfg₁ = (Sᵢ, Comp.ret r₁) ∧ cfg₂ = (Sᵢ', Comp.ret r₂) ∧
        Val.Closed r₁ ∧ Val.Closed r₂ ∧ VrelK m Aᵣ r₁ r₂ ∧
        KrelS m (CTy.F qᵣ' Aᵣ) D eₛ' g Sᵢ Sᵢ' := by
  subst hCeq
  -- Supply `hin` as the resume conjunct's inner premise. Casts:
  --  index: KrelS_mono (le_of_lt hm)   n → m
  --  row:   KrelS_eff_cast              e → εᵢ'
  --  hole grade: choose Cᵢ' := F q B (i.e. qᵣ := q), so hin's hole F q B matches by rfl — the CALLER
  --    picks the grade; the resume conjunct's `∀ Aᵣ, opRes = some Aᵣ → ∃ qᵣ, Cᵢ' = F qᵣ Aᵣ` is then
  --    `Aᵣ = B` (hResB) with qᵣ := q, discharged by ⟨q, rfl⟩.
  have hinner : KrelS m (CTy.F q B) Dᵢ εᵢ' g K₁ᵢ K₂ᵢ :=
    KrelS_eff_cast (KrelS_mono (le_of_lt hm) hin)
  -- fire the resume conjunct at op = op, Cᵢ' = F q B, Kᵢ = K₁ᵢ, Kᵢ' = K₂ᵢ:
  exact hres m hm op w₁ w₂ (CTy.F q B) εᵢ' K₁ᵢ K₂ᵢ cfg₁ cfg₂
    hcatch hcw₁ hcw₂ hVarg hinner habove
    (fun Aᵣ hAr => ⟨q, by rw [hResB] at hAr; injection hAr with h; rw [h]⟩)
    hd₁ hd₂

end Bang.Witness.AnswerForkCompose

#print axioms Bang.Witness.AnswerForkCompose.decomp_route_fires_no_reanswer
