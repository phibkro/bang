import Bang.Meta.BinaryLR

/-! # SkipRelocateProbe — item-1 (BinaryLR:1030): krelS_splitAtId_decomp reformulated to
WELL-FOUNDED recursion on the index `n`, so the SKIP-arm resume conjunct can call the lemma
at `m < n` to STRIP the deep tail off `hSrel` (the config-append inverse). -/

namespace Bang
open Bang.EffectRow (Label)
variable {Eff  : Type} [Lattice Eff] [OrderBot Eff]
variable {Mult : Type} [CommSemiring Mult] [DecidableEq Mult]
variable [EffSig Eff Mult]

theorem krelS_splitAtId_decomp' {n : Nat} {C D : CTy Eff Mult} {e : Eff} {g : Nat}
    {K₁ K₂ : Stack} {nid : Nat} {K₁ᵢ K₁ₒ : Stack} {h : Handler}
    (hK : KrelS n C D e g K₁ K₂)
    (hsp : Bang.splitAtId K₁ nid = some (K₁ᵢ, h, K₁ₒ)) :
    ∃ (K₂ᵢ K₂ₒ : Stack) (h' : Handler) (Dᵢ : CTy Eff Mult) (C' : CTy Eff Mult) (e' : Eff),
      Bang.splitAtId K₂ nid = some (K₂ᵢ, h', K₂ₒ) ∧ HandlerRel Eff Mult n h h' ∧
      KrelS n C Dᵢ e g K₁ᵢ K₂ᵢ ∧ KrelS n C' D e' g K₁ₒ K₂ₒ
      ∧ (∀ m, m < n → ∀ (op' : OpId) (w₁ w₂ : Val) (Cᵢ' : CTy Eff Mult) (εᵢ' : Eff)
            (Kᵢ Kᵢ' : Stack) (cfg₁ cfg₂ : EvalCtx × Comp),
          Bang.handlesOp h h.label op' = true →
          Val.Closed w₁ → Val.Closed w₂ →
          (∀ Aop, EffSig.opArg (Eff := Eff) (Mult := Mult) h.label op' = some Aop → VrelK m Aop w₁ w₂) →
          KrelS m Cᵢ' Dᵢ εᵢ' g Kᵢ Kᵢ' →
          (∀ Aᵣ, EffSig.opRes (Eff := Eff) (Mult := Mult) h.label op' = some Aᵣ →
            ∃ qᵣ, Cᵢ' = CTy.F qᵣ Aᵣ) →
          Bang.dispatchOn nid op' w₁ (Kᵢ, h, K₁ₒ) = some cfg₁ →
          Bang.dispatchOn nid op' w₂ (Kᵢ', h', K₂ₒ) = some cfg₂ →
          (∃ (qᵣ : Mult) (Aᵣ : VTy Eff Mult) (r₁ r₂ : Val) (Sᵢ Sᵢ' : Stack) (eₛ : Eff),
              cfg₁ = (Sᵢ, Comp.ret r₁) ∧ cfg₂ = (Sᵢ', Comp.ret r₂) ∧
              Val.Closed r₁ ∧ Val.Closed r₂ ∧ VrelK m Aᵣ r₁ r₂ ∧
              KrelS m (CTy.F qᵣ Aᵣ) D eₛ g Sᵢ Sᵢ')) := by
  induction K₁ generalizing K₂ K₁ᵢ K₁ₒ C e with
  | nil => simp [Bang.splitAtId] at hsp
  | cons fr K₁' ih =>
      match K₂ with
      | [] => exact absurd hK (by simp only [KrelS]; cases fr <;> exact not_false)
      | fr₂ :: K₂' =>
          cases fr with
          | letF N₁ =>
              cases fr₂ with
              | letF N₂ =>
                  rw [krelS_letF] at hK
                  obtain ⟨q, A, B, φ, hC, hbody, htail⟩ := hK
                  simp only [splitAtId, Option.map_eq_some_iff] at hsp
                  obtain ⟨⟨Ki', hh, Ko'⟩, hsp', heq⟩ := hsp
                  simp only [Prod.mk.injEq] at heq
                  obtain ⟨rfl, rfl, rfl⟩ := heq
                  obtain ⟨K₂ᵢ, K₂ₒ, h', Dᵢ, C', e', hsp2, hHR, hin, htail2, hres2⟩ := ih htail hsp'
                  refine ⟨Frame.letF N₂ :: K₂ᵢ, K₂ₒ, h', Dᵢ, C', e',
                    by simp only [splitAtId]; rw [hsp2]; rfl, hHR, ?_, htail2, hres2⟩
                  rw [krelS_letF]; exact ⟨q, A, B, φ, hC, hbody, hin⟩
              | _ => simp only [KrelS] at hK
          | appF w₁ =>
              cases fr₂ with
              | appF w₂ =>
                  rw [krelS_appF] at hK
                  obtain ⟨q, A, B, hC, hcw₁, hcw₂, hw, htail⟩ := hK
                  simp only [splitAtId, Option.map_eq_some_iff] at hsp
                  obtain ⟨⟨Ki', hh, Ko'⟩, hsp', heq⟩ := hsp
                  simp only [Prod.mk.injEq] at heq
                  obtain ⟨rfl, rfl, rfl⟩ := heq
                  obtain ⟨K₂ᵢ, K₂ₒ, h', Dᵢ, C', e', hsp2, hHR, hin, htail2, hres2⟩ := ih htail hsp'
                  refine ⟨Frame.appF w₂ :: K₂ᵢ, K₂ₒ, h', Dᵢ, C', e',
                    by simp only [splitAtId]; rw [hsp2]; rfl, hHR, ?_, htail2, hres2⟩
                  rw [krelS_appF]; exact ⟨q, A, B, hC, hcw₁, hcw₂, hw, hin⟩
              | _ => simp only [KrelS] at hK
          | handleF mh₁ hh₁ =>
              cases fr₂ with
              | handleF mh₂ hh₂ =>
                  rw [krelS_handleF] at hK
                  obtain ⟨hmid, hHRtop, htail, hres⟩ := hK
                  subst hmid
                  simp only [splitAtId] at hsp
                  by_cases hmn : mh₁ = nid
                  · subst hmn
                    rw [if_pos rfl, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hsp
                    obtain ⟨rfl, rfl, rfl⟩ := hsp
                    refine ⟨[], K₂', hh₂, C, C, e,
                      by simp [splitAtId], hHRtop, ?_, htail, hres⟩
                    rw [krelS_nil]; exact ⟨rfl, fun q A hC v₁ v₂ _ _ _ _ => ⟨1, v₂, rfl⟩⟩
                  · rw [if_neg hmn, Option.map_eq_some_iff] at hsp
                    obtain ⟨⟨Ki', hh, Ko'⟩, hsp', heq⟩ := hsp
                    simp only [Prod.mk.injEq] at heq
                    obtain ⟨rfl, rfl, rfl⟩ := heq
                    obtain ⟨K₂ᵢ, K₂ₒ, h', Dᵢ, C', e', hsp2, hHR, hin, htail2, hres2⟩ := ih htail hsp'
                    refine ⟨Frame.handleF mh₁ hh₂ :: K₂ᵢ, K₂ₒ, h', Dᵢ, C', e',
                      by simp only [splitAtId]; rw [if_neg hmn, hsp2]; rfl, hHR, ?_, htail2, hres2⟩
                    refine krelS_handleF_intro (nh := mh₁) hHRtop hin ?_
                    -- THE STRIP. rebuild hh₁'s resume over Ki' from hres (over K₁' = Ki'++handleF nid hh::Ko').
                    intro m hm op w₁ w₂ Cⱼ εⱼ Kⱼ Kⱼ' cfgg₁ cfgg₂ hcatch hcw₁ hcw₂ hVrel hKj hCⱼ hgd₁ hgd₂
                    have hKdecomp : K₁' = Ki' ++ Frame.handleF nid hh :: Ko' := splitAtId_decomp K₁' nid hsp'
                    have hK2decomp : K₂' = K₂ᵢ ++ Frame.handleF nid h' :: K₂ₒ := splitAtId_decomp K₂' nid hsp2
                    -- lift the goal dispatch (over Ki') to over K₁' (= Ki'++deep), feed hres.
                    have hl₁ := dispatchOn_append_outer mh₁ op w₁ Kⱼ hh₁ Ki' (Frame.handleF nid hh :: Ko') hgd₁
                    have hl₂ := dispatchOn_append_outer mh₁ op w₂ Kⱼ' hh₂ K₂ᵢ (Frame.handleF nid h' :: K₂ₒ) hgd₂
                    rw [← hKdecomp] at hl₁; rw [← hK2decomp] at hl₂
                    obtain ⟨qᵣ, Aᵣ, r₁, r₂, Sᵢ, Sᵢ', eₛ, hcf₁, hcf₂, hcr₁, hcr₂, hr, hSrel⟩ :=
                      hres m hm op w₁ w₂ Cⱼ εⱼ Kⱼ Kⱼ' _ _ hcatch hcw₁ hcw₂ hVrel hKj hCⱼ hl₁ hl₂
                    -- Sᵢ = (goal cfgg₁.1) ++ deep. STRIP via the lemma at m (RECURSION).
                    -- STRIP POINT: hSrel : KrelS m (F qᵣ Aᵣ) D eₛ (cfgg₁.1 ++ deep) Sᵢ' —
                    -- decompose past the appended `handleF nid hh :: Ko'` to `KrelS m .. Dᵢ cfgg₁.1 ..`.
                    -- Blocked: `krelS_append_inv`'s handleF-in-prefix case (see KrelSUnappendProbe) walls.
                    sorry
              | _ => simp only [KrelS] at hK

end Bang
