import Bang.Meta.BinaryLR

/-! # KrelSUnappendProbe — item-1 (BinaryLR:1030) WALL CHARACTERIZATION (task #29).

The SKIP-arm resume relocation reduces to a POSITION-based un-append of `KrelS` past a
shared handleF boundary. The letF/appF prefix cases are CLEAN; the **handleF-in-prefix**
case REPRODUCES the resume-relocation entanglement (its reconstructed wrapper needs hh₁'s
resume over the shorter tail — the very thing being relocated). So the un-append is NOT a
strictly-simpler standalone lemma: it is self-entangled at every nested handler.

Banked GREEN infra: `KrelS_length_eq` (below, exit-0) — KrelS relates only equal-length
stacks; the length pin that ALIGNS the two append boundaries (necessary: the naive
position-inverse WITHOUT the pin is machine-refutable — a shorter prefix's appended handler
can align against a DIFFERENT nid-frame inside the longer stack). -/

namespace Bang
open Bang.EffectRow (Label)
variable {Eff  : Type} [Lattice Eff] [OrderBot Eff]
variable {Mult : Type} [CommSemiring Mult] [DecidableEq Mult]
variable [EffSig Eff Mult]

/-- BANKED GREEN: KrelS relates only equal-length stacks (equal frame-by-frame structure). -/
theorem KrelS_length_eq {n : Nat} {C D : CTy Eff Mult} {ε : Eff} {g : Nat} :
    ∀ {K₁ K₂ : Stack}, KrelS n C D ε g K₁ K₂ → K₁.length = K₂.length := by
  intro K₁
  induction K₁ generalizing C D ε with
  | nil => intro K₂ hK; cases K₂ with
    | nil => rfl
    | cons fr₂ K₂' => exact absurd hK (by simp only [KrelS]; cases fr₂ <;> exact not_false)
  | cons fr K₁' ih =>
      intro K₂ hK; cases K₂ with
      | nil => exact absurd hK (by simp only [KrelS]; cases fr <;> exact not_false)
      | cons fr₂ K₂' =>
          simp only [List.length_cons]
          have htail : K₁'.length = K₂'.length := by
            cases fr <;> cases fr₂ <;>
              first
                | (exact absurd hK (by simp only [KrelS]; exact not_false))
                | (rw [krelS_letF] at hK; obtain ⟨_,_,_,_,_,_,ht⟩ := hK; exact ih ht)
                | (rw [krelS_appF] at hK; obtain ⟨_,_,_,_,_,_,_,ht⟩ := hK; exact ih ht)
                | (rw [krelS_handleF] at hK; obtain ⟨_,_,ht,_⟩ := hK; exact ih ht)
          omega

/-- The position-based un-append. letF/appF close cleanly (no resume). The handleF-in-prefix
case (the `sorry`) reproduces the SKIP-arm resume relocation: reconstructing the wrapper's
resume conjunct over the SHORTER tail is the same relocation, recursively. THIS is the wall. -/
theorem krelS_append_inv {m : Nat} {nid : Nat} {X D : CTy Eff Mult} {eₛ : Eff} {g : Nat}
    {hh h' : Handler} {Ko' K₂ₒ : Stack} :
    ∀ (P P' : Stack),
    KrelS m X D eₛ g (P ++ Frame.handleF nid hh :: Ko') (P' ++ Frame.handleF nid h' :: K₂ₒ) →
    P.length = P'.length →
    ∃ (Dᵢ : CTy Eff Mult), KrelS m X Dᵢ eₛ g P P' := by
  intro P
  induction P with
  | nil =>
      intro P' hK hlen
      cases P' with
      | nil => exact ⟨X, by rw [krelS_nil]; exact ⟨rfl, fun q A hC v₁ v₂ _ _ _ _ => ⟨1, v₂, rfl⟩⟩⟩
      | cons _ _ => simp at hlen
  | cons fr P₀ ih =>
      intro P' hK hlen
      cases P' with
      | nil => simp at hlen
      | cons fr₂ P₀' =>
          rw [List.cons_append, List.cons_append] at hK
          have hlen' : P₀.length = P₀'.length := by simpa using hlen
          cases fr <;> cases fr₂ <;>
            first
              | (exact absurd hK (by simp only [KrelS]; exact not_false))
              | (rw [krelS_letF] at hK
                 obtain ⟨q, A, B, φ, hC, hbody, htail⟩ := hK
                 obtain ⟨Dᵢ, hrec⟩ := ih P₀' htail hlen'
                 exact ⟨Dᵢ, by rw [krelS_letF]; exact ⟨q, A, B, φ, hC, hbody, hrec⟩⟩)
              | (rw [krelS_appF] at hK
                 obtain ⟨q, A, B, hC, hcw₁, hcw₂, hw, htail⟩ := hK
                 obtain ⟨Dᵢ, hrec⟩ := ih P₀' htail hlen'
                 exact ⟨Dᵢ, by rw [krelS_appF]; exact ⟨q, A, B, hC, hcw₁, hcw₂, hw, hrec⟩⟩)
              | (rw [krelS_handleF] at hK
                 obtain ⟨hmid, hHRp, htail, hresp⟩ := hK
                 obtain ⟨Dᵢ, hrec⟩ := ih P₀' htail hlen'
                 refine ⟨Dᵢ, ?_⟩
                 rw [krelS_handleF]
                 refine ⟨hmid, hHRp, hrec, ?_⟩
                 trace_state
                 sorry)

end Bang
