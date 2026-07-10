import Bang.Meta.BinaryLR

namespace Bang
open Bang.EffectRow (Label)
variable {Eff  : Type} [Lattice Eff] [OrderBot Eff]
variable {Mult : Type} [CommSemiring Mult] [DecidableEq Mult]
variable [EffSig Eff Mult]

theorem KrelS_length_eq {n : Nat} {C D : CTy Eff Mult} {ε : Eff} {g : Nat} :
    ∀ {K₁ K₂ : Stack}, KrelS n C D ε g K₁ K₂ → K₁.length = K₂.length := by
  intro K₁
  induction K₁ generalizing C D ε with
  | nil => intro K₂ hK; cases K₂ with
    | nil => rfl
    | cons fr₂ K₂' => exact absurd hK (by simp only [KrelS]; cases fr₂ <;> exact not_false)
  | cons fr K₁' ih =>
      intro K₂ hK
      cases K₂ with
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

end Bang
