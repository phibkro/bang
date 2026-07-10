import Bang.Meta.LR
import Bang.Core.Semantics.Invariants

/-! # KrelSLetFEqProbe — CAN the letF/appF eq-lemma stay BYTE-IDENTICAL after adding the outer
StackInc conjunct? The outer `StackInc(letF::K₁) = StackInc K₁`, and the RHS's tail
`KrelS n B D φ g K₁ K₂` (with ITS outer conjunct) already asserts `StackInc K₁ ∧ StackInc K₂`. So the
outer conjunct is REDUNDANT with the tail → the eq-lemma needs no new conjunct → consumers unaffected. -/

namespace Bang
open Bang.EffectRow (Label)
variable {Eff  : Type} [Lattice Eff] [OrderBot Eff]
variable {Mult : Type} [CommSemiring Mult] [DecidableEq Mult]
variable [EffSig Eff Mult]

-- helper: KrelS's outer conjunct is extractable (the def wraps it).
theorem krelS_gives_stackInc {n : Nat} {C D : CTy Eff Mult} {ε : Eff} {g : Nat} {K₁ K₂ : Stack}
    (h : KrelS n C D ε g K₁ K₂) : StackInc K₁ ∧ StackInc K₂ := by
  rw [KrelS] at h; exact h.1

-- the letF eq-lemma, BYTE-IDENTICAL statement (no StackInc conjunct), proven with the outer conjunct
-- reconstructed from the tail-KrelS in the backward direction.
theorem krelS_letF' {n : Nat} {C D : CTy Eff Mult} {ε : Eff} {g : Nat} {N₁ N₂ : Comp} {K₁ K₂ : Stack} :
    KrelS n C D ε g (Frame.letF N₁ :: K₁) (Frame.letF N₂ :: K₂) ↔
      ∃ q A B φ, C = CTy.F q A ∧
        (∀ m, m < n → ∀ v₁ v₂, Val.Closed v₁ → Val.Closed v₂ → VrelK m A v₁ v₂ →
          CrelK m B φ (Comp.subst v₁ N₁) (Comp.subst v₂ N₂))
        ∧ KrelS n B D φ g K₁ K₂ := by
  rw [KrelS]
  constructor
  · rintro ⟨_, q, A, B, φ, hC, hbody, htail⟩; exact ⟨q, A, B, φ, hC, hbody, htail⟩
  · rintro ⟨q, A, B, φ, hC, hbody, htail⟩
    -- reconstruct the outer conjunct: StackInc (letF::K₁) = StackInc K₁, from the tail-KrelS.
    obtain ⟨hi1, hi2⟩ := krelS_gives_stackInc htail
    exact ⟨⟨hi1, hi2⟩, q, A, B, φ, hC, hbody, htail⟩

end Bang
#print axioms Bang.krelS_letF'
