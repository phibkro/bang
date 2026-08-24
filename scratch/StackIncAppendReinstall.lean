import Bang.Meta.BinaryLR
import Bang.Core.Semantics.Invariants

/-! # StackIncAppendReinstall — the uniform fork-(B) helper: build StackInc (Kᵢ ++ handleF nh :: K)
from StackAbove nh Kᵢ (Kᵢ's ids all > nh) + StackInc Kᵢ + StackBelow nh K + StackInc K. This is the
one fact every reinstall's internal krelS_append needs; the caller supplies StackAbove nh Kᵢ from the
machine-reached resume conjunct (stackInc_gives_above). -/

namespace Bang
open Bang.EffectRow (Label)
variable {Eff  : Type} [Lattice Eff] [OrderBot Eff]
variable {Mult : Type} [CommSemiring Mult] [DecidableEq Mult]
variable [EffSig Eff Mult]

-- StackBelow distributes over ++ (re-proven; library one private).
theorem stackBelow_append_r (g : Nat) : ∀ (K1 K2 : EvalCtx),
    Bang.StackBelow g (K1 ++ K2) ↔ (Bang.StackBelow g K1 ∧ Bang.StackBelow g K2) := by
  intro K1 K2; induction K1 with
  | nil => simp only [List.nil_append, StackBelow, true_and]
  | cons fr K1 ih => cases fr with
    | handleF n hd => simp only [List.cons_append, StackBelow, ih]; tauto
    | letF N => simp only [List.cons_append, StackBelow]; exact ih
    | appF w => simp only [List.cons_append, StackBelow]; exact ih

/-- THE HELPER: Kᵢ above nh, Kᵢ increasing, nh above K, K increasing ⟹ the appended stack increasing.
Every frame in Kᵢ (id > nh) dominates `handleF nh :: K` (nh, then K's ids all < nh); K is increasing;
the head nh dominates K. -/
theorem stackInc_append_reinstall {nh : Nat} {Kᵢ K : EvalCtx} {h : Handler}
    (hAi : StackAbove nh Kᵢ) (hIi : StackInc Kᵢ) (hbK : StackBelow nh K) (hIK : StackInc K) :
    StackInc (Kᵢ ++ Frame.handleF nh h :: K) := by
  induction Kᵢ with
  | nil => exact ⟨hIK, hbK⟩
  | cons fr Kᵢ' ih =>
    cases fr with
    | handleF m hd =>
      obtain ⟨hmn, hArest⟩ := hAi
      obtain ⟨hIrest, hbrest⟩ := hIi
      -- StackInc (handleF m :: (Kᵢ' ++ handleF nh :: K)) = StackInc (Kᵢ'++…) ∧ StackBelow m (Kᵢ'++…)
      refine ⟨ih hArest hIrest, ?_⟩
      -- StackBelow m (Kᵢ' ++ handleF nh :: K): m dominates Kᵢ' (hbrest), m > nh (hmn), m dominates K
      -- (nh dominates K via hbK, and m > nh, so m dominates K by mono).
      rw [stackBelow_append_r]
      refine ⟨hbrest, ?_⟩
      simp only [StackBelow]
      exact ⟨hmn, StackBelow_mono_r (le_of_lt hmn) K hbK⟩
    | letF N => exact ih hAi hIi
    | appF w => exact ih hAi hIi

end Bang
#print axioms Bang.stackInc_append_reinstall
