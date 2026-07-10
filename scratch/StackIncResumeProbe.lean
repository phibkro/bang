import Bang.Meta.BinaryLR
import Bang.Core.Semantics.Invariants
import Bang.Core.Soundness

/-! # StackIncResumeProbe — the RESUME arm: does reinstalling `handleF n` (same id, deep) preserve
StackInc? This is the last viability gate for StackInc as a full machine invariant. -/

namespace Bang
open Bang.EffectRow (Label)
variable {Eff  : Type} [Lattice Eff] [OrderBot Eff]
variable {Mult : Type} [CommSemiring Mult] [DecidableEq Mult]
variable [EffSig Eff Mult]

def StackAbove (nid : Nat) : EvalCtx → Prop
  | [] => True
  | .handleF n _ :: K => nid < n ∧ StackAbove nid K
  | .letF _ :: K => StackAbove nid K
  | .appF _ :: K => StackAbove nid K

def StackInc : EvalCtx → Prop
  | [] => True
  | .handleF n _ :: K => StackInc K ∧ Bang.StackBelow n K
  | .letF _ :: K => StackInc K
  | .appF _ :: K => StackInc K

theorem stackBelow_append_local (g : Nat) : ∀ (K1 K2 : EvalCtx),
    Bang.StackBelow g (K1 ++ K2) ↔ (Bang.StackBelow g K1 ∧ Bang.StackBelow g K2) := by
  intro K1 K2
  induction K1 with
  | nil => simp only [List.nil_append, StackBelow, true_and]
  | cons fr K1 ih =>
    cases fr with
    | handleF n hd => simp only [List.cons_append, StackBelow, ih]; tauto
    | letF N => simp only [List.cons_append, StackBelow]; exact ih
    | appF w => simp only [List.cons_append, StackBelow]; exact ih

/-- RESUME preservation: the reinstalled stack `Kᵢ ++ handleF n reinstall :: Kₒ` has the SAME shape as
the original `Kᵢ ++ handleF n h :: Kₒ` (only the handler payload changes, id `n` fixed), so StackInc is
preserved verbatim — the ordering facts are id-only, payload-blind. -/
theorem stackInc_reinstall {n : Nat} {Kᵢ Kₒ : EvalCtx} {h reinstall : Handler}
    (h0 : StackInc (Kᵢ ++ Frame.handleF n h :: Kₒ)) :
    StackInc (Kᵢ ++ Frame.handleF n reinstall :: Kₒ) := by
  induction Kᵢ with
  | nil =>
    simp only [List.nil_append, StackInc] at h0 ⊢; exact h0
  | cons fr Kᵢ' ih =>
    cases fr with
    | handleF m hd =>
      simp only [List.cons_append, StackInc] at h0 ⊢
      obtain ⟨hincrest, hbelow⟩ := h0
      refine ⟨ih hincrest, ?_⟩
      -- StackBelow m (Kᵢ' ++ handleF n h :: Kₒ) ↔ StackBelow m (Kᵢ' ++ handleF n reinstall :: Kₒ)
      -- (StackBelow is id-only, payload-blind — the middle frame's id n unchanged)
      rw [stackBelow_append_local] at hbelow ⊢
      simp only [StackBelow] at hbelow ⊢
      exact hbelow
    | letF N => simp only [List.cons_append, StackInc] at h0 ⊢; exact ih h0
    | appF w => simp only [List.cons_append, StackInc] at h0 ⊢; exact ih h0

end Bang
#print axioms Bang.stackInc_reinstall
