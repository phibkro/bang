import Bang.Meta.BinaryLR
import Bang.Core.Semantics.Invariants

/-! # StackIncreasingProbe — viability gate for the ADR-0096 corrected carrier.
"Ids increase up the stack" (list head = TOP = largest id). Probe: mint preserves it, and it
delivers the `StackAbove nid` the strip needs on the region ABOVE a deep catcher `nid`. -/

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

-- StackBelow distributes over ++ (re-proven locally; the library one is private).
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

/-- MINT preserves StackInc: pushing `handleF g h` on a `StackBelow g` stack (the WellCounted fact)
gives `StackInc (handleF g h :: K)` since g dominates the tail. -/
theorem stackInc_mint {g : Nat} {h : Handler} {K : EvalCtx}
    (hinc : StackInc K) (hbelow : Bang.StackBelow g K) :
    StackInc (Frame.handleF g h :: K) := ⟨hinc, hbelow⟩

/-- The DELIVERY: from `StackInc` on `Kⱼ ++ handleF nid _ :: Kₒ`, the captured-above region `Kⱼ` is
`StackAbove nid` — exactly what the strip consumes. -/
theorem stackInc_gives_above {nid : Nat} {Kⱼ Kₒ : EvalCtx} {hh : Handler}
    (h : StackInc (Kⱼ ++ Frame.handleF nid hh :: Kₒ)) : StackAbove nid Kⱼ := by
  induction Kⱼ with
  | nil => trivial
  | cons fr Kⱼ' ih =>
    cases fr with
    | handleF m hd =>
      simp only [List.cons_append, StackInc] at h
      obtain ⟨hincrest, hbelow⟩ := h
      have hnm : nid < m := ((stackBelow_append_local m Kⱼ' (Frame.handleF nid hh :: Kₒ)).mp hbelow).2.1
      exact ⟨hnm, ih hincrest⟩
    | letF N => simp only [List.cons_append, StackInc] at h; exact ih h
    | appF w => simp only [List.cons_append, StackInc] at h; exact ih h

end Bang
#print axioms Bang.stackInc_gives_above
