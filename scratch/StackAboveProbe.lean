import Bang.Meta.BinaryLR
import Bang.Core.Semantics.Invariants

/-! # StackAboveProbe — the CORRECT carrier shape for the item-1 strip.
The strip needs `splitAtId Kᵢ nid = none` for a LIVE deep-catcher id `nid`. StackBelow g (ids < g)
is REFUTED insufficient (StackBelowInsufficientProbe). The real fact: Kᵢ is captured ABOVE the nid
frame, so all its ids are `> nid` (inner frames mint later). Define `StackAbove nid K` = every
handleF id on K is `> nid`; prove it gives `splitAtId K nid = none`. -/

namespace Bang
open Bang.EffectRow (Label)
variable {Eff  : Type} [Lattice Eff] [OrderBot Eff]
variable {Mult : Type} [CommSemiring Mult] [DecidableEq Mult]
variable [EffSig Eff Mult]

/-- Every handleF id on `K` is strictly `> nid` (the dual of `StackBelow`). -/
def StackAbove (nid : Nat) : EvalCtx → Prop
  | [] => True
  | .handleF n _ :: K => nid < n ∧ StackAbove nid K
  | .letF _ :: K => StackAbove nid K
  | .appF _ :: K => StackAbove nid K

/-- `StackAbove nid K → splitAtId K nid = none`: nid matches no frame (all are strictly above). -/
theorem splitAtId_above (nid : Nat) (K : EvalCtx) (h : StackAbove nid K) :
    Bang.splitAtId K nid = none := by
  induction K with
  | nil => rfl
  | cons fr K ih =>
    cases fr with
    | handleF n hd =>
      obtain ⟨hlt, hrest⟩ := h
      simp only [splitAtId]
      rw [if_neg (by omega : ¬ n = nid), ih hrest]; rfl
    | letF N => simp only [splitAtId]; rw [ih h]; rfl
    | appF v => simp only [splitAtId]; rw [ih h]; rfl

end Bang
#print axioms Bang.splitAtId_above
