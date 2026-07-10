import Bang.Meta.BinaryLR
import Bang.Core.Semantics.Invariants

/-! # SkipArmChainProbe — does the FULL SKIP-arm freshness chain close from `StackInc` on the
resume-RESULT stack (what stackInc_reinstall gives from StackInc K₁)? The bound Kⱼ's StackAbove-nid
comes NOT from the resume conjunct's KrelS-Kⱼ (only gives StackInc Kⱼ), but from StackInc on the whole
resume-result prefix `Kⱼ ++ handleF mh₁ reinstall :: Ki'`. -/

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
  intro K1 K2; induction K1 with
  | nil => simp only [List.nil_append, StackBelow, true_and]
  | cons fr K1 ih => cases fr with
    | handleF n hd => simp only [List.cons_append, StackBelow, ih]; tauto
    | letF N => simp only [List.cons_append, StackBelow]; exact ih
    | appF w => simp only [List.cons_append, StackBelow]; exact ih

theorem stackAbove_mono {nid nid' : Nat} (hle : nid ≤ nid') :
    ∀ K, StackAbove nid' K → StackAbove nid K := by
  intro K h; induction K with
  | nil => trivial
  | cons fr K ih => cases fr with
    | handleF n hd => obtain ⟨hlt, hr⟩ := h; exact ⟨by omega, ih hr⟩
    | letF N => exact ih h
    | appF w => exact ih h

theorem stackInc_gives_above {nid : Nat} {Kⱼ Kₒ : EvalCtx} {hh : Handler}
    (h : StackInc (Kⱼ ++ Frame.handleF nid hh :: Kₒ)) : StackAbove nid Kⱼ := by
  induction Kⱼ with
  | nil => trivial
  | cons fr Kⱼ' ih => cases fr with
    | handleF m hd =>
      simp only [List.cons_append, StackInc] at h; obtain ⟨hincrest, hbelow⟩ := h
      have hnm : nid < m := ((stackBelow_append_local m Kⱼ' (Frame.handleF nid hh :: Kₒ)).mp hbelow).2.1
      exact ⟨hnm, ih hincrest⟩
    | letF N => simp only [List.cons_append, StackInc] at h; exact ih h
    | appF w => simp only [List.cons_append, StackInc] at h; exact ih h

theorem splitAtId_above (nid : Nat) (K : EvalCtx) (h : StackAbove nid K) :
    Bang.splitAtId K nid = none := by
  induction K with
  | nil => rfl
  | cons fr K ih => cases fr with
    | handleF n hd => obtain ⟨hlt, hrest⟩ := h
                      simp only [splitAtId]; rw [if_neg (by omega : ¬ n = nid), ih hrest]; rfl
    | letF N => simp only [splitAtId]; rw [ih h]; rfl
    | appF v => simp only [splitAtId]; rw [ih h]; rfl

theorem splitAtId_append_boundary' {nid : Nat} {hh : Handler} :
    ∀ (Q Ko' : Stack), Bang.splitAtId Q nid = none →
    Bang.splitAtId (Q ++ Frame.handleF nid hh :: Ko') nid = some (Q, hh, Ko') := by
  intro Q; induction Q with
  | nil => intro Ko' _; simp [splitAtId]
  | cons fr Q₀ ih => intro Ko' hnone; cases fr with
    | handleF m hd =>
        simp only [splitAtId] at hnone
        by_cases hmj : m = nid
        · rw [if_pos hmj] at hnone; simp at hnone
        · rw [if_neg hmj] at hnone
          simp only [List.cons_append, splitAtId, if_neg hmj,
            ih Ko' (Option.map_eq_none_iff.mp hnone), Option.map_some]
    | letF N => simp only [splitAtId, Option.map_eq_none_iff] at hnone
                simp only [List.cons_append, splitAtId, ih Ko' hnone, Option.map_some]
    | appF w => simp only [splitAtId, Option.map_eq_none_iff] at hnone
                simp only [List.cons_append, splitAtId, ih Ko' hnone, Option.map_some]

theorem stackAbove_append_local (nid : Nat) : ∀ (K1 K2 : EvalCtx),
    StackAbove nid (K1 ++ K2) ↔ (StackAbove nid K1 ∧ StackAbove nid K2) := by
  intro K1 K2; induction K1 with
  | nil => simp only [List.nil_append, StackAbove, true_and]
  | cons fr K1 ih => cases fr with
    | handleF n hd => simp only [List.cons_append, StackAbove, ih]; tauto
    | letF N => simp only [List.cons_append, StackAbove]; exact ih
    | appF w => simp only [List.cons_append, StackAbove]; exact ih

/-- THE FULL CHAIN: both StackAbove-nid facts trace to `StackInc` on machine-reached configs —
`StackAbove nid Kⱼ` from `StackInc` on the resume-RESULT (via mono from `StackAbove mh₁ Kⱼ`),
`StackAbove nid Ki'` from the ORIGINAL `StackInc K₁` (where Ki' sat just above the nid catcher). -/
theorem skip_arm_chain {nid mh₁ : Nat} {reinstall hh : Handler} {Kⱼ Ki' Ko' : Stack}
    (hlt : nid < mh₁)
    (hIncRes : StackInc (Kⱼ ++ Frame.handleF mh₁ reinstall :: Ki'))
    (hAiOrig : StackAbove nid Ki') :
    Bang.splitAtId ((Kⱼ ++ Frame.handleF mh₁ reinstall :: Ki') ++ Frame.handleF nid hh :: Ko') nid
      = some (Kⱼ ++ Frame.handleF mh₁ reinstall :: Ki', hh, Ko') := by
  have hAj : StackAbove nid Kⱼ := stackAbove_mono (Nat.le_of_lt hlt) Kⱼ (stackInc_gives_above hIncRes)
  have hpref : StackAbove nid (Kⱼ ++ Frame.handleF mh₁ reinstall :: Ki') := by
    rw [stackAbove_append_local]; exact ⟨hAj, ⟨hlt, hAiOrig⟩⟩
  exact splitAtId_append_boundary' _ Ko' (splitAtId_above nid _ hpref)

end Bang
#print axioms Bang.skip_arm_chain
