import Bang.Meta.BinaryLR
import Bang.Core.Semantics.Invariants

/-! # SkipStripSufficiencyProbe — is `StackAbove nid` on the resume-result prefix SUFFICIENT to locate
the SKIP-arm strip boundary? Target: `splitAtId (Kⱼ ++ handleF mh₁ reinstall :: Ki' ++ handleF nid hh
:: Ko') nid = some (prefix, hh, Ko')`. The prefix carries `nid < mh₁` (mh₁ inner, minted later) and
StackAbove-nid on Kⱼ,Ki' — all TRUE of a real run's captured pieces. -/

namespace Bang
open Bang.EffectRow (Label)
variable {Eff  : Type} [Lattice Eff] [OrderBot Eff]
variable {Mult : Type} [CommSemiring Mult] [DecidableEq Mult]
variable [EffSig Eff Mult]

/-- Every handleF id on `K` is strictly `> nid`. -/
def StackAbove (nid : Nat) : EvalCtx → Prop
  | [] => True
  | .handleF n _ :: K => nid < n ∧ StackAbove nid K
  | .letF _ :: K => StackAbove nid K
  | .appF _ :: K => StackAbove nid K

theorem stackAbove_append (nid : Nat) : ∀ (K1 K2 : EvalCtx),
    StackAbove nid (K1 ++ K2) ↔ (StackAbove nid K1 ∧ StackAbove nid K2) := by
  intro K1 K2
  induction K1 with
  | nil => simp only [List.nil_append, StackAbove, true_and]
  | cons fr K1 ih =>
    cases fr with
    | handleF n hd => simp only [List.cons_append, StackAbove, ih]; tauto
    | letF N => simp only [List.cons_append, StackAbove]; exact ih
    | appF w => simp only [List.cons_append, StackAbove]; exact ih

theorem splitAtId_above (nid : Nat) (K : EvalCtx) (h : StackAbove nid K) :
    Bang.splitAtId K nid = none := by
  induction K with
  | nil => rfl
  | cons fr K ih =>
    cases fr with
    | handleF n hd =>
      obtain ⟨hlt, hrest⟩ := h
      simp only [splitAtId]; rw [if_neg (by omega : ¬ n = nid), ih hrest]; rfl
    | letF N => simp only [splitAtId]; rw [ih h]; rfl
    | appF v => simp only [splitAtId]; rw [ih h]; rfl

-- inlined splitAtId_append_boundary (lives in scratch/DecompFreshStrip, not the imported module)
theorem splitAtId_append_boundary' {nid : Nat} {hh : Handler} :
    ∀ (Q Ko' : Stack), Bang.splitAtId Q nid = none →
    Bang.splitAtId (Q ++ Frame.handleF nid hh :: Ko') nid = some (Q, hh, Ko') := by
  intro Q
  induction Q with
  | nil => intro Ko' _; simp [splitAtId]
  | cons fr Q₀ ih =>
      intro Ko' hnone
      cases fr with
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

/-- THE COMPOSITE STRIP boundary-location, from the run-true facts. -/
theorem skip_strip_locates {nid mh₁ : Nat} {reinstall hh : Handler} {Kⱼ Ki' Ko' : Stack}
    (hlt : nid < mh₁) (hAj : StackAbove nid Kⱼ) (hAi : StackAbove nid Ki') :
    Bang.splitAtId ((Kⱼ ++ Frame.handleF mh₁ reinstall :: Ki') ++ Frame.handleF nid hh :: Ko') nid
      = some (Kⱼ ++ Frame.handleF mh₁ reinstall :: Ki', hh, Ko') := by
  have hpref : StackAbove nid (Kⱼ ++ Frame.handleF mh₁ reinstall :: Ki') := by
    rw [stackAbove_append]; exact ⟨hAj, ⟨hlt, hAi⟩⟩
  exact splitAtId_append_boundary' _ Ko' (splitAtId_above nid _ hpref)

end Bang
#print axioms Bang.skip_strip_locates
