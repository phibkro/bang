import Bang.Meta.BinaryLR
import Bang.Core.Semantics.Invariants

/-! # SkipArmOuterConjunctProbe — with the (i′) OUTER conjunct, KrelS on the resume-result Sᵢ gives
`StackInc Sᵢ` DIRECTLY, and Sᵢ = cfgg₁.1 ++ (handleF nid hh :: Ko') CONTAINS the nid boundary — so
`stackInc_gives_above` yields `StackAbove nid cfgg₁.1` in one step (cleaner than tracking Kⱼ/Ki'
separately). This probe confirms the SKIP-arm strip closes from that single StackInc-Sᵢ fact. -/

namespace Bang
open Bang.EffectRow (Label)
variable {Eff  : Type} [Lattice Eff] [OrderBot Eff]
variable {Mult : Type} [CommSemiring Mult] [DecidableEq Mult]
variable [EffSig Eff Mult]

-- inlined splitAtId_append_boundary (the ready-made strip close)
theorem splitAtId_append_boundary'' {nid : Nat} {hh : Handler} :
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

/-- THE STRIP from a SINGLE StackInc-on-Sᵢ fact (what the outer conjunct provides on hSrel's stack).
Sᵢ = prefix ++ handleF nid hh :: Ko'; StackInc Sᵢ → StackAbove nid prefix → splitAtId prefix nid = none
→ the boundary is located. -/
theorem skip_strip_from_stackInc {nid : Nat} {hh : Handler} {prefix_ Ko' : Stack}
    (hInc : StackInc (prefix_ ++ Frame.handleF nid hh :: Ko')) :
    Bang.splitAtId (prefix_ ++ Frame.handleF nid hh :: Ko') nid = some (prefix_, hh, Ko') :=
  splitAtId_append_boundary'' _ Ko' (splitAtId_above nid _ (stackInc_gives_above hInc))

end Bang
#print axioms Bang.skip_strip_from_stackInc
