import Bang.Meta.BinaryLR

/-! # BWitnessUniqueInResume — the (a)-vs-(b) DISTINGUISHING WITNESS for task #29 item 1.

RULING'S CHECK: is the SKIP-strip's `nid ∉ <inner stack>` fact needed (a) only at the OUTER
splitAtId application (→ top-level premise on krelS_splitAtId_decomp, callers discharge, no def
change), or (b) INSIDE KrelS's resume-conjunct occurrence where a top-level premise can't reach
(→ def-shape enrichment forced, kernel-engineer consult)?

VERDICT: (b), machine-checked below.
 • `strip_with_fact` (GREEN): the strip CLOSES given `splitAtId Q nid = none` on the resume-result
   inner prefix Q — so IF the fact were reachable, no def change would be needed (the (a)-form).
 • `strip_mislocates_when_nid_in_prefix` (GREEN refutation): but the fact is NOT reachable — the
   resume conjunct binds `Kᵢ` (the captured continuation) UNIVERSALLY with ONLY `KrelS m Cᵢ C εᵢ g
   Kᵢ Kᵢ'` (krelS_handleF, LR.lean:1290/1294), NO uniqueness. A concrete `Kᵢ` containing `handleF nid`
   makes `splitAtId` land on Kᵢ's frame, NOT the appended boundary. A top-level premise on the LEMMA
   cannot constrain this bound `Kᵢ`; only a premise CARRIED ON the resume conjunct (a KrelS-def
   change) can. Hence (b): the def-shape enrichment is genuinely forced. -/

namespace Bang
open Bang.EffectRow (Label)
variable {Eff  : Type} [Lattice Eff] [OrderBot Eff]
variable {Mult : Type} [CommSemiring Mult] [DecidableEq Mult]
variable [EffSig Eff Mult]

-- (a)-form: the strip CLOSES given the uniqueness fact on the resume-result inner prefix Q. GREEN.
theorem strip_with_fact {nid : Nat} {hh : Handler} {Q Ko' : Stack}
    (hnone : Bang.splitAtId Q nid = none) :
    Bang.splitAtId (Q ++ Frame.handleF nid hh :: Ko') nid = some (Q, hh, Ko') := by
  induction Q with
  | nil => simp [splitAtId]
  | cons fr Q₀ ih =>
      cases fr with
      | handleF m hd =>
          simp only [splitAtId] at hnone
          by_cases hmj : m = nid
          · rw [if_pos hmj] at hnone; simp at hnone
          · rw [if_neg hmj] at hnone
            simp only [List.cons_append, splitAtId, if_neg hmj,
              ih (Option.map_eq_none_iff.mp hnone), Option.map_some]
      | letF N => simp only [splitAtId, Option.map_eq_none_iff] at hnone
                  simp only [List.cons_append, splitAtId, ih hnone, Option.map_some]
      | appF w => simp only [splitAtId, Option.map_eq_none_iff] at hnone
                  simp only [List.cons_append, splitAtId, ih hnone, Option.map_some]

-- (b) REFUTATION: the resume conjunct's bound `Kᵢ` may contain `nid` (its ONLY constraint is a KrelS,
-- no uniqueness), and then splitAtId MISLOCATES — finds Kᵢ's frame, not the appended boundary. So the
-- needed fact is NOT derivable from the resume conjunct's hypotheses; only a premise ON the conjunct
-- (inside KrelS) supplies it. Concrete: Kᵢ = [handleF nid _], appended boundary at mh₁ ≠ nid.
theorem strip_mislocates_when_nid_in_prefix :
    ∃ (nid mh₁ : Nat) (Kᵢ Ki' Ko' : Stack) (hh reinstall : Handler),
      nid ≠ mh₁ ∧
      Bang.splitAtId (Kᵢ ++ Frame.handleF mh₁ reinstall :: Ki') nid
        ≠ some (Kᵢ ++ Frame.handleF mh₁ reinstall :: Ki', hh, Ko') := by
  refine ⟨0, 1, [Frame.handleF 0 (Handler.throws 1)], [], [],
    Handler.throws 1, Handler.throws 1, (by decide), ?_⟩
  -- splitAtId finds the FIRST id-0 frame (Kᵢ's head) ⟹ inner prefix [], NOT the full-prefix boundary.
  simp [splitAtId]

end Bang
#print axioms Bang.strip_with_fact
#print axioms Bang.strip_mislocates_when_nid_in_prefix
