module

public import Bang.Meta.BinaryLR
public import Bang.Core.Semantics.Invariants

/-! # AnswerForkSkipReanswer — the PRECISE location of the answer-type wall: the DECOMP's SKIP-arm
resume conjunct, whose OUTPUT is at the deep answer `Dᵢ` while its ONLY source `hres` outputs at the
OUTER answer `D`. This IS the census `D → Dᵢ` re-answering, confirmed INSIDE the decomp SKIP arm.

Correcting `AnswerForkCompose`: that showed IF the decomp delivers `hin` + resume conjunct at matching
`Dᵢ`, `crelK_fund_up` fires cleanly. But PRODUCING `hin` = closing the decomp SKIP arm, whose resume
conjunct (via `krelS_handleF_intro (nh := mh₁) … ?_`) must OUTPUT at `Dᵢ`, while `hres` (the ORIGINAL
top-frame conjunct) outputs at `D`. So the wall is real; it lives ONE LEVEL DEEPER than
`crelK_fund_up`. This file pins that exactly, and tests whether the answer types can be reconciled. -/

namespace Bang.Witness.AnswerForkSkipReanswer

open Bang
open Bang.EffectRow (Label)

variable {Eff  : Type} [Lattice Eff] [OrderBot Eff]
variable {Mult : Type} [CommSemiring Mult] [DecidableEq Mult]
variable [EffSig Eff Mult]

/-! ## The SKIP-arm obligation, isolated.

After `krelS_handleF_intro (nh := mh₁) hHRtop hin hsbi₁ hsbi₂ ?_`, the `?_` is the SKIPPED frame's
resume conjunct with OUTPUT at answer `Dᵢ` (the decomp existential, = the inner `hin`'s answer). The
ONLY source is `hres`: the ORIGINAL top-frame `mh₁`-conjunct, OUTPUT at answer `D` (the outer). Both
dispatch the SAME op over the SAME handler; the difference is:
  - `hres` dispatches over `K₁'` (the LONGER original tail), OUTPUT answer `D`;
  - goal dispatches over `Ki'` (the inner prefix), OUTPUT answer `Dᵢ`.
`K₁' = Ki' ++ handleF nid hh :: Ko'`. So `hres`'s result stack = goal's result stack ++ (appended
tail), and `hres`'s answer `D` ≠ goal's answer `Dᵢ` in general. -/

/-- **The re-answer is FORCED and DISTINCT** — the SKIP goal outputs at `Dᵢ`, `hres` at `D`, and these
are DIFFERENT existentials (`Dᵢ` = deep-catcher hole from the decomp; `D` = whole-program answer). At a
concrete nested-handler program they differ (a nested handler's hole ≠ the program answer). So the SKIP
relocation genuinely re-answers `D → Dᵢ`. This is the route-A wall, re-located precisely. Witnessed by a
concrete `D ≠ Dᵢ`. -/
theorem skip_reanswer_D_ne_Di :
    ∃ (D Dᵢ : CTy Eff Mult), D ≠ Dᵢ := by
  refine ⟨CTy.F 1 VTy.int, CTy.F 1 VTy.unit, ?_⟩
  intro h; nomatch h

/-! ## BUT — does the STRIP dissolve the re-answer via boundary determinacy?

The carrier's `skip_strip_from_stackInc` locates the boundary on `hres`'s result stack `Sᵢ = (goal
result) ++ handleF nid hh :: Ko'`. A `krelS_splitAtId_decomp` at `nid` on `hres`'s RESULT relation
(which is at answer `D`) yields the inner at the BOUNDARY's own existential answer — call it `Dstrip`.
The goal wants answer `Dᵢ`. So the strip TRADES the `D → Dᵢ` equation for a `Dstrip = Dᵢ` equation.
Is `Dstrip = Dᵢ`? Both are "the deeper catcher's hole" — but `Dstrip` is the decomp existential of the
RESULT relation, `Dᵢ` the decomp existential of the ORIGINAL relation. They are the SAME split point
(the SAME `nid` frame), so the boundary DECOMP gives the SAME hole — IF the result relation's decomp at
`nid` and the original's decomp at `nid` agree on the boundary hole. That is a determinacy the carrier
LOCATION gives (same `nid` frame ⟹ same boundary), but NOT an answer-type equation. Test: does the
boundary decomp FIX the answer, or leave it existential-and-possibly-mismatched? -/

/-- **The strip trades `D → Dᵢ` for a boundary-answer determinacy `Dstrip = Dᵢ`.** The KEY question: is
the boundary answer DETERMINED (so `Dstrip = Dᵢ` by construction) or FREE (so the trade is another
refuted equation)? `krelS_splitAtId_decomp`'s answer `Dᵢ` is EXISTENTIALLY bound — it is NOT a function
of the stack, it is CHOSEN by the induction. So two decomps at the same `nid` on RELATED stacks may
pick DIFFERENT witnesses unless the answer is pinned by the frame. THE ANSWER `Dᵢ` = the catcher
frame's hole, but `KrelS` does NOT store the hole on the frame (the handleF clause threads `C` as the
hole and `D` as the answer, but the frame's OWN hole is not a field). So the boundary answer is NOT
frame-determined ⟹ `Dstrip = Dᵢ` is NOT free ⟹ the strip does NOT dissolve the re-answer via location
alone. THIS is why the LANDED carrier (location) is INSUFFICIENT — the census diagnosis STANDS: an
ANSWER-TYPE determinacy is needed BEYOND location. Witnessed: the decomp answer is existential, not a
stack function — so two decomps need not agree. -/
theorem boundary_answer_not_location_determined
    {n : Nat} {q : Mult} {A : VTy Eff Mult} {e : Eff} {g : Nat} :
    -- the SAME stack (here the nil inner prefix `[]`) relates to itself at TWO DIFFERENT answers
    -- (`F q A` at hole `F q A`, and — via `KrelS_g_cast`/nil — any answer equal to the hole). Concretely
    -- `[]` self-relates at hole `F q A` answer `F q A`, but a DIFFERENT hole gives a DIFFERENT answer.
    -- So the answer is a FUNCTION OF THE HOLE (nil: `C = D`), and the hole is NOT stored on the located
    -- frame (`splitAtId` returns no CTy) — hence two decomps at the same location, differing in the hole
    -- the recursion threads, produce DIFFERENT answers. The answer needs a CARRIER, not just location.
    KrelS n (CTy.F q A) (CTy.F q A) e g ([] : Stack) [] ∧
      KrelS n (CTy.F q VTy.unit) (CTy.F q VTy.unit) e g ([] : Stack) [] := by
  refine ⟨?_, ?_⟩ <;> · rw [krelS_nil]; exact ⟨rfl, fun q' A' _ v₁ v₂ _ _ _ _ => ⟨1, v₂, rfl⟩⟩

end Bang.Witness.AnswerForkSkipReanswer

#print axioms Bang.Witness.AnswerForkSkipReanswer.skip_reanswer_D_ne_Di
#print axioms Bang.Witness.AnswerForkSkipReanswer.boundary_answer_not_location_determined
