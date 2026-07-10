module

public import Bang.Meta.BinaryLR
public import Bang.Core.Semantics.Invariants

/-! # AnswerForkSkip — the DECOMP's SKIP-relocation residual, isolated, and whether the LANDED carrier
(`skip_strip_from_stackInc` + `dispatchOn_append_outer`) closes it WITHOUT a NEW answer-type carrier.

The `crelK_fund_up` resume arm closes via the FULL decomp `krelS_splitAtId_decomp` (its `hin` +
resume conjunct share `Dᵢ`, so NO `D → Dᵢ` re-answering — `AnswerForkCompose.decomp_route_fires_no_reanswer`,
axiom-clean). The decomp's OWN sorry is the SKIP relocation: the skipped frame `mh₁`'s resume conjunct
over the LONGER tail `K₁'` must relocate to the recursed inner prefix `Ki'` (where `splitAtId` placed
the deeper catcher). `K₁' = Ki' ++ handleF nid hh :: Ko'`.

This file ISOLATES that relocation and tests the composition:
  dispatch over Ki' → LIFT to K₁' (dispatchOn_append_outer) → feed `hres` (over K₁') → STRIP the
  appended tail off the result (skip_strip_from_stackInc / splitAtId_append_boundary).
The question: does the STRIP preserve the answer type, or does an answer-type carrier ADDITION help? -/

namespace Bang.Witness.AnswerForkSkip

open Bang
open Bang.EffectRow (Label)

variable {Eff  : Type} [Lattice Eff] [OrderBot Eff]
variable {Mult : Type} [CommSemiring Mult] [DecidableEq Mult]
variable [EffSig Eff Mult]

/-! ## The LIFT half (forward direction) — dispatchOn over Ki' lifts to K₁'.

`dispatchOn_append_outer` (BANKED, axiom-clean) lifts a dispatch over `(Kᵢ, hh, Ki')` to `(Kᵢ, hh,
Ki' ++ T)` = a dispatch over the longer OUTER stack, appending `T` to the result's stack. This is the
forward direction — used to FEED `hres` (which dispatches over `K₁' = Ki' ++ handleF nid hh :: Ko'`).
Confirm it fires for the SKIP relocation's `T = handleF nid hh :: Ko'`. -/

/-- **The lift is DIRECT** (`dispatchOn_append_outer`, banked). Given the inner dispatch over `Ki'`
(the recursed catcher's outer stack), lift to the ORIGINAL `K₁' = Ki' ++ handleF nid hh :: Ko'`,
appending the skipped-frame tail to the result. NO answer type involved — pure structural. -/
theorem skip_lift_direct
    (mh₁ : Nat) (op : OpId) (w : Val) (Kᵢ : Stack) (hh₁ : Handler) (Ki' : Stack)
    (T : Stack) {cfg : EvalCtx × Comp}
    (hd : Bang.dispatchOn mh₁ op w (Kᵢ, hh₁, Ki') = some cfg) :
    Bang.dispatchOn mh₁ op w (Kᵢ, hh₁, Ki' ++ T) = some (cfg.1 ++ T, cfg.2) :=
  dispatchOn_append_outer mh₁ op w Kᵢ hh₁ Ki' T hd

/-! ## The STRIP half (inverse direction) — the ACTUAL residual.

`hres` (over `K₁'`) yields a resume result `KrelS k (F qᵣ Aᵣ) Dtop eₛ g Sᵢ Sᵢ'` where `Sᵢ = cfg₁.1 ++
handleF nid hh :: Ko'` (the LIFTED result, so `Sᵢ` has the appended tail) and `Dtop` = the SKIPPED
frame's own answer. The relocation goal wants `KrelS k (F qᵣ Aᵣ) Ddeep eₛ g cfg₁.1 cfg₂.1` at the
DEEPER catcher's answer `Ddeep` — i.e. STRIP `handleF nid hh :: Ko'` off `Sᵢ` and RE-ANSWER from
`Dtop` to `Ddeep`. THIS is where the route-A `Dⱼ = Dᵢ` refutation lives.

BUT: with the carrier, `skip_strip_from_stackInc` LOCATES the boundary (`splitAtId Sᵢ nid = some
(cfg₁.1, hh, Ko')`). So the strip is a DECOMP at `nid` on `Sᵢ` — which `krelS_splitAtId_decomp`
handles, yielding the inner at the boundary's answer. The answer at the boundary IS `Ddeep` (the
deeper catcher's hole), delivered as the decomp's existential — NOT re-answered by equation. So the
strip's answer is FIXED by the SAME construction as the forward decomp. Model the strip's answer-source
below: it is the boundary-decomp's existential, not a cross-answer equation. -/

/-- **The strip's answer comes from a boundary DECOMP existential, not a re-answering.** Given a
`KrelS`-related pair whose LEFT is `Sᵢ = P ++ handleF nid hh :: Ko'` with `StackInc Sᵢ` (carrier),
`skip_strip_from_stackInc` locates the boundary, and `krelS_splitAtId_decomp` at `nid` delivers the
inner relation `KrelS k (hole) Dboundary e g P (rhs-inner)` at the boundary's OWN existential answer
`Dboundary`. So the strip's answer is a FRESH existential from the decomp — the SAME mechanism the
forward pass uses. NO `Dtop → Ddeep` equation is imposed; the answer is threaded as DATA. This is the
fork-(a) "carry the answer as DATA" realized THROUGH the existing decomp existential — meaning the
LANDED carrier already supplies the answer-as-data, no NEW carrier needed. Skeleton (the decomp's own
SKIP sorry is the recursion base, so this is stated as the composition shape, body sorry-ed). -/
theorem skip_strip_answer_is_decomp_existential
    {k : Nat} {hole : CTy Eff Mult} {D : CTy Eff Mult} {e : Eff} {g nid : Nat}
    {P Ko' RHS : Stack} {hh : Handler}
    (hK : KrelS k hole D e g (P ++ Frame.handleF nid hh :: Ko') RHS)
    (hInc : StackInc (P ++ Frame.handleF nid hh :: Ko')) :
    -- the strip yields an inner relation at the BOUNDARY's own existential answer `Dboundary` — DATA,
    -- not a re-answered equation. Exactly the decomp's `hin`-at-`Dᵢ` shape.
    ∃ (RHSᵢ RHSₒ : Stack) (h' : Handler) (Dboundary : CTy Eff Mult) (C' : CTy Eff Mult) (e' : Eff),
      Bang.splitAtId RHS nid = some (RHSᵢ, h', RHSₒ) ∧ HandlerRel Eff Mult k hh h' ∧
      KrelS k hole Dboundary e g P RHSᵢ := by
  -- locate the boundary on the LEFT (carrier gives freshness of the prefix):
  have hloc : Bang.splitAtId (P ++ Frame.handleF nid hh :: Ko') nid = some (P, hh, Ko') :=
    skip_strip_from_stackInc hInc
  -- the decomp at nid delivers the inner at the boundary's OWN answer existential:
  obtain ⟨RHSᵢ, RHSₒ, h', Dboundary, C', e', hsp2, hHR, hin, _htail2, _hres2⟩ :=
    krelS_splitAtId_decomp hK hloc
  exact ⟨RHSᵢ, RHSₒ, h', Dboundary, C', e', hsp2, hHR, hin⟩

end Bang.Witness.AnswerForkSkip

#print axioms Bang.Witness.AnswerForkSkip.skip_lift_direct
#print axioms Bang.Witness.AnswerForkSkip.skip_strip_answer_is_decomp_existential
