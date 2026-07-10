module

public import Bang.Meta.BinaryLR
public import Bang.Core.Semantics.Invariants
public import Bang.Witness.HoleDetRefute

/-! # HoleDetAlphaDelivery — route (α) STEP 4: GIVEN the strongest STATABLE conclusion datum, does
the census4 SKIP tie `Cb' = C'` become derivable?

## The delivery geometry (the SKIP arm, `BinaryLR.lean:1203-1223`)

After `krelS_handleF_intro`, the goal's resume dispatches `mh₁` over `(Kᵢ, hh₁, Ki')`, producing a
result stack `Sᵢ`. `hres` (the ORIGINAL resume of `hh₁`) dispatches over the LONGER tail
`K₁' = Ki' ++ handleF nid hh :: Ko'`; by `dispatchOn_append_outer` its result is `Sᵢ ++ handleF nid hh
:: Ko'`. To feed the goal (`KrelS m (F qᵣ Aᵣ) D eₛ g Sᵢ Sᵢ'`), the strip STRIPS the appended
`handleF nid hh :: Ko'` off `hres`'s result by re-decomposing at `nid`.

The re-decomposition delivers the inner `Sᵢ` at answer `Db` with `Db = Cb'` (the re-decomp's OWN
`Dᵢ=C'` output conjunct), where `Cb'` is the outer hole `hres`'s result assigns over `Ko'`. Closing
needs `Cb' = C'`, where `C'` is `ih`'s ORIGINAL outer hole over the SAME `Ko'` at the SAME answer `D`
(`ih`'s `KrelS n C' D e' g Ko' K₂ₒ`).

## Why NO conclusion datum delivers it (STEP 4 REFUTES)

Even the STRONGEST statable conclusion datum — "hand back the resume result's OWN
decomposition-at-`nid` outer hole `Cb'` directly" (the ADR's 'inner-relation extractor') — delivers
`Cb'` as `hres`'s result's outer hole. But `C'` comes from `ih`'s INDEPENDENT decomposition of the
ORIGINAL `Ko'`. These are TWO DISTINCT `KrelS` derivations over the same tail `Ko'` at the same answer
`D`; tying their holes IS `krelS_hole_det` on `Ko'` — REFUTED (`HoleDetRefute`). A conclusion
strengthening on `hres` can pin `hres`-result's own hole to anything it likes, but it CANNOT pin it to
`ih`'s independently-chosen `C'` — `ih` is not in `hres`'s scope, and the two holes are genuinely free
to differ over a `letF`/`appF`-headed `Ko'`.

## What the witness establishes

`two_independent_decomps_over_shared_tail_can_disagree` — over a shared `letF`/`appF`-headed tail
`Ko'`, two `KrelS` derivations at the SAME answer can carry DIFFERENT outer holes. So the "strip's
`Cb'`" (one derivation's hole) and "`ih`'s `C'`" (another's) are NOT forced equal by ANY datum local
to one derivation. This is the delivery refutation: the tie is inter-derivation, unreachable by a
conclusion strengthening on a single derivation.

`alpha_delivery_skeleton` — the delivery-skeleton shape: GIVEN a hypothetical conclusion datum
`hCb : Cb' = <hres-result's own hole>` (the best (α) can produce), the goal `Cb' = C'` STILL requires
`<hres-result's own hole> = C'`, which is the refuted inter-derivation tie — discharged here only by a
`sorry`, FLAGGED as the surviving wall. -/

namespace Bang.Witness

open Bang
open Bang.EffectRow (Label)

variable {Eff  : Type} [Lattice Eff] [OrderBot Eff]
variable {Mult : Type} [CommSemiring Mult] [DecidableEq Mult]
variable [EffSig Eff Mult]

/-- **The delivery refutation.** Two independent `KrelS` derivations over the SAME
`letF`-headed tail, at the SAME answer, carry DIFFERENT outer holes (`F 0 unit` vs `F 0 int`). So
"`hres`-result's outer hole `Cb'`" and "`ih`'s outer hole `C'`" — being holes of two DIFFERENT
derivations over the shared `Ko'` — are not forced equal. This is precisely the inter-derivation tie
the SKIP close needs and route (α)'s single-derivation conclusion datum cannot supply. -/
theorem two_independent_decomps_over_shared_tail_can_disagree :
    ∃ (Cb C' D : CTy Eff Mult) (e : Eff) (g : Nat) (Ko' K₂ₒ : Stack),
      KrelS 0 Cb D e g Ko' K₂ₒ ∧ KrelS 0 C' D e g Ko' K₂ₒ ∧ Cb ≠ C' := by
  obtain ⟨h1, h2⟩ := letF_relates_at_two_holes (Eff := Eff) (Mult := Mult)
  exact ⟨CTy.F 0 VTy.unit, CTy.F 0 VTy.int, CTy.F 0 VTy.unit, ⊥, 0,
    [Frame.letF (Comp.ret Val.vunit), Frame.appF Val.vunit],
    [Frame.letF (Comp.ret Val.vunit), Frame.appF Val.vunit],
    h1, h2, by simp⟩

/-- **The delivery skeleton (the tie is NOT dischargeable from a conclusion datum).** The SKIP close
needs `Cb' = C'`. Route (α)'s best conclusion datum gives `Cb'` = the resume result's OWN re-decomp
hole (`hStripHole`). The residual is then `<result's own hole> = C'` — the inter-derivation tie over
the shared `Ko'`. It is discharged here ONLY by `sorry` (FLAGGED): there is no fact tying the two
independent derivations, because hole-determinacy over `Ko'` is refuted. This is the surviving wall
under route (α). -/
theorem alpha_delivery_skeleton
    {n : Nat} {Cb' C' D : CTy Eff Mult} {e' : Eff} {g : Nat} {Ko' K₂ₒ : Stack}
    -- the strip's boundary-decomp delivers the resume result inner at answer `Cb'` (route (α)'s datum
    -- would supply this — the result's OWN re-decomp hole, statable on the conclusion):
    (hStrip : KrelS n Cb' D e' g Ko' K₂ₒ)
    -- `ih`'s ORIGINAL outer relation, INDEPENDENT derivation over the SAME `Ko'` at the SAME answer:
    (hOuter : KrelS n C' D e' g Ko' K₂ₒ) :
    Cb' = C' := by
  -- The tie `Cb' = C'` is `krelS_hole_det` on `Ko'` — REFUTED. No conclusion datum on `hStrip`
  -- reaches `hOuter`'s independently-chosen `C'`. THE SURVIVING WALL under route (α).
  sorry

end Bang.Witness

#print axioms Bang.Witness.two_independent_decomps_over_shared_tail_can_disagree
