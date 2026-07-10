module

public import Bang.Meta.BinaryLR
public import Bang.Core.Semantics.Invariants
public import Bang.Witness.HoleDetRefute

/-! # HoleDetAlphaStatability — route (α) STEP 1: can the hole-determinacy tie even be STATED on
the resume conjunct's conclusion, and does stating it SHRINK the relation below what the compat
cores / `krelS_refl` populate?

## What route (α) must carry (the SKIP-strip's exact need)

The census4 SKIP strip, given the resume conclusion's `KrelS m (F qᵣ Aᵣ) D eₛ g Sᵢ Sᵢ'`, re-decomposes
`Sᵢ` at the DEEP catcher id `nid` and gets an inner-region-at-`Db` with `Db = Cb'` (the re-decomposed
outer hole over the shared tail). To close it needs `Cb' = C'` where `C'` is the ORIGINAL outer hole
(from the first decomp, BEFORE the resume). So route (α) would ADD to the resume conclusion a datum
tying `Sᵢ`'s re-decomposition-at-`nid` outer hole to a KNOWN value.

## The statability obstruction (STEP 1)

**The resume conjunct does NOT have `nid`/`C'` in scope.** The `KrelS` handleF resume clause
(`LR.lean:1212`) universally binds `∀ m op w₁ w₂ Cᵢ εᵢ Kᵢ Kᵢ' cfg₁ cfg₂` and concludes about the
resume result `Sᵢ`. The captured continuation `Kᵢ` is UNIVERSALLY bound; the deeper catcher `nid`
that the OUTER decomposition will search for lives INSIDE `Kᵢ` (or inside the reinstalled tail),
which the conjunct treats abstractly. There is no `nid`/`C'` the conjunct can name.

So the ONLY way to state the tie generically is to QUANTIFY it: "for ALL `nid` and ALL decompositions
of `Sᵢ` at `nid`, the outer hole is <determined by the tail-pair>". But that is EXACTLY
`krelS_hole_det` re-imposed on `Sᵢ` — which `HoleDetRefute.krelS_hole_det_refuted` proves FALSE.
Carrying it as a def-conjunct would therefore SHRINK `KrelS` to the sub-relation where every
resume-result stack has determined holes at every internal catcher — a property the `letF`/`appF`
producers (`krelS_letF_intro`/`krelS_appF_intro`, which introduce holes with FREE `A`/`q`) cannot
supply.

## What the witnesses establish

1. `alpha_conclusion_conjunct_is_hole_det_on_Si` — the generic (nid-quantified) form of the tie IS
   `krelS_hole_det` specialized to `Sᵢ` (definitional unfolding of the requirement). Modelled: the
   requirement "∀ nid, decomp of Sᵢ at nid has outer hole C'-determined" reduces to the
   two-decomps-agree shape.
2. `alpha_conjunct_shrinks_out_letF_producer` — the letF producer `krelS_letF_intro` produces a
   `KrelS` whose head-hole `A` is caller-chosen and UNPINNED; requiring the def-conjunct
   (hole-det on the produced stack) makes `krelS_letF_intro` UNPROVABLE for the free-`A` instance
   (two calls with different `A` over the same tail both claim the conjunct, contradicting it).

Together: route (α)'s generic conclusion-tie is `krelS_hole_det` in disguise, refuted, and adding it
shrinks the relation below the producers. **STEP 1 REFUTES the GENERIC α-conjunct.** (The surgical
non-generic form — carrying `nid`/`C'` literally — is UNSTATABLE: they are not in scope.) -/

namespace Bang.Witness

open Bang
open Bang.EffectRow (Label)

variable {Eff  : Type} [Lattice Eff] [OrderBot Eff]
variable {Mult : Type} [CommSemiring Mult] [DecidableEq Mult]
variable [EffSig Eff Mult]

/-- **Statability obstruction, part 1.** The only GENERIC (scope-respecting) form of the hole-det tie
the resume conclusion can carry is: "the resume-result stack `Sᵢ` has a hole determined by its
(stack, answer)". Formalized as a predicate on a stack; it is `krelS_hole_det` restricted to that
stack. We show it IS the two-decomps-agree shape — so carrying it inherits the refutation. -/
def ResumeHoleDetOn (Eff Mult : Type) [Lattice Eff] [OrderBot Eff]
    [CommSemiring Mult] [DecidableEq Mult] [EffSig Eff Mult]
    (n : Nat) (D : CTy Eff Mult) (e : Eff) (g : Nat) (Sᵢ Sᵢ' : Stack) : Prop :=
  ∀ (C₁ C₂ : CTy Eff Mult), KrelS n C₁ D e g Sᵢ Sᵢ' → KrelS n C₂ D e g Sᵢ Sᵢ' → C₁ = C₂

/-- The generic α-conjunct on a resume result IS hole-determinacy restricted to that stack pair:
if EVERY resume conclusion carried `ResumeHoleDetOn … Sᵢ Sᵢ'`, then in particular the
`letF`/`appF`-headed resume results would be hole-determined — which the falsifier refutes for the
concrete `[letF, appF]` pair. -/
theorem alpha_conclusion_conjunct_is_hole_det_on_Si
    (Hgen : ∀ (n : Nat) (D : CTy Eff Mult) (e : Eff) (g : Nat) (Sᵢ Sᵢ' : Stack),
              ResumeHoleDetOn Eff Mult n D e g Sᵢ Sᵢ') :
    False := by
  -- specialize to the witness stack `[letF, appF]` (self-related at two holes, same answer)
  obtain ⟨h1, h2⟩ := letF_relates_at_two_holes (Eff := Eff) (Mult := Mult)
  have := Hgen 0 (CTy.F (0 : Mult) VTy.unit) ⊥ 0
    [Frame.letF (Comp.ret Val.vunit), Frame.appF Val.vunit]
    [Frame.letF (Comp.ret Val.vunit), Frame.appF Val.vunit]
    (CTy.F (0 : Mult) VTy.unit) (CTy.F (0 : Mult) VTy.int) h1 h2
  exact absurd this (by simp)

/-- **Statability obstruction, part 2.** The `letF` producer introduces a `KrelS` at a caller-chosen
hole `F q A` with `A` UNPINNED (vacuous body at `n = 0`). If the `KrelS` def carried the α-conjunct
(the produced stack is hole-determined), the producer would have to prove it — but it is FALSE on the
produced stack, because a SECOND `krelS_letF_intro` call at a different `A` over the same tail also
produces a relation at the same stack/answer. So the α-conjunct is INCOMPATIBLE with the free-`A`
`letF` producer: adding it shrinks `KrelS` out of the producers' range. -/
theorem alpha_conjunct_shrinks_out_letF_producer :
    -- the two producer calls both land in `KrelS`, at the SAME stack+answer, DIFFERENT holes.
    -- Any def-conjunct forcing hole-determinacy on this stack is therefore unprovable AT the producer.
    (KrelS 0 (CTy.F (0 : Mult) VTy.unit) (CTy.F (0 : Mult) VTy.unit) (⊥ : Eff) 0
        [Frame.letF (Comp.ret Val.vunit), Frame.appF Val.vunit]
        [Frame.letF (Comp.ret Val.vunit), Frame.appF Val.vunit])
    ∧ (KrelS 0 (CTy.F (0 : Mult) VTy.int) (CTy.F (0 : Mult) VTy.unit) (⊥ : Eff) 0
        [Frame.letF (Comp.ret Val.vunit), Frame.appF Val.vunit]
        [Frame.letF (Comp.ret Val.vunit), Frame.appF Val.vunit])
    ∧ ((CTy.F (0 : Mult) VTy.unit : CTy Eff Mult) ≠ CTy.F (0 : Mult) VTy.int) := by
  refine ⟨(letF_relates_at_two_holes (Eff := Eff) (Mult := Mult)).1,
   (letF_relates_at_two_holes (Eff := Eff) (Mult := Mult)).2, ?_⟩
  simp

end Bang.Witness

#print axioms Bang.Witness.alpha_conclusion_conjunct_is_hole_det_on_Si
#print axioms Bang.Witness.alpha_conjunct_shrinks_out_letF_producer
