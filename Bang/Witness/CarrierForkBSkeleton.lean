module

public import Bang.Meta.BinaryLR
public import Bang.Core.Semantics.Invariants

/-! # CarrierForkBSkeleton — the fork-(b) DISCHARGE-CHAIN skeleton: the MINT-site obligation, the
recursive-body re-discharge, and the `lr_fundamental` root discharge, all SHAPE-elaborating.

This is the "type-checked skeleton of the changed def + the hardest site's proof sketch" the probe
contract asks for. It does NOT edit `CrelK`/`KrelS` (the ruling comes first); instead it models the
fork-(b) shape with the REAL kernel `StackBelow`/`WellCounted` objects, showing the three discharge
obligations that a `WellCounted (g,K) = StackBelow g K` premise on `CrelK`'s def would impose all
elaborate from facts already in scope.

## The proposed change (fork b, NOT landed here)

`CrelK n C ε c₁ c₂ := ∀ g D K₁ K₂, StackBelow g K₁ → StackBelow g K₂ → KrelS n C D ε g K₁ K₂ → CoApproxC_le …`
(add the two `StackBelow g` hypotheses; `KrelS` and `KrelS_g_cast` stay BYTE-IDENTICAL — the fork's
whole selling point vs (a)).

## The three obligations and their discharge (all elaborate below)

1. MINT-site: the compat core `intro`s `g K₁ K₂ hsb₁ hsb₂ hK`; the freshly-minted `handleF g` frame
   needs `StackBelow g K₁` — NOW `hsb₁`, directly. (`mint_site_has_freshness`.)
2. recursive-body re-discharge: the compat core applies the body CrelK at `(g+1, handleF g :: K₁)`;
   the premise it now demands is `StackBelow (g+1) (handleF g :: K₁)`, dischargeable from `hsb₁` by
   `StackBelow`-monotonicity + `g < g+1`. (`body_reapply_discharges`.)
3. root discharge: `lr_fundamental` / `crelK_adequacy_nil` consume `CrelK` at `(g:=0, K:=[])`, where
   `StackBelow 0 [] = True`; `lr_sound` at `(g:=handlerCount C, K:=C)` needs `StackBelow (handlerCount
   C) C` — the Q22 seam (held), matching the ADR census. (`root_nil_discharges` + the Q22 note.) -/

namespace Bang.Witness

open Bang
open Bang.EffectRow (Label)

variable {Eff  : Type} [Lattice Eff] [OrderBot Eff]
variable {Mult : Type} [CommSemiring Mult] [DecidableEq Mult]
variable [EffSig Eff Mult]

/-- **Obligation 1 (MINT-site freshness is now a HYPOTHESIS).** After the compat core's
`intro g D K₁ K₂ hsb₁ hsb₂ hK`, the `StackBelow g K₁` the fresh-mint `krelS_handleF_intro` demands
IS `hsb₁` — no `sorry`. (The current code's `have hsbg₁ : StackBelow g K₁ := by sorry` at
`compatK_handleState:1242` becomes `hsb₁`.) -/
theorem mint_site_has_freshness {g : Nat} {K₁ : EvalCtx}
    (hsb₁ : Bang.StackBelow g K₁) : Bang.StackBelow g K₁ := hsb₁

/-- **Obligation 2 (the recursive body re-application discharges by monotonicity).** The compat core
runs the body at the post-MINT `(g+1, handleF g (state ℓ s) :: K₁)`. Under fork-(b)'s `CrelK` the body
demands `StackBelow (g+1) (handleF g h :: K₁)`. From the outer `StackBelow g K₁` (= `hsb₁`) this
elaborates: `g < g+1` and `StackBelow (g+1) K₁` (monotone-lift of `hsb₁`). This is the step that fork
(a) CANNOT do — its `StackBelow g` lives inside `KrelS`, coupled to the non-monotone `KrelS_g_cast`;
here it is a SEPARATE monotone-liftable hypothesis. Uses the real `StackBelow`. -/
theorem body_reapply_discharges {g : Nat} {K₁ : EvalCtx} {h : Handler}
    (hsb₁ : Bang.StackBelow g K₁) :
    Bang.StackBelow (g + 1) (Frame.handleF g h :: K₁) := by
  -- StackBelow (g+1) (handleF g h :: K₁) = (g < g+1) ∧ StackBelow (g+1) K₁
  refine ⟨by omega, ?_⟩
  -- monotone lift of hsb₁ : StackBelow g K₁ ⟹ StackBelow (g+1) K₁
  induction K₁ with
  | nil => trivial
  | cons fr K ih =>
    cases fr with
    | handleF n hd => exact ⟨by have := hsb₁.1; omega, ih hsb₁.2⟩
    | letF N => exact ih hsb₁
    | appF w => exact ih hsb₁

/-- **Obligation 3 (root discharge at the nil observation).** `crelK_adequacy_nil` / `lr_fundamental`
consume `CrelK` at `(g := 0, K := [])`; the fork-(b) premise `StackBelow 0 []` is `True`. So
`lr_fundamental`/`lr_fundamental_closed` discharge cleanly (census 18→20). -/
theorem root_nil_discharges : Bang.StackBelow 0 ([] : EvalCtx) := trivial

/-- **Obligation 3′ (the `lr_sound` root does NOT discharge — the Q22 seam, held).** `lr_sound`
instantiates `CrelK` at `(g := handlerCount C, K := C)` for a `HasStack`-typed source stack `C`; the
premise `StackBelow (handlerCount C) C` is UNPROVABLE from `HasStack` alone (`HasStack.handleF` binds
the frame id FREE — `FreshCarrierDischargeProbe`). So fork (b), like the ADR's (i′), sheds
`lr_fundamental`+`lr_fundamental_closed` (18→20) but NOT `lr_sound` (needs Q22). Recorded as the
do-not-retry `sorry` — the census is UNCHANGED by the fork ruling. -/
theorem lr_sound_root_needs_Q22
    {C : Stack} {e eo : Eff} {B Co : CTy Eff Mult}
    (hC : HasStack C e B eo Co) :
    Bang.StackBelow (Bang.handlerCount C) C := by
  -- HasStack.handleF binds `nh` free — no density premise. This IS the Q22 reshape seam. HELD.
  sorry

end Bang.Witness

#print axioms Bang.Witness.mint_site_has_freshness
#print axioms Bang.Witness.body_reapply_discharges
#print axioms Bang.Witness.root_nil_discharges
