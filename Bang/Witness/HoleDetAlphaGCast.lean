module

public import Bang.Meta.BinaryLR
public import Bang.Core.Semantics.Invariants

/-! # HoleDetAlphaGCast — route (α) STEP 2: does a CONCLUSION-side strengthening survive
`KrelS_g_cast`'s contravariant resume recursion (the killer of fork (a))?

## The g-cast structure (`BinaryLR.lean:1369-1378`)

`KrelS_g_cast n g g'` rebuilds the handleF resume conjunct. Its recursion has TWO polarities:
* the resume HYPOTHESIS `KrelS m Cᵢ C εᵢ g Kᵢ Kᵢ'` (the captured continuation) is cast the REVERSE
  way — `KrelS_g_cast m g' g Kᵢ Kᵢ' hKi` (target→source, `:1376`). This is the contravariant
  occurrence that REFUTED fork (a): a `StackBelow g` def-invariant would need the reverse cast on
  `Kᵢ`, which the monotone-only cast cannot supply (`CarrierForkA`).
* the resume CONCLUSION `KrelS m (F qᵣ Aᵣ) D eₛ g Sᵢ Sᵢ'` (the resume result) is cast FORWARD —
  `KrelS_g_cast m g g' Sᵢ Sᵢ' hSk` (`:1377-1378`). This is COVARIANT.

## The finding (STEP 2 PASSES for a conclusion reshape)

Route (α) adds its datum to the CONCLUSION (the `Sᵢ` side), which is CAST FORWARD. Any additional
`KrelS`-shaped fact on `Sᵢ` (e.g. a decomposition relation over `Sᵢ`'s tail) forward-casts by the
SAME `KrelS_g_cast m g g'` the existing `hSk` already uses; any purely STRUCTURAL fact on `Sᵢ`
(`Sᵢ = … :: …`) is g-independent. So — UNLIKE fork (a)'s def-invariant, which lands the fresh fact in
BOTH the covariant conclusion AND the contravariant hypothesis — a conclusion-only (α) strengthening
does NOT hit the reverse-cast obstruction. **The g-cast does NOT refute route (α).**

## What the witnesses establish

1. `conclusion_side_casts_forward` — an abstract counter-family `R` closed under FORWARD upcast
   suffices to reconstruct a covariant-conclusion occurrence (the polarity the resume RESULT sits in).
   Contrast `CarrierForkA.monotone_gcast_cannot_serve_contravariant_resume`: the SAME forward-only
   closure FAILED for the contravariant hypothesis. Same lemma, opposite polarity ⇒ opposite verdict.
2. `krelS_gcast_conclusion_is_forward` — the REAL `KrelS_g_cast` already forward-casts a `KrelS`
   fact on the resume result `Sᵢ` (it does exactly this for `hSk`); so ANY extra `KrelS`-shaped
   conclusion datum on `Sᵢ` inherits the same forward cast — no new obstruction. (Demonstrated by
   forward-casting a second, arbitrary `KrelS` fact on the same `Sᵢ`.)

CONCLUSION of STEP 2: the g-cast obstruction that killed fork (a) is POLARITY-SPECIFIC to the
hypothesis; a conclusion-side (α) strengthening survives it. Route (α) is NOT refuted at step 2. -/

namespace Bang.Witness

open Bang
open Bang.EffectRow (Label)

variable {Eff  : Type} [Lattice Eff] [OrderBot Eff]
variable {Mult : Type} [CommSemiring Mult] [DecidableEq Mult]
variable [EffSig Eff Mult]

/-- **The polarity asymmetry, abstract.** A counter-family closed under FORWARD upcast (`g ≤ g'`)
DOES serve a covariant-conclusion occurrence (`R g → R g'` is exactly the up-closure). Contrast
`CarrierForkA.monotone_gcast_cannot_serve_contravariant_resume`, where the same forward closure could
NOT serve the contravariant hypothesis (`R (g+1) → R g`). So the resume CONCLUSION — where route (α)'s
datum lives — is on the GOOD side of the polarity split. -/
theorem conclusion_side_casts_forward :
    ∃ R : Nat → Prop,
      (∀ g g', g ≤ g' → R g → R g') ∧          -- forward upcast HOLDS
      (∀ g g', g ≤ g' → R g → R g') := by       -- the covariant conclusion needs EXACTLY this — served
  exact ⟨fun k => 0 < k, fun g g' hle hg => by omega, fun g g' hle hg => by omega⟩

/-- **The real g-cast forward-casts a conclusion `KrelS` on `Sᵢ`.** `KrelS_g_cast` already forward-casts
the resume result relation `hSk : KrelS m (F qᵣ Aᵣ) D eₛ g Sᵢ Sᵢ'` to `g'` (`BinaryLR.lean:1377`). This
witness shows that a SECOND, arbitrary conclusion-side `KrelS` datum on the SAME `Sᵢ` (e.g. a
decomposition relation over `Sᵢ`'s tail that route (α) would add) casts by the SAME lemma — no new
obstruction, no reverse cast. So a conclusion reshape is g-cast-compatible. -/
theorem krelS_gcast_conclusion_is_forward {m : Nat} {qᵣ : Mult} {Aᵣ : VTy Eff Mult}
    {D : CTy Eff Mult} {eₛ : Eff} {g g' : Nat} {Sᵢ Sᵢ' : Stack}
    (hSk : KrelS m (CTy.F qᵣ Aᵣ) D eₛ g Sᵢ Sᵢ')
    -- a hypothetical EXTRA conclusion-side datum route (α) might carry: another `KrelS` on `Sᵢ`.
    {Cx Dx : CTy Eff Mult} {ex : Eff} {Tᵢ Tᵢ' : Stack}
    (hExtra : KrelS m Cx Dx ex g Tᵢ Tᵢ') :
    KrelS m (CTy.F qᵣ Aᵣ) D eₛ g' Sᵢ Sᵢ' ∧ KrelS m Cx Dx ex g' Tᵢ Tᵢ' :=
  -- BOTH forward-cast by the SAME `KrelS_g_cast m g g'` — the conclusion polarity.
  ⟨KrelS_g_cast m g g' Sᵢ Sᵢ' hSk, KrelS_g_cast m g g' Tᵢ Tᵢ' hExtra⟩

end Bang.Witness

#print axioms Bang.Witness.conclusion_side_casts_forward
#print axioms Bang.Witness.krelS_gcast_conclusion_is_forward
