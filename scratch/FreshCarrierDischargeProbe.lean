import Bang.Meta.BinaryLR
import Bang.Core.Semantics.Invariants

/-! # FreshCarrierDischargeProbe — lane lrfresh (task #35), the design-consult viability probe.

QUESTION: for the three carrier shapes (i)/(iii) that put a `StackBelow g K` well-formedness
fact on the LR (either as a `KrelS` def-invariant conjunct or a threaded side judgment), CAN the
`krelS_refl` instantiation in `lr_sound` (`Spec.lean:236`) DISCHARGE it?

`lr_sound` instantiates the biorthogonal closure at `g := handlerCount C` for a `HasStack`-typed
observation stack `C` (`Spec.lean:248`). So any def-invariant carrier forces `krelS_refl` to prove
`StackBelow (handlerCount C) C` FROM `HasStack C e B eo (F qo Ao)` alone.

FINDING (code-read, NOT yet machine-checked — build in flight): `HasStack.handleF` (`Typing.lean:378`)
binds the frame id `n` as a FREE variable with NO density/bound premise (no `n < handlerCount`, no
`WellCounted`). A source-level observation context is NOT reached by a fresh machine run, so its ids
are arbitrary. Therefore `StackBelow (handlerCount C) C` is NOT derivable from `HasStack` — this is
the SAME density obligation ADR-0058 route-1 deleted (`Canonical`/`CapsBelow`), reappearing at the
`lr_sound` boundary. The carrier that closes item-1 (the SKIP relocation, which needs `nid ∉ cfg₁.1`
for a config reached by a REAL machine run, where `StackBelow` DOES hold via `wellCounted_reachable`)
does not automatically discharge at the `lr_sound` `handlerCount`-instantiation — that is the Q22
reshape seam (`Spec.lean:252`), a SEPARATE residual.

CONSEQUENCE for the ADR: the carrier closes `lr_fundamental`/`lr_fundamental_closed` (which route
ONLY through `crelK_fund` → `crelK_fund_up`, where the config is machine-reached and `StackBelow`
holds); it does NOT by itself close `lr_sound`, which ALSO carries the Q22 bridge. Census win from
the carrier alone is 18→20, not 18→21. `lr_sound`'s third shed needs Q22 co-resolved.

This file is a PROSE-COMMENTED probe (no live claim compiled — the build is mid-fetch on this lane's
clone). The `sorry` below marks the obligation the def-invariant shape imposes on `krelS_refl`, kept
as the do-not-retry witness that it is NOT free from `HasStack`. -/

namespace Bang
open Bang.EffectRow (Label)
variable {Eff  : Type} [Lattice Eff] [OrderBot Eff]
variable {Mult : Type} [CommSemiring Mult] [DecidableEq Mult]
variable [EffSig Eff Mult]

/-- The obligation a def-invariant / side-judgment carrier imposes on `krelS_refl`: for a source
observation stack `C`, prove `StackBelow (handlerCount C) C`. UNPROVABLE from `HasStack` alone —
`HasStack.handleF` binds `n` free (Typing.lean:378), no density premise. This is the Q22 reshape
seam, distinct from item-1's machine-reached config. -/
theorem stackBelow_handlerCount_of_hasStack_REFUTED
    {C : Stack} {e eo : Eff} {B Co : CTy Eff Mult}
    (hC : HasStack C e B eo Co) :
    Bang.StackBelow (Bang.handlerCount C) C := by
  -- `HasStack.handleF` gives no `n < handlerCount C` — the frame id is arbitrary. Not derivable.
  sorry

end Bang
