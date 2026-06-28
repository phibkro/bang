/-
  scratch/CompatRoute1Spike.lean — BUILD-CONFIRMATION of ADR-0058 route 1 (proof-engineer,
  inc5-compat-rekey, 2026-06-28).

  CONTEXT. `CanonicalWallProbe.lean` build-REFUTED route 3 (derive `Canonical` from `KrelS`):
  the frozen-counter design DERIVES the observation counter as `handlerCount K`, so a `handleF`
  pop on `ret` lands at `handlerCount K' + 1` while the tail observation is at `handlerCount K'`.
  The `+1` mismatch is bridged by `run_bump_converges`, which DEMANDS the density guard
  `Canonical K` + `CapsBelow 0 v` — UNSUPPLIABLE from the arbitrary `KrelS`-related stack that
  `CrelK` quantifies over (the wall at `crelK_fund_up`, Compat:1643).

  ADR-0058 route 1: carry the REAL counter `g` instead of deriving it. The machine threads `g`
  MONOTONICALLY — a `handleF` pop keeps `g` (Operational:476 `(g,handleF _ _::K,ret v) ↦ (g,K,ret
  v)`); only MINT (`handle`) increments it. So with a threaded `g`, the pop's two configs share
  the SAME counter and the bridge collapses to `coApproxC_le_reduce` + `ih` — NO density, NO
  `run_bump`, NO `CapsBelow`. This file build-CONFIRMS the two mechanisms the wall needs:

   (A) `pop_route1` — the handleF-pop arm of `crelK_ret` closes WITHOUT any `Canonical`/`CapsBelow`
       guard once `g` is the real (threaded) counter, not `handlerCount K`. This is the exact
       arm CanonicalWallProbe identified as load-bearing for the density guard (Route-4 verdict,
       LR:1869-1908). Route 1 DISSOLVES it. ⇒ the counter-bridge half of the wall is real-g-closed.

   (B) `perform_escape_vacuous` — the OTHER half of Compat:1643's wall: `CapResolves K m ℓ op`
       (the cap resolves in the ARBITRARY observation stack `K`) is NOT a `KrelS` fact. But it
       need not be SUPPLIED — it can be CASE-SPLIT away: when `idDispatch = none` (the cap
       escapes, ADR-0063 defined-escape), `Source.step` is stuck, so the left config never
       converges and `CoApproxC_le` is VACUOUS. So `crelK_fund_up` never needs `CapResolves` as a
       hypothesis; it cases on `splitAtId`/`idDispatch` and the escape branch is free.

  COMBINED VERDICT (build-confirmed below): both halves of the Compat:1643 wall dissolve under
  route 1 + ADR-0063 escapedCap. The frozen `Crel`/Spec.lean signatures are PRESERVED by
  quantifying `g` UNIVERSALLY inside `CrelK` (alongside the already-internal `D`), so `CrelK`'s
  external arity is unchanged — `abbrev Crel := CrelK` stays byte-identical. The remaining
  some-branch dispatch (`krelS_splitAtId_decomp` + resume conjunct) is EXISTING machinery to
  re-key, not new proof.
-/
import Bang.LR

namespace Bang.CompatRoute1Spike
open Bang

variable {Eff Mult : Type} [Lattice Eff] [OrderBot Eff] [CommSemiring Mult]
  [DecidableEq Mult] [EffSig Eff Mult]

/-- **(A) Route-1 pop-bridge.** With the REAL counter `g` threaded (not derived as
`handlerCount K`), a `handleF`-pop on a `ret` closes from the tail observation `ih` by ONE
`coApproxC_le_reduce` — NO `Canonical`, NO `CapsBelow`, NO `run_bump_converges`. Both sides step
`(g, handleF _ _ :: K', ret v) ↦ (g, K', ret v)` keeping `g`, so the reduct counter matches `ih`'s
exactly. This is the load-bearing arm CanonicalWallProbe's Route-4 verdict flagged (LR:1869-1908,
~27 lines of density bridging) collapsed to a single line. -/
theorem pop_route1 {n g nh₁ nh₂ : Nat} {h₁ h₂ : Handler} {K₁' K₂' : Stack} {v₁ v₂ : Val}
    (ih : CoApproxC_le n (g, K₁', Comp.ret v₁) (g, K₂', Comp.ret v₂)) :
    CoApproxC_le n (g, Frame.handleF nh₁ h₁ :: K₁', Comp.ret v₁)
                   (g, Frame.handleF nh₂ h₂ :: K₂', Comp.ret v₂) :=
  coApproxC_le_reduce (cfg₁' := (g, K₁', Comp.ret v₁)) (cfg₂' := (g, K₂', Comp.ret v₂))
    rfl (by intro g' v hc; simp at hc) rfl (by intro g' v hc; simp at hc) ih

/-- **(B) Escape-vacuity.** The other half of the Compat:1643 wall. When the performed capability
ESCAPES the observation stack `K₁` (`idDispatch = none`, ADR-0063 defined-escape), `Source.step`
is stuck, so the left config cannot converge and `CoApproxC_le` holds VACUOUSLY against ANY right
config. So `crelK_fund_up` never needs `CapResolves K₁ m ℓ op` as a hypothesis — it cases on
`idDispatch`, and this branch is discharged with no `KrelS`/density input at all. -/
theorem perform_escape_vacuous {n g : Nat} {K₁ : Stack} {m : Nat} {ℓ : EffectRow.Label} {op : OpId}
    {v₁ : Val} {cfg₂ : Config}
    (hesc : idDispatch K₁ m ℓ op v₁ = none) :
    CoApproxC_le n (g, K₁, Comp.perform (Val.vcap m ℓ) op v₁) cfg₂ := by
  intro hconv
  exact absurd hconv
    (not_convergesC_le_of_stuck
      (by simp only [Source.step, hesc, Option.map_none]) (by intro g' v; simp))

end Bang.CompatRoute1Spike
