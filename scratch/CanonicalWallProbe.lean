/-
  scratch/CanonicalWallProbe.lean — BUILD-CONFIRMATION of the inc-5 endgame verdict
  (proof-engineer, inc5-endgame, 2026-06-26).

  QUESTION (lead): closing `crelK_fund`'s `ret` case needs `crelK_ret`, whose guard is
  `Canonical K₁ K₂` (dense ids) + `CapsBelow 0 v`. Is `Canonical K₁ K₂` DERIVABLE from the
  KrelS hypothesis (and the B-occ-strengthened HasCTy) at the use site?  → ROUTE 3.

  VERDICT (build-confirmed below): NO. Two facts:
   (1) `Canonical`'s density constraint genuinely bites — a `handleF` whose id ≥ handlerCount
       is NOT Canonical (`density_bites`).
   (2) The `ret`-case obligation `crelK_ret D K₁ K₂ hK …` leaves EXACTLY `Canonical K₁/K₂`
       + `CapsBelow 0 v₁/v₂` as residual goals, suppliable ONLY from `hK : KrelS …`
       (`ret_obligation_shape`).
  And `KrelS`'s handleF clause (`krelS_handleF`, LR.lean) forces `nh₁ = nh₂` with NO `nh <
  handlerCount` bound — so a KrelS-related stack `[handleF 5 (throws ℓ)]` (handlerCount 1) is
  KrelS-self-relatable yet not Canonical. KrelS ⊉ Canonical; B-occ (answer-type label-freedom)
  is orthogonal to id-density. ⇒ ROUTE 3 FAILS.

  ROUTE 4 (is the guard over-strong?) is ALSO refuted by source: `crelK_ret`'s handleF-pop case
  (LR.lean:1869-1895) consumes `hcan` via `Canonical.capsBelow → run_bump_converges` to bridge the
  `+1` counter-shift of the pop. Removing the guard breaks that case. The density is load-bearing.

  ⇒ STOP-and-SHOW: closing the binary LR needs route 1 (CrelK quantifies over Canonical stacks —
  FROZEN Crel/Spec.lean change, ADR + STATEMENT_CHANGE_OK) or route 2 (Canonical-reachability).
-/
import Bang.LR

namespace Bang.CanonicalWallProbe
open Bang Bang.RunPlugReshape

variable {Eff Mult : Type} [Lattice Eff] [OrderBot Eff] [CommSemiring Mult]
  [DecidableEq Mult] [EffSig Eff Mult]

/-- (1) `Canonical`'s density bites: id 5 on a 1-handler stack is NOT dense (`5 < 1` is false). -/
theorem density_bites (ℓ : EffectRow.Label) :
    ¬ Canonical [Frame.handleF 5 (Handler.throws ℓ)] := by
  simp [Canonical, Frame.CapsBelow, handlerCount]

/-- (2) The exact `ret`-case obligation. `crelK_ret` discharges `CoApproxC_le …` but leaves
`Canonical K₁`, `Canonical K₂`, `CapsBelow 0 v₁`, `CapsBelow 0 v₂` — suppliable ONLY from
`hK : KrelS …` (the CrelK quantifier gives arbitrary related stacks). KrelS forces `nh₁=nh₂`
only (see `krelS_handleF`), NOT density ⇒ these 4 goals are the unsuppliable wall. -/
theorem ret_obligation_shape {n : Nat} {q : Mult} {A : VTy Eff Mult} {e : Eff} {D : CTy Eff Mult}
    {K₁ K₂ : Stack} {v₁ v₂ : Val}
    (hK : KrelS n (CTy.F q A) D e K₁ K₂)
    (hc₁ : Val.Closed v₁) (hc₂ : Val.Closed v₂) (hv : VrelK n A v₁ v₂) :
    CoApproxC_le n (handlerCount K₁, K₁, Comp.ret v₁) (handlerCount K₂, K₂, Comp.ret v₂) := by
  refine crelK_ret D K₁ K₂ hK ?canon₁ ?canon₂ ?caps₁ ?caps₂ hc₁ hc₂ hv
  -- ↓ the four residual goals: Canonical K₁ · Canonical K₂ · CapsBelow 0 v₁ · CapsBelow 0 v₂.
  -- NONE is derivable from hK/hc/hv — this `sorry` cluster IS the documented wall (route 3 verdict).
  case canon₁ => sorry
  case canon₂ => sorry
  case caps₁ => sorry
  case caps₂ => sorry

end Bang.CanonicalWallProbe
