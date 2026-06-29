/-
  scratch/AdequacySpike.lean — DE-RISK the lr_sound reshape↔observation bridge (proof-engineer,
  inc5-spec-repoint, 2026-06-29).

  QUESTION (lead): close `lr_sound` over the inc-5 `converges_plug_iff` (reshaped RHS) + the
  route-1 `CrelK` (raw-focus observation `(g, K, c)`). The brief proposes a bridge lemma:
    CrelK n B e c₁ c₂ → CoApproxC_le n (handlerCount C, canonStack C c₁, capSubstInto C c₁) (… c₂)
  built on krelS_refl + run_plug_reshape + a canonStack-KrelS-self fact.

  This file build-tests whether that bridge typechecks / closes.

  VERDICT (build-confirmed below):
  - `adequacy_bridge_attempt1` — the brief's instantiation (CrelK at g := handlerCount C,
    K := canonStack C cᵢ) TYPE-MISMATCHES: CrelK observes the RAW focus cᵢ, the goal needs the
    cap-substituted `capSubstInto C cᵢ`. Held as a `sorry` (the mismatch is the residual).
  - `adequacy_bridge_attempt2` — the bridge CLOSES (EXIT 0) IFF `capSubstInto C cᵢ = cᵢ`. So the
    ENTIRE gap is that focus equation.
  - `capSubstInto C cᵢ = cᵢ` holds ⟺ cᵢ does not reference C's cap binders ⟺ cᵢ does NOT perform
    C's effects — i.e. it EXCLUDES exactly the effectful case (the whole point of contextual
    approximation). So the bridge is UNPROVABLE from CrelK alone for effectful cᵢ.

  ROOT CAUSE: route-1 CrelK (ADR-0058) observes the RAW focus `(g, K, c)`; the inc-5 statement-fix to
  `converges_plug_iff` (correctly) observes the CAP-SUBSTITUTED reshaped focus `capSubstInto C c`. These
  were aligned under the OLD (false) `converges_plug_iff` RHS `(handlerCount C, C, c)`; the fix broke the
  alignment and no CrelK instantiation can restore it (the observed focus is structurally fixed to the raw
  c parameter). ARCHITECTURAL — the labelling-vs-closure cap-rep seam (OPEN_QUESTIONS Q22). → orchestrator.
-/
import Bang.Compat

namespace Bang
open Bang.EffectRow (Label)
open Bang.RunPlugReshape

variable {Eff  : Type} [Lattice Eff] [OrderBot Eff]
variable {Mult : Type} [CommSemiring Mult] [DecidableEq Mult]
variable [EffSig Eff Mult]

/-- ATTEMPT 1: the brief's bridge, instantiating CrelK at g := handlerCount C, K := canonStack C cᵢ.
The focus that CrelK observes is RAW cᵢ; the goal config's focus is `capSubstInto C cᵢ`. -/
theorem adequacy_bridge_attempt1 {n : Nat} {C : EvalCtx} {e eo : Eff} {B Co : CTy Eff Mult}
    {qo : Mult} {Ao : VTy Eff Mult} {c₁ c₂ : Comp}
    (hCo : Co = CTy.F qo Ao) (hC : HasStack C e B eo Co)
    (hself : KrelS n B Co e (handlerCount C) (canonStack C c₁) (canonStack C c₂))
    (h : CrelK n B e c₁ c₂) :
    CoApproxC_le n (handlerCount C, canonStack C c₁, capSubstInto C c₁)
                   (handlerCount C, canonStack C c₂, capSubstInto C c₂) := by
  rw [CrelK] at h
  have hobs := h (handlerCount C) Co (canonStack C c₁) (canonStack C c₂) hself
  -- hobs : CoApproxC_le n (handlerCount C, canonStack C c₁, c₁) (handlerCount C, canonStack C c₂, c₂)
  -- GOAL  : CoApproxC_le n (handlerCount C, canonStack C c₁, capSubstInto C c₁) (…, capSubstInto C c₂)
  -- Focus MISMATCH: hobs has raw cᵢ, goal has capSubstInto C cᵢ. BUILD-CONFIRMED type mismatch:
  --   has    CoApproxC_le n (handlerCount C, canonStack C c₁, c₁) (…, c₂)
  --   expected CoApproxC_le n (handlerCount C, canonStack C c₁, capSubstInto C c₁) (…, capSubstInto C c₂)
  sorry

/-- ATTEMPT 2: the bridge closes IFF `capSubstInto C cᵢ = cᵢ` (the focus mismatch is the ONLY gap).
This isolates the obstruction to exactly that equation. -/
theorem adequacy_bridge_attempt2 {n : Nat} {C : EvalCtx} {e eo : Eff} {B Co : CTy Eff Mult}
    {qo : Mult} {Ao : VTy Eff Mult} {c₁ c₂ : Comp}
    (hsub1 : capSubstInto C c₁ = c₁) (hsub2 : capSubstInto C c₂ = c₂)
    (hself : KrelS n B Co e (handlerCount C) (canonStack C c₁) (canonStack C c₂))
    (h : CrelK n B e c₁ c₂) :
    CoApproxC_le n (handlerCount C, canonStack C c₁, capSubstInto C c₁)
                   (handlerCount C, canonStack C c₂, capSubstInto C c₂) := by
  rw [hsub1, hsub2, CrelK] at *
  exact h (handlerCount C) Co (canonStack C c₁) (canonStack C c₂) hself

/-- PROBE: is `capSubstInto C c = c` derivable, and under what condition? Test the simplest:
a single `handleF` frame context substitutes a `vcap` into the focus at de Bruijn 0, so for a
focus that USES index 0 it is NOT identity. Concrete witness below. -/
example : True := trivial

end Bang
