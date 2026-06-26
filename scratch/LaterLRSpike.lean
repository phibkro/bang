/-
  scratch/LaterLRSpike.lean — DE-RISKING SPIKE for opt-1 (later/Kripke LR).

  QUESTION (team-lead): does a step-indexed / "later" (▷) modality let the POP arm of
  `wsCfg_step` close for the dead-cap counterexample, staying UNARY, term+type-indexed?

  This file isolates the CORE OBSTRUCTION as a build-checked generic lemma, then the
  prose verdict (bottom) reads the obstruction off it. No concrete `Eff` instance needed —
  the lemma is generic, so it pins the structural fact, not an artifact of one model.
-/
import Bang.Model

namespace Bang.LaterLRSpike
open Bang Bang.Model
open Bang.EffectRow (Label)

variable {Eff Mult : Type} [Lattice Eff] [OrderBot Eff] [CommSemiring Mult] [DecidableEq Mult] [EffSig Eff Mult]

/-- **THE OBSTRUCTION (build-checked).** A `vcap n ℓ` sitting under a thunk whose OWN row is
`labelEff ℓ` is FORCED by `WSV` to resolve in the *current* stack `K` — the `vthunk` ambient-RESET
(`ρ ↦ labelEff ℓ`) does NOT shield it; it re-exposes the cap at exactly its performable row, and the
`vcap` leaf gate (`labelEff ℓ ≤ labelEff ℓ`, true by `le_refl`) then fires unconditionally.

This is the counterexample's deep cap `vthunk (perform (vcap g 1) op _)` (arg type `U (labelEff 1) (F q unit)`).
Holds for ANY outer ambient `ρ` — the OUTER `¬LabelOccurs ℓ A` (the ADR-0057 B-occ premise) is irrelevant,
because the inner thunk's row resets the ambient to `labelEff ℓ` regardless of the outer type. -/
theorem deep_cap_gate_fires {K : EvalCtx} {ρ : Eff} {n : Nat} {ℓ : Label} {op : OpId} {w : Val}
    {q : Mult} {B : VTy Eff Mult}
    (h : WSV K ρ (Val.vthunk (Comp.perform (Val.vcap n ℓ) op w))
          (VTy.U (EffSig.labelEff (Eff := Eff) (Mult := Mult) ℓ) (CTy.F q B))) :
    ResolvesLabel K n ℓ := by
  -- invert the thunk (ambient resets to its own row `labelEff ℓ`)
  cases h with
  | vthunk hbody =>
    -- invert the perform (cap part at the reset ambient `labelEff ℓ`)
    cases hbody with
    | perform hcap _ =>
      -- invert the vcap leaf gate: the obligation is PRESENT-TENSE against `K`
      cases hcap with
      | vcap hgate => exact hgate le_rfl

/-- **WHY ▷-ON-THUNK DOES NOT HELP (build-checked corollary).** A step-indexed reading would weaken
`WSV.vthunk` to `▷ WSC` = `∀ j < k, WSCk j …`. But the POP step does NOT touch this thunk, so it does
NOT decrement the index of the thunk's contents; and the failing obligation is the `vcap` LEAF gate,
which is present-tense at EVERY index `j` (a leaf carries no `▷`). So for every `j < k` the step-indexed
body still yields `ResolvesLabel K n ℓ` against the POPPED stack `K` — exactly the false obligation.

We model "the body holds at index j" by the un-indexed `WSC` (the j-th rung of the ▷ tower has the
SAME leaf gate); `deep_cap_gate_fires` shows that rung alone forces the false `ResolvesLabel`. -/
theorem later_on_thunk_still_forces {K : EvalCtx} {ρ : Eff} {n : Nat} {ℓ : Label} {op : OpId} {w : Val}
    {q : Mult} {B : VTy Eff Mult}
    -- ▷-tower's j-th rung = the body WSC at the reset row, against the SAME (popped) stack K:
    (hrung : WSC K (EffSig.labelEff (Eff := Eff) (Mult := Mult) ℓ)
              (Comp.perform (Val.vcap n ℓ) op w)
              (EffSig.labelEff (Eff := Eff) (Mult := Mult) ℓ) (CTy.F q B)) :
    ResolvesLabel K n ℓ := by
  cases hrung with
  | perform hcap _ => cases hcap with | vcap hgate => exact hgate le_rfl

end Bang.LaterLRSpike
