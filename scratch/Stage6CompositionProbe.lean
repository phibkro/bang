/-
  scratch/Stage6CompositionProbe.lean — #44 STAGE 6 (soundness composition) DESIGN PROBE.
  Lane s6probe, 2026-07-10. CENSUS-SAFE: outside the `Bang.+` glob, imported by nothing in `Bang/`,
  never in `Bang/Audit.lean` — the trusted-three census is byte-unchanged by this file.

  PURPOSE: state the candidate Stage-6 theorems against the REAL landed definitions and confirm they
  COMPILE (with sorry where a proof is deferred). The design map is docs/notes/stage6-soundness-design.md.

  FINDING (build-grounded, see the map): the ADR-0085 §Staged-plan Stage-6 HEADLINE obligation
  (preservation/progress/type_safety + no_accidental_handling custom cases, gated by `just axioms`)
  is ALREADY DISCHARGED on main — those four are axiom-clean WITH `Handler.custom` present, their
  custom arms folded in as Stages 2-5 landed. So Stage 6 is NOT new frozen theorems; it is (i) two
  small INSTANTIATION lemmas that make the general theorems usable AT a custom handler, and (ii) an
  optional END-TO-END composition COROLLARY. This file states all three and (i) closes clean.
-/
import Bang.Core.Soundness
import Bang.Spec

open Bang

namespace Stage6Probe

variable {Eff : Type} [DecidableEq Eff] [Lattice Eff] [OrderBot Eff]
variable {Mult : Type} [CommSemiring Mult] [DecidableEq Mult]
variable [EffSig Eff Mult]

/-! ### CANDIDATE 1 (the real Stage-6 content) — `custom_handlesWithin`.
The custom analogue of `throws_handlesWithin`: a `custom ℓ p cl` handler is scoped to `ℓ`'s row.
This is what makes `no_accidental_handling` INSTANTIABLE at a custom handler (the frozen theorem is
already general; it needs its `HandlesWithin` premise discharged for the custom form). PROVABLE clean
set_option linter.unusedSectionVars false
— `handlesOp (custom ℓ …) ℓ' op = true` forces `ℓ' = ℓ` by the label-match `&&`, same shape as throws. -/
theorem custom_handlesWithin (ℓ : EffectRow.Label) (p : Val) (cl : List (OpId × Comp)) :
    HandlesWithin (Eff := Eff) (Mult := Mult)
      (EffSig.labelEff (Eff := Eff) (Mult := Mult) ℓ) (Handler.custom ℓ p cl) := by
  intro ℓ' op hcatch
  -- handlesOp (custom ℓ p cl) ℓ' op = (ℓ = ℓ') && (cl.find? …).isSome ; the true forces ℓ = ℓ'.
  simp only [Bang.handlesOp, Bool.and_eq_true, decide_eq_true_eq] at hcatch
  obtain ⟨hℓ, _⟩ := hcatch
  subst hℓ
  exact le_refl _

/-- CANDIDATE 1' — the corollary: a scoped custom handler never catches a FOREIGN op. This is
`no_accidental_handling` INSTANTIATED at the custom form via Candidate 1. Fully clean (rides the
already-clean frozen theorem). This IS "extending no_accidental_handling to user labels" concretely. -/
theorem no_accidental_handling_custom
    {ℓ : EffectRow.Label} {p : Val} {cl : List (OpId × Comp)} {e : Eff}
    (hDisj : _root_.Disjoint (EffSig.labelEff (Eff := Eff) (Mult := Mult) ℓ) e) :
    ∀ ℓ' op, EffSig.labelEff (Eff := Eff) (Mult := Mult) ℓ' ≤ e →
      Bang.handlesOp (Handler.custom ℓ p cl) ℓ' op = false :=
  no_accidental_handling (custom_handlesWithin ℓ p cl) hDisj

/-! ### CANDIDATE 2 — the end-to-end user-effect soundness COROLLARY (optional Stage-6 headline).
Composes Stage-3 typing (`HasCTy` at a fully-discharged row `⊥`) with `type_safety`: a program that
INSTALLS a custom handler and handles its label to ⊥ never runs to `.stuck`. This is a pure corollary
of the frozen `type_safety` (no new arm) — it just witnesses the composition on a custom program. It
needs `HasConfig'` at the initial config; `type_safety` supplies the rest. Stated with sorry for the
`HasConfig'`-from-`HasCTy` packaging (a mechanical lift; the interesting content is already proven). -/
theorem custom_program_safe
    {c : Comp} {q : Mult} {A : VTy Eff Mult}
    (hc : HasCTy (Eff := Eff) (Mult := Mult) [] [] c ⊥ (CTy.F q A)) :
    ∀ fuel, Source.eval fuel c ≠ Result.stuck := by
  -- COMPOSITION: HasCTy [] [] c ⊥ (F q A) ⟹ HasConfig' (0,[],c) ⊥ (F q A) ⟹ type_safety.
  -- The custom fragment is INSIDE `c`; type_safety is constructor-agnostic so it already covers it.
  -- The only gap is the initial-config packaging lemma (HasCTy → HasConfig'), mechanical, not custom.
  sorry

end Stage6Probe

-- AXIOM GATE (the real sorry-signal — reads the proof term, not a text grep):
#print axioms Stage6Probe.custom_handlesWithin
#print axioms Stage6Probe.no_accidental_handling_custom
