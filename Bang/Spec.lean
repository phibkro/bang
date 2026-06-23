/-
  Bang/Spec.lean — THE PRD.
  ──────────────────────────────────────────────────────────────────────
  Re-exports all submodules; carries every frozen theorem STATEMENT.
  Each module owns its DEFINITIONS; this file owns the CLAIMS.

  Module layout:
    Bang.Core         types (Val, Comp, Handler, VTy, CTy, GradeVec, TyCtx, Frame)
    Bang.Syntax       q_or_1, HasVTy/HasCTy (resource-enforcing), row well-formedness
    Bang.Operational  subst, Source.step/eval, Trace, isReturn
    Bang.LR           Stack, BaseRel, Vrel/Srel/Krel/Crel, NotEvaluated, recovery helpers
    Bang.Compile      Wasmfx.* + compileC/compileV/compileHandler
    Bang.Spec         (this file) — re-exports + frozen theorem statements

  THE THEOREMS ARE THE ACCEPTANCE CRITERIA. Every `sorry` is a backlog item;
  the `sorry` count is the burndown chart (`bash tools/burndown.sh`).
  See also `Bang/Audit.lean` for #print axioms per theorem.

  STATUS (Phase A part 2 in progress):
    - Module split landed
    - Spec.lean axioms 44 → 37 (subst, Ctx, isReturn, HasVTy, HasCTy,
      Source.step/eval all concrete in their modules)
    - Theorem statements still all `sorry` (Phase B targets)
    - See `docs/notes/OPEN_QUESTIONS.md` for deferred design decisions
-/

import Bang.Core
import Bang.Syntax
import Bang.Operational
import Bang.LR
import Bang.Compile
import Bang.Metatheory

namespace Bang

variable {Eff  : Type} [Lattice Eff] [OrderBot Eff]
variable {Mult : Type} [CommSemiring Mult] [DecidableEq Mult]
variable [EffSig Eff Mult]


/-! ## 0.5 Effect-row well-formedness theorems -/

-- [INV] the load-bearing typing side-condition. WfInst carries the lacks-constraint
-- (ADR-0024 D3); the theorem projects out the disjointness it requires.
theorem rowinst_requires_disjoint
    {q : Eff → CTy Eff Mult} {L ε : Eff} :
    WfInst q L ε → Disjoint ε L := rowinst_requires_disjoint_proof

-- [INV][KEY] abstraction-safety / NO accidental handling — the invariant that
-- licenses dropping ρ-maps (ADR-0018). Origin: zhang-popl19 "accidental handling".
-- Restated faithfully (ADR-0024 D2): the old ∀-`h` form was vacuous. A handler
-- SCOPED to row `l` (`HandlesWithin l h`) never catches a FOREIGN operation (label
-- in a disjoint row `e`) — foreign ops tunnel to an outer handler. Correct-by-
-- construction in the label-indexed CK machine (ADR-0023): `handlesOp` matches the
-- label exactly, so a handler cannot catch a label it does not name.
theorem no_accidental_handling
    {l e : Eff} {h : Handler} :
    HandlesWithin (Eff := Eff) (Mult := Mult) l h → Disjoint l e →
    ∀ ℓ' op, EffSig.labelEff (Eff := Eff) (Mult := Mult) ℓ' ≤ e → handlesOp h ℓ' op = false
    := no_accidental_handling_proof


/-! ## 3. Core syntactic metatheory -/

-- [STD] Graded value substitution (de Bruijn — ADR-0020).
-- Shape: a value `v` typed in `Γ` at grade `γ_v`, substituted for the binder at
-- index 0 (graded at multiplicity `ρ` in `c`), yields `c[v]` typed in
-- `γ + ρ·γ_v` — Torczon's `T_App` arithmetic `γ₁ Q+ q Q* γ₂`
-- (resource/CBPV/typing.v), over the positional grade-vec + ambient TyCtx.
--   shape: torczon-oopsla24-effects-coeffects §graded-subst
-- ALL FIVE NAMED SIDE-CONDITIONS ARE GONE (ADR-0020):
--   the cons `ρ :: γ` structurally pins the bound var's grade and shadows
--   positionally; `Γ` lookup is positional (`get?`), so no no-dup-keys; subst is
--   capture-avoiding by construction (shift under binders), so no closedness.
--   `γ` and `γ_v` are both length `Γ.length`, so `+` (zipWith) is well-defined.
theorem subst_value
    (ρ : Mult) {γ γ_v : GradeVec Mult} {Γ : TyCtx Eff Mult}
    {v : Val} {A : VTy Eff Mult}
    {c : Comp} {e : Eff} {B : CTy Eff Mult} :
    HasVTy γ_v Γ v A →
    HasCTy (ρ :: γ) (A :: Γ) c e B →
    HasCTy (γ + ρ • γ_v) Γ (Comp.subst v c) e B
    := subst_value_proof ρ

-- [STD] Preservation (ADR-0023, config-level). A machine transition preserves the
-- whole-program type `Co`; the running effect `eo` may only shrink (it shrinks at
-- the REDUCE-handleF/ret and DISPATCH transitions, where a handler discharges its
-- label). Stated over `HasConfig` (focus typing + stack typing) because the CK
-- machine's state is a config, not a bare term (the substitution `Source.step` no
-- longer exists).
theorem preservation
    {cfg cfg' : Config} {eo : Eff} {Co : CTy Eff Mult} :
    HasConfig cfg eo Co → Source.step cfg = some cfg' →
    ∃ eo', eo' ≤ eo ∧ HasConfig cfg' eo' Co := preservation_proof

-- [STD] Progress (ADR-0023, config-level). A config typed at whole-program effect
-- `⊥` (fully handled) and returner type `F q A` is either a returned config
-- `⟨[], ret v⟩` or it steps. Genuinely true for effectful programs now: a
-- `⟨K, up ℓ op v⟩` at `⊥` always has a handling frame in `K` (the label must be
-- discharged up the stack — `labelEff ℓ ≰ ⊥` — and op-partiality forces that
-- handler to catch `op`), so DISPATCH fires.
theorem progress
    {cfg : Config} {q : Mult} {A : VTy Eff Mult} :
    HasConfig cfg ⊥ (CTy.F q A) →
    isReturnConfig cfg ∨ ∃ cfg', Source.step cfg = some cfg' := progress_proof

-- [STD] Safety = progress + preservation, fuel-lifted. Frozen statement (ADR-0023
-- D3): `Source.eval`'s signature is unchanged (load ⟨[], c⟩, run, unload). The
-- proof bridges through the config-level progress/preservation. At `⊥`:
-- preservation gives `eo' ≤ ⊥`, so `eo' = ⊥` re-establishes the fuel IH.
theorem type_safety
    {c : Comp} {q : Mult} {A : VTy Eff Mult} :
    HasCTy [] [] c ⊥ (CTy.F q A) → ∀ fuel, Source.eval fuel c ≠ Result.stuck
    := type_safety_proof


/-! ## 4. Grade soundness (the QTT payoff) -/

-- [KEY] Coeffect erasure: a 0-graded binder (index 0) is never evaluated.
theorem zero_usage_erasable
    {γ : GradeVec Mult} {Γ : TyCtx Eff Mult} {A : VTy Eff Mult}
    {c : Comp} {e : Eff} {B : CTy Eff Mult} :
    HasCTy ((0 : Mult) :: γ) (A :: Γ) c e B →
    NotEvaluated 0 c := by
  intro _hc v₁ v₂
  -- GOAL (NotEvaluated unfolded): `Comp.substFrom 0 v₁ c ≈ Comp.substFrom 0 v₂ c`.
  -- This is Torczon's grade-0 COEFFECT ERASURE (`semtyping.v`): a binder typed at grade `0` cannot
  -- influence observable behaviour, so any two fillers give `≈`-equal computations. It is genuinely
  -- SEMANTIC — a 0-graded var is still substituted syntactically (`ret (vvar 0)` type-checks at
  -- returner grade `q = 0`), so there is no structural / syntactic-non-occurrence shortcut (verified:
  -- both the "syntactic non-occurrence" and "syntactic subst-independence" readings are refuted by
  -- `ret (vvar 0)` at `q = 0`). The proof routes through the logical relation:
  --   BLOCKER: needs `lr_fundamental` (PROOF_ORDER #1, still `sorry`) — instantiate `Crel`/`Vrel` at
  --   the grade-0 slot to get observational irrelevance of the filler (Torczon proves erasure as a
  --   corollary of the fundamental property, `semtyping.v`). With `lr_sound`+`lr_fundamental` closed,
  --   this becomes: derive `Crel n B e (subst v₁ c) (subst v₂ c)` for all `n` from `_hc` (the 0-slot
  --   makes the `Vrel`-relatedness of `v₁,v₂` irrelevant), then `lr_sound` gives `⊑` both ways = `≈`.
  -- Leaving the single `sorry` here (theorem body only) per discipline; the def `NotEvaluated` is
  -- axiom-free (the `NotEvaluated` axiom is REMOVED — it is now a real `def` in `Bang/LR.lean`).
  sorry

-- [KEY] Effect soundness: static grade `e` over-approximates every observed trace.
theorem effect_sound
    {c : Comp} {e : Eff} {q : Mult} {A : VTy Eff Mult} {fuel : Nat}
    {v : Val} {t : Trace} :
    HasCTy [] [] c e (CTy.F q A) →
    Source.evalTrace fuel c = Result.done (v, t) →
    traceWithin t e := sorry


/-! ## 5. Logical relation theorems -/

-- [RISKY] Soundness: LR implies contextual approximation. PROVE THIS FIRST
-- in Phase B (PROOF_ORDER #1).
theorem lr_sound
    {c₁ c₂ : Comp} {e : Eff} {B : CTy Eff Mult} :
    (∀ n, Crel n B e c₁ c₂) → c₁ ⊑ c₂ := sorry

-- [KEY] Fundamental theorem.
theorem lr_fundamental
    {γ : GradeVec Mult} {Γ : TyCtx Eff Mult}
    {c : Comp} {e : Eff} {B : CTy Eff Mult} :
    HasCTy γ Γ c e B → ∀ n, Crel n B e c c := sorry


/-! ## 6. Recovery algebra (ADR-0018, amended by ADR-0032) -/

-- [KEY] monoid ⇒ ret is a unit for sequencing.
theorem seq_unit (v : Val) {c : Comp} : seqComp (Comp.ret v) c ≈ c := seq_unit_proof v

-- `group_recovers` RETIRED (ADR-0032, supersedes ADR-0018's "group ⇒ rollback" row).
-- The law `[AddGroup Eff] → seqComp c (recover c) ≈ idComp` was FALSE as a plain `≈`
-- (refutable: a diverging `c` makes `(c;ret()) ≉ ret()`), vacuous for the real effect
-- lattice (no `AddGroup` instance — rows are an idempotent join-semilattice), and
-- redundant: v1 rollback is a HANDLER mechanism, proven by `all_or_nothing_abort`
-- (ADR-0030/0031, axiom-clean `84e3ab3`), NOT an effect-algebra inverse.


/-! ## 7. WasmFX compilation correctness (the contribution) -/

-- [KEY] Type preservation under translation.
theorem compile_well_typed
    {c : Comp} {e : Eff} {q : Mult} {A : VTy Eff Mult} :
    HasCTy [] [] c e (CTy.F q A) → Wasmfx.WellTyped (compileC c) := sorry

-- [KEY][RISKY] Forward simulation — the heart of the contribution.
theorem compile_forward_sim {c : Comp} {v : Val} {fuel : Nat} :
    Source.eval fuel c = Result.done v →
    ∃ fuel', Wasmfx.run fuel' (compileC c) = Result.done (compileV v) := sorry

-- [KEY] Handler ↦ suspend/resume.
theorem handler_compiles {h : Handler} :
    HandlerLawful h → Wasmfx.HandlerEquiv (compileHandler h) h := sorry

-- [KEY] Erasure observable in output: 0-graded binder (index 0) emits no code.
theorem zero_grade_no_code
    {γ : GradeVec Mult} {Γ : TyCtx Eff Mult} {A : VTy Eff Mult}
    {c : Comp} {e : Eff} {B : CTy Eff Mult} :
    HasCTy ((0 : Mult) :: γ) (A :: Γ) c e B →
    ¬ Wasmfx.MentionsLocal (compileC c) 0 := sorry

end Bang
