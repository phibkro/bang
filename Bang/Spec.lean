/-
  Bang/Spec.lean — THE PRD.
  ──────────────────────────────────────────────────────────────────────
  Re-exports all submodules; carries every frozen theorem STATEMENT.
  Each module owns its DEFINITIONS; this file owns the CLAIMS.

  Module layout:
    Bang.Core         types (Val, Comp, Handler, VTy, CTy, GradeVec, TyCtx, Frame)
    Bang.Syntax       q_or_1, HasVTy/HasCTy (resource-enforcing), row well-formedness
    Bang.Operational  subst, Source.step/eval, Trace, isReturn, NotEvaluated
    Bang.LR           Stack, BaseRel, Vrel/Srel/Krel/Crel, recovery helpers
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


/-! ## 0.5 Effect-row well-formedness theorems -/

-- [INV] the load-bearing typing side-condition.
theorem rowinst_requires_disjoint
    {q : Eff → CTy Eff Mult} {L ε : Eff} :
    WfInst (RowAll q L) ε (q ε) → Disjoint ε L := sorry

-- [INV][KEY] abstraction-safety / NO accidental handling — the invariant
-- that licenses dropping ρ-maps. See ADR-0018.
-- Property origin: zhang-popl19-abstraction-safe-tunneling coined "accidental
-- handling"; their operational *tunneling* guarantee is what our structural
-- lacks-constraint (Disjoint l e) formulation discharges.
theorem no_accidental_handling
    {γ : GradeVec Mult} {Γ : TyCtx Eff Mult}
    {l e : Eff} {A : VTy Eff Mult} {q : Mult}
    {body : Comp} {h : Handler} :
    Disjoint l e →
    HasCTy γ Γ body (l ⊔ e) (CTy.F q A) →
    HandlesIntended l body h := sorry


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

-- [STD] Preservation.
theorem preservation
    {γ : GradeVec Mult} {Γ : TyCtx Eff Mult}
    {c c' : Comp} {e : Eff} {B : CTy Eff Mult} :
    HasCTy γ Γ c e B → Source.step c = some c' →
    ∃ e', e' ≤ e ∧ HasCTy γ Γ c' e' B := preservation_proof

-- [STD] Progress. Closed (empty context ⇒ empty grade vector). Stated at a
-- returner type `F q A` (ADR-0021, C4): at `arr` type a bare `lam` is a normal
-- form that is neither `ret` nor a step, so general `B` is false; `F q A` is also
-- exactly what `type_safety` consumes.
theorem progress
    {c : Comp} {e : Eff} {q : Mult} {A : VTy Eff Mult} :
    HasCTy [] [] c e (CTy.F q A) → isReturn c ∨ ∃ c', Source.step c = some c' := progress_proof

-- [STD] Safety = progress + preservation, fuel-lifted.
theorem type_safety
    {c : Comp} {e : Eff} {q : Mult} {A : VTy Eff Mult} :
    HasCTy [] [] c e (CTy.F q A) → ∀ fuel, Source.eval fuel c ≠ Result.stuck
    := type_safety_proof


/-! ## 4. Grade soundness (the QTT payoff) -/

-- [KEY] Coeffect erasure: a 0-graded binder (index 0) is never evaluated.
theorem zero_usage_erasable
    {γ : GradeVec Mult} {Γ : TyCtx Eff Mult} {A : VTy Eff Mult}
    {c : Comp} {e : Eff} {B : CTy Eff Mult} :
    HasCTy ((0 : Mult) :: γ) (A :: Γ) c e B →
    NotEvaluated 0 c := sorry

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
    {c₁ c₂ : Comp} {B : CTy Eff Mult} :
    (∀ n, Crel n B c₁ c₂) → c₁ ⊑ c₂ := sorry

-- [KEY] Fundamental theorem.
theorem lr_fundamental
    {γ : GradeVec Mult} {Γ : TyCtx Eff Mult}
    {c : Comp} {e : Eff} {B : CTy Eff Mult} :
    HasCTy γ Γ c e B → ∀ n, Crel n B c c := sorry


/-! ## 6. Recovery algebra — the Trinity (ADR-0018) -/

-- [KEY] monoid ⇒ ret is a unit for sequencing.
theorem seq_unit (v : Val) {c : Comp} : seqComp (Comp.ret v) c ≈ c := sorry

-- [RISKY] group (invertible) effects ⇒ recovery rolls back.
-- See `docs/notes/OPEN_QUESTIONS.md` Q8 for the H-K bridge.
theorem group_recovers
    [AddGroup Eff] {c : Comp} :
    seqComp c (recover c) ≈ idComp := sorry


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
