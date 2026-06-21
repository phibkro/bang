/-
  Bang/Spec.lean — THE PRD.
  ──────────────────────────────────────────────────────────────────────
  Re-exports all submodules; carries every frozen theorem STATEMENT.
  Each module owns its DEFINITIONS; this file owns the CLAIMS.

  Module layout:
    Bang.Core         types (Val, Comp, Handler, VTy, CTy, Ctx, Frame)
    Bang.Syntax       Ctx.scale/add, HasVTy/HasCTy, row well-formedness
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

namespace Bang

variable {Eff  : Type} [Lattice Eff] [OrderBot Eff]
variable {Mult : Type} [Semiring Mult] [DecidableEq Mult]


/-! ## 0.5 Effect-row well-formedness theorems -/

-- [INV] the load-bearing typing side-condition.
theorem rowinst_requires_disjoint
    {q : Eff → CTy Eff Mult} {L ε : Eff} :
    WfInst (RowAll q L) ε (q ε) → Disjoint ε L := sorry

-- [INV][KEY] abstraction-safety / NO accidental handling — the invariant
-- that licenses dropping ρ-maps. See ADR-0018.
theorem no_accidental_handling
    {Γ : Ctx Eff Mult} {l e : Eff} {A : VTy Eff Mult} {q : Mult}
    {body : Comp} {h : Handler} :
    Disjoint l e →
    HasCTy Γ body (l ⊔ e) (CTy.F q A) →
    HandlesIntended l body h := sorry


/-! ## 3. Core syntactic metatheory -/

-- [STD] Value substitution; grades compose multiplicatively.
-- Conclusion should read `[v/x] c` once subst is wired into the statement.
theorem subst_value
    (ρ : Mult) {Γ Δ : Ctx Eff Mult} {v : Val} {A : VTy Eff Mult}
    {c : Comp} {e : Eff} {B : CTy Eff Mult} :
    HasVTy Δ v A →
    HasCTy (Ctx.add Γ (Ctx.scale ρ Δ)) c e B →
    HasCTy (Ctx.add Γ (Ctx.scale ρ Δ)) c e B
    := sorry

-- [STD] Preservation.
theorem preservation
    {Γ : Ctx Eff Mult} {c c' : Comp} {e : Eff} {B : CTy Eff Mult} :
    HasCTy Γ c e B → Source.step c = some c' →
    ∃ e', e' ≤ e ∧ HasCTy Γ c' e' B := sorry

-- [STD] Progress.
theorem progress
    {c : Comp} {e : Eff} {B : CTy Eff Mult} :
    HasCTy Ctx.empty c e B → isReturn c ∨ ∃ c', Source.step c = some c' := sorry

-- [STD] Safety = progress + preservation, fuel-lifted.
theorem type_safety
    {c : Comp} {e : Eff} {q : Mult} {A : VTy Eff Mult} :
    HasCTy Ctx.empty c e (CTy.F q A) → ∀ fuel, Source.eval fuel c ≠ Result.stuck
    := sorry


/-! ## 4. Grade soundness (the QTT payoff) -/

-- [KEY] Coeffect erasure: a 0-graded variable is never evaluated.
theorem zero_usage_erasable
    {Γ : Ctx Eff Mult} {x : Var} {A : VTy Eff Mult}
    {c : Comp} {e : Eff} {B : CTy Eff Mult} :
    HasCTy (Ctx.bind x (0 : Mult) A Γ) c e B → NotEvaluated x c := sorry

-- [KEY] Effect soundness: static grade `e` over-approximates every observed trace.
theorem effect_sound
    {c : Comp} {e : Eff} {q : Mult} {A : VTy Eff Mult} {fuel : Nat}
    {v : Val} {t : Trace} :
    HasCTy Ctx.empty c e (CTy.F q A) →
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
    {Γ : Ctx Eff Mult} {c : Comp} {e : Eff} {B : CTy Eff Mult} :
    HasCTy Γ c e B → ∀ n, Crel n B c c := sorry


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
    HasCTy Ctx.empty c e (CTy.F q A) → Wasmfx.WellTyped (compileC c) := sorry

-- [KEY][RISKY] Forward simulation — the heart of the contribution.
theorem compile_forward_sim {c : Comp} {v : Val} {fuel : Nat} :
    Source.eval fuel c = Result.done v →
    ∃ fuel', Wasmfx.run fuel' (compileC c) = Result.done (compileV v) := sorry

-- [KEY] Handler ↦ suspend/resume.
theorem handler_compiles {h : Handler} :
    HandlerLawful h → Wasmfx.HandlerEquiv (compileHandler h) h := sorry

-- [KEY] Erasure observable in output: 0-graded binder emits no code.
theorem zero_grade_no_code
    {Γ : Ctx Eff Mult} {x : Var} {A : VTy Eff Mult}
    {c : Comp} {e : Eff} {B : CTy Eff Mult} :
    HasCTy (Ctx.bind x (0 : Mult) A Γ) c e B →
    ¬ Wasmfx.MentionsLocal (compileC c) x := sorry

end Bang
