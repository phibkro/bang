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
import Bang.Compat   -- the fundamental-theorem proofs (sibling to Metatheory); wired to the
                     -- frozen `lr_fundamental`/`lr_sound` statements below via `:= …_proof`

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
    -- ◊4.5b (g): `NotEvaluated` reduces to `≈` (typed-context `ctxEquiv`), so its `Eff`/`Mult` params are
    -- not inferrable from `(0, c)` (both untyped). Pin them to the in-scope `Eff`/`Mult`; the focus type
    -- `{e B}` inside `NotEvaluated` stays universally quantified (erasure holds at every observation type).
    NotEvaluated (Eff := Eff) (Mult := Mult) 0 c := by
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

-- [RISKY] Soundness: LR implies contextual approximation. PROOF_ORDER #1.
--   STATUS (U5): the CLOSED fragment is DONE and axiom-clean — `LR.lr_sound_closed`
--   proves `(∀ n, Crel n B e c₁ c₂) → (Converges c₁ → Converges c₂)` (the `⊑` clause
--   at the EMPTY context `C = []`), via `LR.krel_nil_succ` (the empty stack is
--   `Krel`-self-related at successor indices). What remains for FULL `⊑` over arbitrary
--   `C : Cxt`: `Krel n B e C C` for every evaluation context `C` ("Krel-reflexivity" /
--   identity extension). That is the FUNDAMENTAL-THEOREM direction — both halves of
--   `Krel C C` (related values / related stuck-ops plugged into `C` co-converge) are
--   context-CONGRUENCE, which `Crel` alone does not give (the `letF N :: C'` induction
--   case blocks on `N[v₁] ~ N[v₂]` needing `Crel`-relatedness from `Vrel v₁ v₂`). Hence
--   `lr_sound` and `lr_fundamental` are coupled (PROOF_ORDER #1 groups them): close
--   `lr_fundamental` (→ `Krel`-reflexivity as its identity instance), then
--   `lr_sound = lr_sound_closed ∘ (congruence of the observation context)`.
--   ◊4.5 (ADR-0039): full `lr_sound` over arbitrary `C` consumes `krel_refl`, whose handler-frame +
--   μ-return cases sit in the deferred iso-recursive-▷ subsystem (needs IxFree ∀k≤n Kripke-monotone
--   Crel/Krel/Srel — plain-Nat phrasing lacks the both-ways monotonicity; build-confirmed). The CLOSED
--   fragment (`lr_sound_closed`, F-typed) is DONE; the arbitrary-`C` closure is ◊4.5.
-- [KEY] Soundness: the LR implies contextual approximation. PROOF_ORDER #1. ◊4.5b (g): CLOSED via
-- `lr_sound_closed ∘ krelS_refl` over the now-TYPED `⊑` (the observation context restricted to those
-- `HasStack`-typed at the focus `(e, B)` — ADR decision (a), the standard contextual-equivalence
-- quantifier; the untyped form was a DEFECT under which `lr_sound` is FALSE). The proof: the typed `⊑`
-- hands us `hStack : HasStack C e B eo (F qo Ao)` for the observation context; `krelS_refl` turns it into
-- the IDENTITY EXTENSION `KrelS fuel B (F qo Ao) e C C`; `Crel = CrelK`'s biorthogonal closure then
-- co-converges the two configs at the witnessing fuel (the `lr_sound_closed` adequacy strip, generalized
-- from `C = []` to the typed `C`). Traces to `sorryAx` SOLELY via `krelS_refl`'s state/txn arms = the
-- `krelS_append` + ▷-metering research crux — NO introduced non-append sorry.
--   shape: benton-hur-icfp09 biorthogonal adequacy; pitts-step-indexed; ahmed-esop06 identity extension.
theorem lr_sound
    {c₁ c₂ : Comp} {e : Eff} {B : CTy Eff Mult} :
    (∀ n, Crel n B e c₁ c₂) → ctxApprox (e := e) (B := B) c₁ c₂ := by
  intro hCrel C eo qo Ao hStack hconv
  -- typed `⊑`: `C` is `HasStack`-typed at the focus `(e, B)`, answer type `F qo Ao` (returner, ADR-0038).
  -- Refocus both observations to the config level (`converges_plug_iff`).
  rw [Cxt.plug, converges_plug_iff] at hconv
  rw [Cxt.plug, converges_plug_iff]
  obtain ⟨fuel, w, hfuel⟩ := hconv
  -- instantiate the biorthogonal closure `Crel = CrelK` at the witnessing fuel, observation context (C,C),
  -- answer type `F qo Ao`. The self-relation `KrelS fuel B (F qo Ao) e C C` is `krelS_refl hStack`.
  have hC := hCrel fuel
  rw [show (Crel fuel B e c₁ c₂) = CrelK fuel B e c₁ c₂ from rfl, CrelK] at hC
  exact hC (CTy.F qo Ao) C C (krelS_refl (n := fuel) rfl hStack) ⟨w, hfuel⟩

-- [KEY] Fundamental theorem (ADR-0034: env-closed Biernacki form). A well-typed OPEN computation
-- relates to ITSELF under every pair of `Vrel`-related closing substitution environments. The bare
-- `c c` / arbitrary-Γ form (the Phase-A stub) was UNDER-SPECIFIED — false for open `c` (a free
-- `vvar i` is not `Vrel`-related to itself), and unusable as the induction invariant (the proof
-- descends under binders into open sub-terms). The faithful statement closes `c` over related
-- environments `δ₁,δ₂` (`EnvRel`, `closeC` in `Bang/LR.lean §5.2b`). The closed (`Γ=[]`) instance
-- that `lr_sound`/the capstone consume is the named corollary `lr_fundamental_closed` below.
--   shape: biernacki-popl18 §5.2 (`G⟦Γ⟧η` fundamental theorem); ahmed-esop06 closing substitution.
-- ◊4.5b (g): WIRED to `Bang.crelK_fund` (Compat.lean §B.5′, the ANSWER-TYPED fundamental theorem; the
-- frozen `Crel`/`EnvRel` names abbreviate `CrelK`/`EnvRelK`, so the statement is byte-identical and the
-- proof term typechecks definitionally). PARTIAL: `crelK_fund` carries documented `sorry`s ONLY in the
-- state/transaction producer arms (the `krelS_append` + ▷-metering research crux); THROWS closes
-- end-to-end. So `lr_fundamental` carries `sorryAx` tracing solely to that one crux until it resolves.
theorem lr_fundamental
    {γ : GradeVec Mult} {Γ : TyCtx Eff Mult}
    {c : Comp} {e : Eff} {B : CTy Eff Mult} :
    HasCTy γ Γ c e B →
    ∀ n (δ₁ δ₂ : List Val), EnvRel n Γ δ₁ δ₂ → Crel n B e (closeC δ₁ c) (closeC δ₂ c) :=
  fun h => crelK_fund h

-- [KEY] The CLOSED (`Γ=[]`) corollary — the instance `lr_sound`/`krel_refl`/the capstone consume.
-- Empty environments (`EnvRel n [] [] []` holds; `closeC [] c = c`), so this is `lr_fundamental`
-- specialized to `δ₁=δ₂=[]`. "The fundamental theorem" as closed-program adequacy uses it.
theorem lr_fundamental_closed
    {γ : GradeVec Mult} {c : Comp} {e : Eff} {B : CTy Eff Mult} :
    HasCTy γ ([] : TyCtx Eff Mult) c e B → ∀ n, Crel n B e c c := by
  intro hc n
  have h := lr_fundamental hc n [] [] (by simp [EnvRel])
  simpa using h


/-! ## 6. Recovery algebra (ADR-0018, amended by ADR-0032) -/

-- [KEY] monoid ⇒ ret is a unit for sequencing.
-- ◊4.5b (g): `≈` now carries an implicit focus type `{e B}` (the typed-context restriction). The
-- left-unit law holds at EVERY focus type (the head reduction is typing-independent), so `{e B}` are
-- universally quantified here and threaded explicitly into `ctxEquiv` (the bare notation cannot elaborate
-- a free focus type — `Comp` is untyped). NOT a statement weakening: the proposition is the left-unit law
-- at an arbitrary observation type, which is strictly the standard reading.
theorem seq_unit (v : Val) {c : Comp} {e : Eff} {B : CTy Eff Mult} :
    ctxEquiv (e := e) (B := B) (seqComp (Comp.ret v) c) c := seq_unit_proof v

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
