/-
  Spec.lean
  ─────────────────────────────────────────────────────────────────────────
  The contract for bang-lang's graded-CBPV metatheory and its lowering to
  WebAssembly typed stack-switching (WasmFX / the stack-switching proposal).

  This file IS the PRD. The theorem *statements* are the acceptance criteria;
  every `sorry` is a backlog item; the `sorry` count is the burndown chart.
  Because statements are checked against the definitions, the spec cannot
  drift from the implementation.

  GAP (one paragraph): Graded CBPV with effects and coeffects is already
  mechanized (Torczon et al., OOPSLA 2024, Coq; FSCD 2025 metatheory). What is
  NOT done is a verified lowering from a graded-CBPV source to typed
  continuations: compiling the F-returner's effect grade to WasmFX
  suspend/resume handlers, discharging the coeffect grade by erasure, with a
  machine-checked simulation. That path is the contribution.

  RISK TAGS:
    [STD]   standard; failure means a definition is wrong, not the design
    [KEY]   the actual contribution; novelty lives here
    [RISKY] most likely to expose a bad design choice — PROVE THESE FIRST

  This will NOT typecheck as-is. Replace every `opaque`/stub with your real
  AST and judgments (your existing K2/K3 interpreters, CalcReify machinery).
-/

namespace Bang

/-! ## 0. Grade algebras

Following Torczon et al. (OOPSLA 2024, §1): the effect grade indexes the
**thunk** `U_φ B` (the latent effect of the suspended computation, surfaced
when forced), and the multiplicity / coeffect grade indexes the **returner**
`F_q A` (the consumer-side usage budget on the produced value).

This matches the only existing mechanized graded CBPV (plclub/cbpv-effects-coeffects).
Cross-check our Lean defs against their Coq when in doubt. -/

-- Effect grades index the thunk `U φ B`.  `+` = choice, `·` = sequencing,
-- (optionally `*` = iteration; swap in `KleeneAlgebra` if you want star).
-- Ordered for sub-effecting (φ' ≤ φ — a more permissive thunk type is a
-- supertype of a more restricted one).
variable {Eff  : Type} [OrderedSemiring Eff]
-- Multiplicity / coeffect grades index the returner `F q A`.  QTT-style {0,1,ω}.
-- Ordered for sub-usaging; `0` is the erasable grade.
-- Also annotates context bindings `x :_ρ A` as the consumer's usage budget.
variable {Mult : Type} [OrderedSemiring Mult]

/-! ## 0.5 Effect-row well-formedness — the discipline that keeps rows SET-shaped

bang-lang's rows are idempotent `Finset`s, so they sit in the disjoint/set
fragment (Biernacki §5.4; Links / Hillerström–Lindley) where the ρ-maps vanish.
But "set-shaped" is NOT automatic under row polymorphism: instantiating `α` in
`∀α. ⟨l | α⟩` with a row containing `l` would let a handler for `l` ACCIDENTALLY
capture an operation smuggled in through `α` — i.e. loss of abstraction-safety.
The fix, and the precise thing that LICENSES dropping the ρ-maps, is a "lacks"
constraint on row variables, enforced at instantiation. Phase A must build this
rule, or it will be forced to rebuild the duplicate-effect machinery to stay
sound. -/

opaque Disjoint : Eff → Eff → Prop          -- rows share no effect; Finset model: ∩ = ∅
opaque RowAll   : (Eff → CTy) → Eff → CTy    -- `∀(α # L). B`, carrying lacks-set L
opaque WfInst   : CTy → Eff → CTy → Prop     -- well-formed row instantiation

-- [INV] the load-bearing typing side-condition: α may be instantiated with `ε`
-- only when `ε` lacks the constraint set `L`.
theorem rowinst_requires_disjoint {q : Eff → CTy} {L ε : Eff} :
    WfInst (RowAll q L) ε (q ε) → Disjoint ε L := sorry

-- [INV][KEY] abstraction-safety / NO accidental handling: under the lacks
-- discipline, a handler for `l` never intercepts an `l` introduced through a row
-- variable. THIS invariant is what makes the ρ-map-free (set) model SOUND — it
-- is the obligation taken on in exchange for the simpler metatheory.
opaque HandlesIntended : Eff → Comp → Handler → Prop
theorem no_accidental_handling {Γ : Ctx} {l e : Eff} {A : VTy}
    {body : Comp} {h : Handler} :
    Disjoint l e →                              -- `l` fresh w.r.t. the tail `e`
    HasCTy Γ body (l * e) (F (l * e) A) →
    HandlesIntended l body h := sorry

/-! ## 1. Syntax + judgments (stubs — replace with your real inductives) -/

opaque VTy  : Type
opaque CTy  : Type
opaque Val  : Type
opaque Comp : Type
opaque Var  : Type

-- polarity-crossing constructors (Torczon §1)
opaque U : Eff  → CTy → VTy     -- thunk, graded by latent effect φ (forced ⇒ effects ⊆ φ)
opaque F : Mult → VTy → CTy     -- returner, graded by consumer-usage budget q on the result

opaque Ctx        : Type
opaque emptyCtx   : Ctx
opaque Ctx.bind   : Var → Mult → VTy → Ctx → Ctx
opaque Ctx.scale  : Mult → Ctx → Ctx          -- ρ · Γ
opaque Ctx.add    : Ctx → Ctx → Ctx           -- Γ₁ + Γ₂  (resource split)

-- values are inert (no effect); computations carry an effect grade `e`
opaque HasVTy : Ctx → Val → VTy → Prop
opaque HasCTy : Ctx → Comp → Eff → CTy → Prop

/-! ## 2. Operational semantics (fuel-indexed — matches CalcReify) -/

inductive Result (α : Type) | done (v : α) | oom | stuck
opaque Source.step      : Comp → Option Comp
opaque Source.eval      : Nat → Comp → Result Val
opaque Source.evalTrace : Nat → Comp → Result (Val × Trace)
opaque Trace            : Type
opaque traceWithin      : Trace → Eff → Prop     -- observed trace ∈ static grade
opaque isReturn         : Comp → Prop
opaque NotEvaluated     : Var → Comp → Prop

/-! ## 3. Core syntactic metatheory -/

-- [STD] Value substitution; grades compose multiplicatively. CBPV's value-only
-- substitution invariant relocates the QTT budget-split to the U-comonad
-- axiom, so this is total — no σ∈{0,1} restriction needed.
theorem subst_value (ρ : Mult) {Γ Δ : Ctx} {v : Val} {A : VTy}
    {c : Comp} {e : Eff} {B : CTy} :
    HasVTy Δ v A →
    HasCTy (Ctx.add Γ (Ctx.scale ρ Δ)) c e B →
    HasCTy (Ctx.add Γ (Ctx.scale ρ Δ)) c e B    -- ⟵ on `[v/x] c`
    := sorry

-- [STD] Preservation: a step preserves type and does not raise the grade.
theorem preservation {Γ : Ctx} {c c' : Comp} {e : Eff} {B : CTy} :
    HasCTy Γ c e B → Source.step c = some c' →
    ∃ e', e' ≤ e ∧ HasCTy Γ c' e' B := sorry

-- [STD] Progress.
theorem progress {c : Comp} {e : Eff} {B : CTy} :
    HasCTy emptyCtx c e B → isReturn c ∨ ∃ c', Source.step c = some c' := sorry

-- [STD] Safety = progress + preservation, lifted to fuel-indexed eval.
theorem type_safety {c : Comp} {e : Eff} {A : VTy} :
    HasCTy emptyCtx c e (F e A) → ∀ fuel, Source.eval fuel c ≠ Result.stuck
    := sorry

/-! ## 4. Grade soundness (the QTT payoff) -/

-- [KEY] Coeffect erasure: a 0-graded variable is never evaluated. The
-- operational content of "0 = erased but contemplatable". Cashes out in §6.
theorem zero_usage_erasable {Γ : Ctx} {x : Var} {A : VTy}
    {c : Comp} {e : Eff} {B : CTy} :
    HasCTy (Ctx.bind x (0 : Mult) A Γ) c e B → NotEvaluated x c := sorry

-- [KEY] Effect soundness: static grade `e` over-approximates every observed
-- trace. Graded-monad soundness for `F e`.
theorem effect_sound {c : Comp} {e : Eff} {A : VTy} {fuel : Nat}
    {v : Val} {t : Trace} :
    HasCTy emptyCtx c e (F e A) →
    Source.evalTrace fuel c = Result.done (v, t) →
    traceWithin t e := sorry

/-! ## 5. Observational equivalence — `≈` IS PINNED HERE (do not redefine) -/

-- extra term stubs used below
opaque ret     : Val → Comp
opaque seqComp : Comp → Comp → Comp    -- c₁ ; c₂
opaque idComp  : Comp
opaque recover : Comp → Comp
opaque Cxt      : Type                 -- computation-to-computation contexts
opaque Cxt.plug : Cxt → Comp → Comp

-- Observation: fuel-bounded convergence to a returned value.
def Converges (c : Comp) : Prop := ∃ fuel v, Source.eval fuel c = Result.done v

-- THE SPEC NOTION. Contextual approximation (`⊑`) and equivalence (`≈`).
def ctxApprox (c₁ c₂ : Comp) : Prop :=
  ∀ C : Cxt, Converges (Cxt.plug C c₁) → Converges (Cxt.plug C c₂)
def ctxEquiv (c₁ c₂ : Comp) : Prop := ctxApprox c₁ c₂ ∧ ctxApprox c₂ c₁
-- (rename/scope these if they clash with Mathlib order notation)
infixl:50 " ⊑ " => ctxApprox
infixl:50 " ≈ " => ctxEquiv

-- THE PROOF VEHICLE — now TRANSCRIBED from the actual definitions in Biernacki
-- et al. 2018 "Handle with Care" (Figs 6–9), adapted from their CBV λ^H/L to our
-- CBPV substrate, crossed with Benton–Hur biorthogonality + Katsumata ⊤⊤.
-- Coq source to cross-check: bitbucket.org/pl-uwr/aleff-logrel (IxFree/COFE).
--
-- CORRECTION vs the earlier draft: there is NO `HandlesOnly` predicate. The
-- effect side is (a) the row denotation as control-stuck "simple expressions"
-- (`Srel`, their 𝒮) plus (b) a freeness side-condition. The context relation
-- tests against BOTH related return-values AND related control-stuck ops — that
-- second half is the capstone (their §3.2 / Fig 7).
--
-- bang-lang SIMPLIFICATION (their §5.4): the `ρ`-maps + `lift ↑` exist ONLY to
-- distinguish duplicate effects (⟨l,l⟩ ≠ ⟨l⟩). bang-lang's rows are idempotent
-- `Finset`s — the disjoint/set fragment — so the freeness maps vanish and the
-- row is interpreted as a plain set. We drop ρ and `n-free`. (Restore iff you
-- ever make ⟨l,l⟩ ≠ ⟨l⟩.)

-- Observation = termination to a returned value (their `Obs`, approximation
-- form; the paper guards it with ▷ and counts steps only on the left).
def CoApprox (c₁ c₂ : Comp) : Prop := Converges c₁ → Converges c₂

opaque Stack       : Type                  -- CBPV stacks = their eval contexts E
opaque Stack.plug  : Stack → Comp → Comp
opaque BaseRel     : VTy → Val → Val → Prop
opaque thunk       : Comp → Val
opaque asThunk     : VTy → Option (Mult × CTy)
opaque asReturner  : CTy → Option (Eff × VTy)
-- a control-stuck computation: operation in row `e` applied to a value, in
-- evaluation position, unhandled by the enclosing stack (inner context E' and
-- freeness elided — trivial for set-rows; see Coq Fig 7).
opaque raise       : Eff → Val → Comp
opaque opArgTy     : Eff → VTy             -- Σ(op) argument type
opaque opResTy     : Eff → VTy             -- Σ(op) result type = output relation μ

mutual
  -- VALUE relation (their ⟦τ⟧, Fig 6).
  -- THUNK clause (Torczon U_φ): two thunks are related iff forcing them
  -- produces Crel-related computations at the inner CTy. The static grade `φ`
  -- bounds the effects of those forced bodies (see effect_sound) — relatedness
  -- itself is the same shape as their Fig 6's λV.U clause.
  def Vrel : Nat → VTy → Val → Val → Prop
    | n, A, v₁, v₂ =>
      match asThunk A with
      | some (_φ, B) =>
          ∀ m, m < n → ∀ c₁ c₂, v₁ = thunk c₁ → v₂ = thunk c₂ → Crel m B c₁ c₂
      | none => BaseRel A v₁ v₂

  -- SIMPLE-EXPRESSION relation (their 𝒮, Fig 7 + row denotation Fig 8).
  -- A control-stuck pair is related at `F e A` iff: same operation in row `e`,
  -- ▷-related arguments, and every ▷-related pair of OUTPUT results (the μ
  -- relation), resumed into the stacks, co-converges.
  def Srel : Nat → Eff → Stack → Stack → Comp → Comp → Prop
    | n, e, S₁, S₂, c₁, c₂ =>
      ∃ a₁ a₂, c₁ = raise e a₁ ∧ c₂ = raise e a₂
        ∧ (∀ m, m < n → Vrel m (opArgTy e) a₁ a₂)                      -- ▷ args
        ∧ (∀ m, m < n → ∀ r₁ r₂, Vrel m (opResTy e) r₁ r₂ →            -- ▷ output μ
             CoApprox (Stack.plug S₁ (ret r₁)) (Stack.plug S₂ (ret r₂)))

  -- STACK relation (their 𝒦, Fig 7). TWO obligations: agree on related RETURN
  -- values AND on related control-stuck OPERATIONS (the 𝒮 half).
  --
  -- NOTE on the Torczon-aligned grading: the returner now carries the coeffect
  -- `q` (consumer budget). The effect axis (`e` below) is the *running effect*
  -- of stacks built around U_φ-typed thunks — derived from the typing judgment,
  -- not the F annotation. `q = 0` is the F-erasure clause: stacks may discard
  -- the value entirely (relates anything). Captured via asReturner returning
  -- the coeffect q and inner A; the effect side is supplied by Srel's row.
  def Krel : Nat → CTy → Stack → Stack → Prop
    | n, B, S₁, S₂ =>
      match asReturner B with
      | some (q, A) =>
          if q = 0 then True   -- F_0 erasure: any consumer-stack works
          else
            (∀ m, m ≤ n → ∀ v₁ v₂, Vrel m A v₁ v₂ →
                CoApprox (Stack.plug S₁ (ret v₁)) (Stack.plug S₂ (ret v₂)))
            ∧ (∀ m e₀, m ≤ n → ∀ c₁ c₂, Srel m e₀ S₁ S₂ c₁ c₂ →
                CoApprox (Stack.plug S₁ c₁) (Stack.plug S₂ c₂))
      | none => BaseStackRel n B S₁ S₂

  -- COMPUTATION relation = biorthogonal ⊤⊤-closure over related stacks
  -- (their ℰ, Fig 7; Benton–Hur; = ⊤⊤-lift of `Vrel` through `F e`).
  def Crel : Nat → CTy → Comp → Comp → Prop
    | n, B, c₁, c₂ =>
      ∀ S₁ S₂, Krel n B S₁ S₂ → CoApprox (Stack.plug S₁ c₁) (Stack.plug S₂ c₂)
end
-- decreasing_by: well-founded on (n, sizeOf type); every "▷" call is at m < n.
-- This is their COFE guardedness (the `▷` later modality), automated by IxFree
-- in Coq; in Lean either thread the index explicitly or port an IxFree-style ▷.

opaque BaseStackRel : Nat → CTy → Stack → Stack → Prop  -- function-type stacks etc.

-- [RISKY] Soundness: the LR implies contextual approximation. The bridge that
-- licenses using the LR at all. PROVE THIS FIRST — nothing downstream is
-- legitimate without it. With biorthogonality this is near-free (Galois
-- connection): adequacy of `Converges` w.r.t. plugging gives `Crel ⊆ ⊑`.
theorem lr_sound {c₁ c₂ : Comp} {B : CTy} :
    (∀ n, Crel n B c₁ c₂) → c₁ ⊑ c₂ := sorry

-- [KEY] Fundamental theorem ("parametricity"): every well-typed computation is
-- related to itself at every index. The workhorse; most equivalences are
-- corollaries of this plus per-constructor compatibility lemmas.
theorem lr_fundamental {Γ : Ctx} {c : Comp} {e : Eff} {B : CTy} :
    HasCTy Γ c e B → ∀ n, Crel n B c c := sorry

/-! ## 6. Recovery algebra — the Trinity, stated against `≈` -/

-- [KEY] monoid ⇒ ret is a unit for sequencing.
theorem seq_unit (v : Val) {c : Comp} : seqComp (ret v) c ≈ c := sorry

-- [RISKY] group (invertible) effects ⇒ recovery rolls back: `c ; recover c ≈ id`.
-- NOT fresh ground. This is the *invertible* (groupoid, f† = f⁻¹) special case of
-- Heunen–Karvonen: effectful computations are reversible IFF the monad is
-- dagger-Frobenius. The genuinely open part is the BRIDGE:
--     E a group  ⇒?  the graded monad `F` (with respect to effects on `U_φ`)
--     is dagger-Frobenius.
-- If the bridge holds, this theorem is a corollary. If not, the Frobenius law
-- must be added as an explicit hypothesis (= the "observability side-condition").
-- SETTLE THE BRIDGE FIRST — it decides whether this is mechanical or research.
--
-- NOTE (Torczon grading): under our convention effects live on `U_φ` (thunks),
-- not on `F`. So the "invertibility" in question is about composing latent
-- thunk-effects, not about a Mult-graded returner. The Heunen–Karvonen story
-- is about effect-side invertibility (still applies). The coeffect side
-- (Mult on F) has its own erasure story (`F_0`) but no obvious group analogue.
-- See ADR-0018 Trinity table — the recovery axis is the *effect* axis.
theorem group_recovers [AddGroup Eff] {c : Comp} :
    seqComp c (recover c) ≈ idComp := sorry

/-! ## 7. WasmFX target + compilation correctness (the unclaimed ground) -/

opaque Wasmfx.Module    : Type
opaque Wasmfx.Val       : Type
opaque Wasmfx.Ty        : Type
opaque Wasmfx.run       : Nat → Wasmfx.Module → Result Wasmfx.Val
opaque Wasmfx.WellTyped : Wasmfx.Module → Prop
opaque Wasmfx.MentionsLocal : Wasmfx.Module → Var → Prop
opaque Handler          : Type
opaque HandlerLawful    : Handler → Prop
opaque Wasmfx.HandlerEquiv : Wasmfx.Module → Handler → Prop
opaque compileC       : Comp → Wasmfx.Module
opaque compileV       : Val  → Wasmfx.Val
opaque compileHandler : Handler → Wasmfx.Module

-- [KEY] Type preservation under translation. Effect grade ↦ handler tags;
-- multiplicity grade erases (compile-time only).
theorem compile_well_typed {c : Comp} {e : Eff} {A : VTy} :
    HasCTy emptyCtx c e (F e A) → Wasmfx.WellTyped (compileC c) := sorry

-- [KEY][RISKY] Forward simulation, fuel-indexed (NOT coinduction — matches
-- CalcReify). Source converges ⇒ compiled module converges to the translated
-- value. The heart of the contribution.
theorem compile_forward_sim {c : Comp} {v : Val} {fuel : Nat} :
    Source.eval fuel c = Result.done v →
    ∃ fuel', Wasmfx.run fuel' (compileC c) = Result.done (compileV v) := sorry

-- [KEY] Handler ↦ suspend/resume: a lawful algebraic-effect handler compiles
-- to a WasmFX suspend-handler on a typed continuation, preserving semantics.
-- The Plotkin–Pretnar ↔ WasmFX bridge.
theorem handler_compiles {h : Handler} :
    HandlerLawful h → Wasmfx.HandlerEquiv (compileHandler h) h := sorry

-- [KEY] Erasure is observable in the output: a 0-graded binder emits no code.
-- "0 = erased" cashed out in the target — the concrete payoff of grading.
theorem zero_grade_no_code {Γ : Ctx} {x : Var} {A : VTy}
    {c : Comp} {e : Eff} {B : CTy} :
    HasCTy (Ctx.bind x (0 : Mult) A Γ) c e B →
    ¬ Wasmfx.MentionsLocal (compileC c) x := sorry

end Bang
