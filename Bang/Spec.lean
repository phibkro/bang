/-
  Spec.lean
  ─────────────────────────────────────────────────────────────────────────
  The contract for bang-lang's graded-CBPV metatheory and its lowering to
  WebAssembly typed stack-switching (WasmFX).

  This file IS the PRD. The theorem *statements* are the acceptance criteria;
  every `sorry` is a backlog item; the `sorry` count is the burndown chart.

  STATUS (Phase A part 1, 2026-06-21):
    - §1 syntactic types CONCRETE (Val · Comp · Handler · VTy · CTy · Frame · EvalCtx)
    - §1 typing judgments + Ctx resource ops still OPAQUE (Phase A part 2)
    - §2 Source.step + Source.eval still OPAQUE (Phase A part 2; small-step + eval-ctx
      per ADR-0016 + the operational-shape decision; Lexa-style frames)
    - §5 LR is defined; uses opaque BaseRel / asThunk / asReturner (Phase B)
    - All theorems carry `sorry` (Phase B)

  GAP (one paragraph): Graded CBPV with effects and coeffects is mechanized
  (Torczon et al., OOPSLA 2024, Coq). What is NOT done is verified lowering
  from a graded-CBPV source to typed continuations: compiling the U-thunk's
  effect grade to WasmFX suspend/resume handlers, discharging the F-returner's
  coeffect grade by erasure, with a machine-checked simulation. The contribution.

  RISK TAGS:
    [STD]   standard; failure means a definition is wrong, not the design
    [KEY]   the actual contribution; novelty lives here
    [RISKY] most likely to expose a bad design choice — PROVE THESE FIRST
-/

import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Finset.Basic
import Bang.EffectRow

namespace Bang

open Bang.EffectRow (Label)

/-! ## 0. Grade algebras

Following Torczon et al. (OOPSLA 2024, §1):
- the **effect** grade indexes the **thunk** `U_φ B` (latent effect of the
  suspended computation, surfaced when forced),
- the **multiplicity / coeffect** grade indexes the **returner** `F_q A`
  (consumer-side usage budget on the produced value).

This matches the only existing mechanized graded CBPV
(plclub/cbpv-effects-coeffects). Cross-check our Lean against their Coq.

These are declared as `variable` for theorems / defs that need them.
Inductive type formers (VTy / CTy) take them as explicit parameters
because Lean 4's `variable` doesn't auto-bind to inductive type formers. -/

variable {Eff  : Type} [OrderedSemiring Eff]
variable {Mult : Type} [OrderedSemiring Mult]


/-! ## 1. Syntax + judgments -/

/-! ### 1.1 Identifiers -/

abbrev Var  := String
abbrev OpId := String


/-! ### 1.2 Term syntax (CBPV value/computation split)

Values are inert; computations are effectful. The CBPV adjunction crosses
polarity via `vthunk` (value reifying a computation) and `force` (computation
realising a thunked value). Per ADR-0007, force is the only explicit kind-shift.

`Handler` is a value-level spec of how to handle a labelled operation
(per ADR-0008 + the canonical demos). The `state ℓ s` handler threads an
initial state; `throws ℓ` is the zero-shot exception form. -/

mutual
inductive Val : Type where
  | vunit  : Val
  | vint   : Int → Val
  | vvar   : Var → Val
  | vthunk : Comp → Val
  deriving Inhabited
inductive Comp : Type where
  | ret    : Val → Comp                       -- return v  (the F-introducer)
  | letC   : Var → Comp → Comp → Comp         -- let x = M; N
  | force  : Val → Comp                       -- $v
  | lam    : Var → Comp → Comp                -- λx. M
  | app    : Comp → Val → Comp                -- M v
  | up     : Label → OpId → Val → Comp        -- perform ℓ.op(v)  (= Spec.raise)
  | handle : Handler → Comp → Comp            -- with h handle M
  | oom    : Comp                              -- out-of-fuel
  | wrong  : String → Comp                     -- genuinely stuck (type error etc.)
inductive Handler : Type where
  | state  : Label → Val → Handler             -- state ℓ s₀
  | throws : Label → Handler                   -- throws ℓ (zero-shot)
end


/-! ### 1.3 Operational machinery: evaluation contexts (CK frames)

Per ADR-0016 + the operational-shape decision: small-step over a frame list
(Lexa OOPSLA'24 style; near-syntactic mapping to WasmFX typed continuations
later). A `Frame` is one node of the evaluation context; `EvalCtx` is a list
of frames (innermost first).

In the LR (§5), `Stack` is the abstract version; here we have the concrete
representation. The mapping is direct. -/

inductive Frame : Type where
  | letF    : Var → Comp → Frame        -- let x = □; body
  | appF    : Val → Frame                 -- □ v
  | handleF : Handler → Frame             -- handle h □
  deriving Inhabited

abbrev EvalCtx := List Frame   -- innermost frame first; head = next reduction site


/-! ### 1.4 Type syntax (Torczon graded CBPV)

Values inhabit positive `VTy`; computations inhabit negative `CTy`. The
adjunction crosses via:
  - `U φ B`  thunk graded by latent effect φ (surfaced when forced)
  - `F q A`  returner graded by consumer-usage budget q on the result -/

mutual
inductive VTy (Eff Mult : Type) : Type where
  | unit : VTy Eff Mult
  | int  : VTy Eff Mult
  | U    : Eff → CTy Eff Mult → VTy Eff Mult
inductive CTy (Eff Mult : Type) : Type where
  | F   : Mult → VTy Eff Mult → CTy Eff Mult
  | arr : VTy Eff Mult → CTy Eff Mult → CTy Eff Mult
end


/-! ### 1.5 Context — typing environment

A context is a list of (variable, multiplicity, type) bindings. Resource
arithmetic (`scale ρ Γ`, `Γ₁ + Γ₂`) requires the `OrderedSemiring Mult`
instance; left opaque pending Phase A part 2 (QTT-style arithmetic w.r.t.
variable shadowing wants careful definition). -/

abbrev Ctx (Eff Mult : Type) := List (Var × Mult × VTy Eff Mult)

namespace Ctx
  def empty {Eff Mult : Type} : Ctx Eff Mult := []
  def bind {Eff Mult : Type}
      (x : Var) (ρ : Mult) (A : VTy Eff Mult) (Γ : Ctx Eff Mult) : Ctx Eff Mult :=
    (x, ρ, A) :: Γ
end Ctx

-- Resource arithmetic — Phase A part 2 will make these concrete.
opaque Ctx.scale {Eff Mult : Type} [OrderedSemiring Mult] :
    Mult → Ctx Eff Mult → Ctx Eff Mult
opaque Ctx.add {Eff Mult : Type} [OrderedSemiring Mult] :
    Ctx Eff Mult → Ctx Eff Mult → Ctx Eff Mult


/-! ### 1.6 Typing judgments

Inductive-Prop families. Phase A part 1: opaque signatures (the form is
frozen; downstream theorems use it). Phase A part 2: per-rule constructors.

  HasVTy : values are inert, judged at VTy
  HasCTy : computations carry an explicit running effect grade `e`,
            inhabit CTy (whose `F q A` annotation is consumer-side coeffect) -/

opaque HasVTy {Eff Mult : Type} [OrderedSemiring Eff] [OrderedSemiring Mult] :
    Ctx Eff Mult → Val → VTy Eff Mult → Prop
opaque HasCTy {Eff Mult : Type} [OrderedSemiring Eff] [OrderedSemiring Mult] :
    Ctx Eff Mult → Comp → Eff → CTy Eff Mult → Prop


/-! ## 0.5 Effect-row well-formedness — keeps rows SET-shaped

bang-lang's rows are idempotent `Finset`s, so they sit in the disjoint/set
fragment (Biernacki §5.4) where the ρ-maps vanish. "Set-shaped" is NOT
automatic under row polymorphism: instantiating `α` in `∀α. ⟨l | α⟩` with a
row containing `l` would let a handler for `l` ACCIDENTALLY capture an
operation smuggled in through `α`. Fix = "lacks" constraint on row variables,
enforced at instantiation. See ADR-0018. -/

opaque Disjoint {Eff : Type} : Eff → Eff → Prop      -- Finset model: ∩ = ∅
opaque RowAll {Eff Mult : Type} :
    (Eff → CTy Eff Mult) → Eff → CTy Eff Mult         -- ∀(α # L). B
opaque WfInst {Eff Mult : Type} :
    CTy Eff Mult → Eff → CTy Eff Mult → Prop          -- well-formed row instantiation

-- [INV] the load-bearing typing side-condition.
theorem rowinst_requires_disjoint
    {Eff Mult : Type} [OrderedSemiring Eff] [OrderedSemiring Mult]
    {q : Eff → CTy Eff Mult} {L ε : Eff} :
    WfInst (RowAll q L) ε (q ε) → Disjoint ε L := sorry

-- [INV][KEY] abstraction-safety / NO accidental handling.
opaque HandlesIntended {Eff : Type} : Eff → Comp → Handler → Prop

theorem no_accidental_handling
    {Eff Mult : Type} [OrderedSemiring Eff] [OrderedSemiring Mult]
    {Γ : Ctx Eff Mult} {l e : Eff} {A : VTy Eff Mult} {q : Mult}
    {body : Comp} {h : Handler} :
    Disjoint l e →
    HasCTy Γ body (l * e) (CTy.F q A) →
    HandlesIntended l body h := sorry


/-! ## 2. Operational semantics (small-step + fuel-iterated)

Per ADR-0016 + the operational-shape decision: `Source.step` is small-step
over a CK-machine decomposition (uses `Frame` / `EvalCtx` from §1.3);
`Source.eval` iterates step under fuel; `Trace` records observed
effect-emission history.

Phase A part 2: concrete `Source.step` rules (force-thunk reduction,
let/app substitution, handler interpretation via Frame inspection). -/

inductive Result (α : Type) where
  | done : α → Result α
  | oom : Result α
  | stuck : Result α

opaque Source.step      : Comp → Option Comp
opaque Source.eval      : Nat → Comp → Result Val
opaque Source.evalTrace : Nat → Comp → Result (Val × Trace)
opaque Trace            : Type
opaque traceWithin      {Eff : Type} : Trace → Eff → Prop
opaque isReturn         : Comp → Prop
opaque NotEvaluated     : Var → Comp → Prop


/-! ## 3. Core syntactic metatheory -/

-- [STD] Value substitution; grades compose multiplicatively.
-- The conclusion's `c` should read `[v/x] c` once subst is concrete;
-- placeholder shape preserves the type signature.
theorem subst_value
    {Eff Mult : Type} [OrderedSemiring Eff] [OrderedSemiring Mult]
    (ρ : Mult) {Γ Δ : Ctx Eff Mult} {v : Val} {A : VTy Eff Mult}
    {c : Comp} {e : Eff} {B : CTy Eff Mult} :
    HasVTy Δ v A →
    HasCTy (Ctx.add Γ (Ctx.scale ρ Δ)) c e B →
    HasCTy (Ctx.add Γ (Ctx.scale ρ Δ)) c e B    -- ⟵ TODO: `[v/x] c`
    := sorry

-- [STD] Preservation.
theorem preservation
    {Eff Mult : Type} [OrderedSemiring Eff] [OrderedSemiring Mult]
    {Γ : Ctx Eff Mult} {c c' : Comp} {e : Eff} {B : CTy Eff Mult} :
    HasCTy Γ c e B → Source.step c = some c' →
    ∃ e', e' ≤ e ∧ HasCTy Γ c' e' B := sorry

-- [STD] Progress.
theorem progress
    {Eff Mult : Type} [OrderedSemiring Eff] [OrderedSemiring Mult]
    {c : Comp} {e : Eff} {B : CTy Eff Mult} :
    HasCTy Ctx.empty c e B → isReturn c ∨ ∃ c', Source.step c = some c' := sorry

-- [STD] Safety = progress + preservation, fuel-lifted.
theorem type_safety
    {Eff Mult : Type} [OrderedSemiring Eff] [OrderedSemiring Mult]
    {c : Comp} {e : Eff} {q : Mult} {A : VTy Eff Mult} :
    HasCTy Ctx.empty c e (CTy.F q A) → ∀ fuel, Source.eval fuel c ≠ Result.stuck
    := sorry


/-! ## 4. Grade soundness (the QTT payoff) -/

-- [KEY] Coeffect erasure: a 0-graded variable is never evaluated.
theorem zero_usage_erasable
    {Eff Mult : Type} [OrderedSemiring Eff] [OrderedSemiring Mult]
    {Γ : Ctx Eff Mult} {x : Var} {A : VTy Eff Mult}
    {c : Comp} {e : Eff} {B : CTy Eff Mult} :
    HasCTy (Ctx.bind x (0 : Mult) A Γ) c e B → NotEvaluated x c := sorry

-- [KEY] Effect soundness: static grade `e` over-approximates every observed trace.
theorem effect_sound
    {Eff Mult : Type} [OrderedSemiring Eff] [OrderedSemiring Mult]
    {c : Comp} {e : Eff} {q : Mult} {A : VTy Eff Mult} {fuel : Nat}
    {v : Val} {t : Trace} :
    HasCTy Ctx.empty c e (CTy.F q A) →
    Source.evalTrace fuel c = Result.done (v, t) →
    traceWithin t e := sorry


/-! ## 5. Observational equivalence — `≈` IS PINNED HERE (do not redefine) -/

-- Helper terms used in §6.
opaque seqComp  : Comp → Comp → Comp
opaque idComp   : Comp
opaque recover  : Comp → Comp
opaque Cxt      : Type                       -- computation-to-computation contexts
opaque Cxt.plug : Cxt → Comp → Comp

-- Observation: fuel-bounded convergence to a returned value.
def Converges (c : Comp) : Prop := ∃ fuel v, Source.eval fuel c = Result.done v

-- THE SPEC NOTION. Contextual approximation (`⊑`) and equivalence (`≈`).
def ctxApprox (c₁ c₂ : Comp) : Prop :=
  ∀ C : Cxt, Converges (Cxt.plug C c₁) → Converges (Cxt.plug C c₂)
def ctxEquiv (c₁ c₂ : Comp) : Prop := ctxApprox c₁ c₂ ∧ ctxApprox c₂ c₁
infixl:50 " ⊑ " => ctxApprox
infixl:50 " ≈ " => ctxEquiv

-- LR is TRANSCRIBED from Biernacki et al. 2018 "Handle with Care" Figs 6–9,
-- adapted from CBV λ^H/L to our CBPV substrate, crossed with Benton–Hur
-- biorthogonality + Katsumata ⊤⊤. Coq cross-check: bitbucket.org/pl-uwr/aleff-logrel.
--
-- bang-lang SIMPLIFICATION (Biernacki §5.4): set-rows ⇒ ρ-maps + `lift` vanish;
-- the row is a plain `Finset`. We drop ρ and `n-free`.

def CoApprox (c₁ c₂ : Comp) : Prop := Converges c₁ → Converges c₂

-- LR helpers (Phase B will make some concrete).
opaque Stack       : Type                            -- abstract; concrete = EvalCtx
opaque Stack.plug  : Stack → Comp → Comp
opaque BaseRel     {Eff Mult : Type} : VTy Eff Mult → Val → Val → Prop
opaque BaseStackRel {Eff Mult : Type} : Nat → CTy Eff Mult → Stack → Stack → Prop
-- THUNK: returns (latent-effect φ, inner CTy). Torczon: φ lives on U.
opaque asThunk     {Eff Mult : Type} : VTy Eff Mult → Option (Eff × CTy Eff Mult)
-- RETURNER: returns (consumer-budget q, inner VTy). Torczon: q lives on F.
opaque asReturner  {Eff Mult : Type} : CTy Eff Mult → Option (Mult × VTy Eff Mult)
-- a control-stuck computation: operation in row `e` applied to a value, in
-- evaluation position, unhandled by the enclosing stack.
opaque raise       {Eff : Type} : Eff → Val → Comp
opaque opArgTy     {Eff Mult : Type} : Eff → VTy Eff Mult
opaque opResTy     {Eff Mult : Type} : Eff → VTy Eff Mult

section LR
variable {Eff Mult : Type} [OrderedSemiring Eff] [OrderedSemiring Mult]

mutual
  -- VALUE relation (their ⟦τ⟧, Fig 6).
  -- THUNK clause (Torczon U_φ): related iff forcing gives related comps.
  -- The grade `φ` bounds effects of the forced body (see effect_sound).
  def Vrel : Nat → VTy Eff Mult → Val → Val → Prop
    | n, A, v₁, v₂ =>
      match asThunk A with
      | some (_φ, B) =>
          ∀ m, m < n → ∀ c₁ c₂,
            v₁ = Val.vthunk c₁ → v₂ = Val.vthunk c₂ → Crel m B c₁ c₂
      | none => BaseRel A v₁ v₂

  -- SIMPLE-EXPRESSION relation (their 𝒮, Fig 7 + row denotation Fig 8).
  def Srel : Nat → Eff → Stack → Stack → Comp → Comp → Prop
    | n, e, S₁, S₂, c₁, c₂ =>
      ∃ a₁ a₂, c₁ = raise e a₁ ∧ c₂ = raise e a₂
        ∧ (∀ m, m < n → Vrel m (opArgTy e) a₁ a₂)
        ∧ (∀ m, m < n → ∀ r₁ r₂, Vrel m (opResTy e) r₁ r₂ →
             CoApprox (Stack.plug S₁ (Comp.ret r₁)) (Stack.plug S₂ (Comp.ret r₂)))

  -- STACK relation (their 𝒦, Fig 7). The `q=0` clause is F-erasure.
  def Krel : Nat → CTy Eff Mult → Stack → Stack → Prop
    | n, B, S₁, S₂ =>
      match asReturner B with
      | some (q, A) =>
          if q = 0 then True   -- F_0 erasure: any consumer-stack works
          else
            (∀ m, m ≤ n → ∀ v₁ v₂, Vrel m A v₁ v₂ →
                CoApprox (Stack.plug S₁ (Comp.ret v₁)) (Stack.plug S₂ (Comp.ret v₂)))
            ∧ (∀ m e₀, m ≤ n → ∀ c₁ c₂, Srel m e₀ S₁ S₂ c₁ c₂ →
                CoApprox (Stack.plug S₁ c₁) (Stack.plug S₂ c₂))
      | none => BaseStackRel n B S₁ S₂

  -- COMPUTATION relation = biorthogonal ⊤⊤-closure over related stacks.
  def Crel : Nat → CTy Eff Mult → Comp → Comp → Prop
    | n, B, c₁, c₂ =>
      ∀ S₁ S₂, Krel n B S₁ S₂ → CoApprox (Stack.plug S₁ c₁) (Stack.plug S₂ c₂)
end
-- decreasing_by: well-founded on (n, sizeOf type); every "▷" is at m < n.
-- May require explicit termination hint or thread the index via WellFoundedRecursion.

end LR

-- [RISKY] Soundness: LR implies contextual approximation. PROVE THIS FIRST.
theorem lr_sound
    {Eff Mult : Type} [OrderedSemiring Eff] [OrderedSemiring Mult]
    {c₁ c₂ : Comp} {B : CTy Eff Mult} :
    (∀ n, Crel n B c₁ c₂) → c₁ ⊑ c₂ := sorry

-- [KEY] Fundamental theorem.
theorem lr_fundamental
    {Eff Mult : Type} [OrderedSemiring Eff] [OrderedSemiring Mult]
    {Γ : Ctx Eff Mult} {c : Comp} {e : Eff} {B : CTy Eff Mult} :
    HasCTy Γ c e B → ∀ n, Crel n B c c := sorry


/-! ## 6. Recovery algebra — the Trinity, stated against `≈` -/

-- [KEY] monoid ⇒ ret is a unit for sequencing.
theorem seq_unit (v : Val) {c : Comp} : seqComp (Comp.ret v) c ≈ c := sorry

-- [RISKY] group (invertible) effects ⇒ recovery rolls back: `c ; recover c ≈ id`.
-- Heunen–Karvonen: effectful computations are reversible IFF the monad is
-- dagger-Frobenius. Open bridge:
--   E a group  ⇒?  the graded monad over U_φ is dagger-Frobenius.
-- Under Torczon grading effects live on U; the H-K invertibility argument
-- still applies on the effect axis. See ADR-0018 Trinity table.
theorem group_recovers
    {Eff : Type} [OrderedSemiring Eff] [AddGroup Eff] {c : Comp} :
    seqComp c (recover c) ≈ idComp := sorry


/-! ## 7. WasmFX target + compilation correctness (the unclaimed ground) -/

opaque Wasmfx.Module        : Type
opaque Wasmfx.Val           : Type
opaque Wasmfx.Ty            : Type
opaque Wasmfx.run           : Nat → Wasmfx.Module → Result Wasmfx.Val
opaque Wasmfx.WellTyped     : Wasmfx.Module → Prop
opaque Wasmfx.MentionsLocal : Wasmfx.Module → Var → Prop
opaque HandlerLawful        : Handler → Prop
opaque Wasmfx.HandlerEquiv  : Wasmfx.Module → Handler → Prop
opaque compileC             : Comp → Wasmfx.Module
opaque compileV             : Val  → Wasmfx.Val
opaque compileHandler       : Handler → Wasmfx.Module

-- [KEY] Type preservation under translation.
theorem compile_well_typed
    {Eff Mult : Type} [OrderedSemiring Eff] [OrderedSemiring Mult]
    {c : Comp} {e : Eff} {q : Mult} {A : VTy Eff Mult} :
    HasCTy Ctx.empty c e (CTy.F q A) → Wasmfx.WellTyped (compileC c) := sorry

-- [KEY][RISKY] Forward simulation. The heart of the contribution.
theorem compile_forward_sim {c : Comp} {v : Val} {fuel : Nat} :
    Source.eval fuel c = Result.done v →
    ∃ fuel', Wasmfx.run fuel' (compileC c) = Result.done (compileV v) := sorry

-- [KEY] Handler ↦ suspend/resume.
theorem handler_compiles {h : Handler} :
    HandlerLawful h → Wasmfx.HandlerEquiv (compileHandler h) h := sorry

-- [KEY] Erasure is observable in the output.
theorem zero_grade_no_code
    {Eff Mult : Type} [OrderedSemiring Eff] [OrderedSemiring Mult]
    {Γ : Ctx Eff Mult} {x : Var} {A : VTy Eff Mult}
    {c : Comp} {e : Eff} {B : CTy Eff Mult} :
    HasCTy (Ctx.bind x (0 : Mult) A Γ) c e B →
    ¬ Wasmfx.MentionsLocal (compileC c) x := sorry

end Bang
