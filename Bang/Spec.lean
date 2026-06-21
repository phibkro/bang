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
    - §5 LR is defined; uses axiomBaseRel / asThunk / asReturner (Phase B)
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

variable {Eff  : Type} [Semiring Eff] [PartialOrder Eff]
variable {Mult : Type} [Semiring Mult] [DecidableEq Mult]


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


/-! ### 1.3a Substitution (capture-avoiding, named binders)

Standard structural substitution `[v/x]` on `Val`/`Comp`/`Handler`. Three
mutual defs because:
  - `Val.vthunk` carries a `Comp` → needs `Comp.subst` recursively
  - `Comp.handle` carries a `Handler` → needs `Handler.subst`
  - `Handler.state` carries a `Val` → needs `Val.subst`

At binders (`letC y _ _`, `lam y _`) we skip substitution into the scope when
`x = y` (the bound `y` shadows the outer `x`). This is the standard textbook
shape; α-renaming subtleties are deferred (works for closed-program reductions).
-/

mutual
def Val.subst (x : Var) (v : Val) : Val → Val
  | .vunit       => .vunit
  | .vint n      => .vint n
  | .vvar y      => if x = y then v else .vvar y
  | .vthunk M    => .vthunk (Comp.subst x v M)
def Comp.subst (x : Var) (v : Val) : Comp → Comp
  | .ret w       => .ret (Val.subst x v w)
  | .letC y M N  => if x = y then .letC y (Comp.subst x v M) N
                             else .letC y (Comp.subst x v M) (Comp.subst x v N)
  | .force w     => .force (Val.subst x v w)
  | .lam y M     => if x = y then .lam y M else .lam y (Comp.subst x v M)
  | .app M w     => .app (Comp.subst x v M) (Val.subst x v w)
  | .up ℓ op w   => .up ℓ op (Val.subst x v w)
  | .handle h M  => .handle (Handler.subst x v h) (Comp.subst x v M)
  | .oom         => .oom
  | .wrong s     => .wrong s
def Handler.subst (x : Var) (v : Val) : Handler → Handler
  | .state ℓ s   => .state ℓ (Val.subst x v s)
  | .throws ℓ    => .throws ℓ
end


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
arithmetic (`scale ρ Γ`, `Γ₁ + Γ₂`) is QTT-style: scale multiplies every
binding's multiplicity by ρ; add combines two contexts of the same shape
(same variables in same order) by adding multiplicities pointwise.

CAVEAT: this List-based representation requires `Γ₁` and `Γ₂` in
`Ctx.add` to have matching variable lists in matching order. A FinMap-based
representation would handle arbitrary contexts cleanly; defer that to a
future Ctx refactor if proofs surface the need. -/

abbrev Ctx (Eff Mult : Type) := List (Var × Mult × VTy Eff Mult)

namespace Ctx
  def empty {Eff Mult : Type} : Ctx Eff Mult := []
  def bind {Eff Mult : Type}
      (x : Var) (ρ : Mult) (A : VTy Eff Mult) (Γ : Ctx Eff Mult) : Ctx Eff Mult :=
    (x, ρ, A) :: Γ
end Ctx

-- Resource arithmetic — concrete QTT-style. Scale multiplies; add zips.
def Ctx.scale {Eff Mult : Type} [Semiring Mult] (ρ : Mult)
    (Γ : Ctx Eff Mult) : Ctx Eff Mult :=
  Γ.map (fun b => (b.1, ρ * b.2.1, b.2.2))

def Ctx.add {Eff Mult : Type} [Semiring Mult]
    (Γ₁ Γ₂ : Ctx Eff Mult) : Ctx Eff Mult :=
  List.zipWith (fun b₁ b₂ => (b₁.1, b₁.2.1 + b₂.2.1, b₁.2.2)) Γ₁ Γ₂


/-! ### 1.6 Typing judgments

Inductive-Prop families. One constructor per typing rule:

  HasVTy : values are inert (no effect grade); judged at VTy
  HasCTy : computations carry an explicit running effect grade `e`;
           inhabit CTy (whose `F q A` annotation is consumer-side coeffect)

PHASE A part 2 first cut: rules cover the common cases. Refinements pending:
  - `vvar`: only checks variable presence, not multiplicity `1 ≤ ρ`
    (needs `[PartialOrder Mult]` or explicit threshold predicate)
  - `up`: omitted (needs `opArgTy`/`opResTy` concrete; see §5 LR helpers)
  - `handle`: simplified — body's effect passes through unchanged
    (real rule should remove the handled label from the effect row)
  - QTT-style context arithmetic (Ctx.scale, Ctx.add in premises) is
    approximated by simple list-cons context extension `(y, ρ, A) :: Γ`
-/

mutual
inductive HasVTy : Ctx Eff Mult → Val → VTy Eff Mult → Prop where
  | vunit  : ∀ {Γ}, HasVTy Γ Val.vunit VTy.unit
  | vint   : ∀ {Γ n}, HasVTy Γ (Val.vint n) VTy.int
  | vvar   : ∀ {Γ x A}, (∃ ρ, (x, ρ, A) ∈ Γ) → HasVTy Γ (Val.vvar x) A
  | vthunk : ∀ {Γ M φ B}, HasCTy Γ M φ B → HasVTy Γ (Val.vthunk M) (VTy.U φ B)
inductive HasCTy : Ctx Eff Mult → Comp → Eff → CTy Eff Mult → Prop where
  | ret    : ∀ {Γ v A q}, HasVTy Γ v A → HasCTy Γ (Comp.ret v) 0 (CTy.F q A)
  | letC   : ∀ {Γ y M N φ₁ φ₂ ρ A q B},
      HasCTy Γ M φ₁ (CTy.F q A) →
      HasCTy ((y, ρ, A) :: Γ) N φ₂ B →
      HasCTy Γ (Comp.letC y M N) (φ₁ + φ₂) B
  | force  : ∀ {Γ v φ B},
      HasVTy Γ v (VTy.U φ B) →
      HasCTy Γ (Comp.force v) φ B
  | lam    : ∀ {Γ y M φ ρ A B},
      HasCTy ((y, ρ, A) :: Γ) M φ B →
      HasCTy Γ (Comp.lam y M) 0 (CTy.arr A B)
  | app    : ∀ {Γ M v φ A B},
      HasCTy Γ M φ (CTy.arr A B) →
      HasVTy Γ v A →
      HasCTy Γ (Comp.app M v) φ B
  | handle : ∀ {Γ h M φ B},
      HasCTy Γ M φ B →
      HasCTy Γ (Comp.handle h M) φ B
end


/-! ## 0.5 Effect-row well-formedness — keeps rows SET-shaped

bang-lang's rows are idempotent `Finset`s, so they sit in the disjoint/set
fragment (Biernacki §5.4) where the ρ-maps vanish. "Set-shaped" is NOT
automatic under row polymorphism: instantiating `α` in `∀α. ⟨l | α⟩` with a
row containing `l` would let a handler for `l` ACCIDENTALLY capture an
operation smuggled in through `α`. Fix = "lacks" constraint on row variables,
enforced at instantiation. See ADR-0018. -/

axiom Disjoint {Eff : Type} : Eff → Eff → Prop      -- Finset model: ∩ = ∅
axiom RowAll {Eff Mult : Type} :
    (Eff → CTy Eff Mult) → Eff → CTy Eff Mult         -- ∀(α # L). B
axiom WfInst {Eff Mult : Type} :
    CTy Eff Mult → Eff → CTy Eff Mult → Prop          -- well-formed row instantiation

-- [INV] the load-bearing typing side-condition.
theorem rowinst_requires_disjoint
    {q : Eff → CTy Eff Mult} {L ε : Eff} :
    WfInst (RowAll q L) ε (q ε) → Disjoint ε L := sorry

-- [INV][KEY] abstraction-safety / NO accidental handling.
axiom HandlesIntended {Eff : Type} : Eff → Comp → Handler → Prop

theorem no_accidental_handling
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

/-! Source.step — substitution-based small-step semantics

Reductions at the head:
  force (vthunk M)            ↦  M
  app   (lam x M) v           ↦  M[v/x]
  letC  x (ret v) N           ↦  N[v/x]
  handle h (ret v)            ↦  ret v                  (simplified: handler discards on return)
  handle (throws ℓ) (up ℓ "raise" v)   ↦  ret v          (zero-shot throws catches matching label)
  handle (state ℓ s) (up ℓ "get" _)    ↦  handle (state ℓ s) (ret s)
  handle (state ℓ _) (up ℓ "put" v)    ↦  handle (state ℓ v) (ret .vunit)

Search (no head redex): step into the leftmost subterm of letC / app / handle.

PHASE A part 2 simplifications (refine in Phase B):
  - Handler return clauses are identity (real return clause is per-handler).
  - Operation propagation: when `handle h (up ℓ op v)` doesn't match,
    we return `none` (stuck) rather than propagating with the inner handler
    preserved for later resumption. Pure substitution-based step can't
    cleanly express deep-handler resumption; a CK-machine variant
    (Frame / EvalCtx already defined in §1.3) is the eventual home.
-/
def Source.step : Comp → Option Comp
  | .force (.vthunk M)                         => some M
  | .app (.lam x M) v                          => some (Comp.subst x v M)
  | .letC x (.ret v) N                         => some (Comp.subst x v N)
  | .handle _ (.ret v)                         => some (.ret v)
  | .handle (.throws ℓ) (.up ℓ' "raise" v)     =>
      if ℓ = ℓ' then some (.ret v) else none
  | .handle (.state ℓ s) (.up ℓ' "get" _)      =>
      if ℓ = ℓ' then some (.handle (.state ℓ s) (.ret s)) else none
  | .handle (.state ℓ _) (.up ℓ' "put" v)      =>
      if ℓ = ℓ' then some (.handle (.state ℓ v) (.ret .vunit)) else none
  -- Search rules (no head redex): step into the leftmost subterm.
  | .letC x M N                                =>
      match Source.step M with
      | some M' => some (.letC x M' N)
      | none    => none
  | .app M v                                   =>
      match Source.step M with
      | some M' => some (.app M' v)
      | none    => none
  | .handle h M                                =>
      match Source.step M with
      | some M' => some (.handle h M')
      | none    => none
  | _                                          => none
  termination_by c => sizeOf c

-- Source.eval: fuel-iterated step until we reach a returned value.
def Source.eval : Nat → Comp → Result Val
  | 0, _      => .oom
  | _ + 1, .ret v => .done v
  | n + 1, c  =>
      match Source.step c with
      | some c' => Source.eval n c'
      | none    => .stuck

-- Trace + evalTrace: pending Phase B (depends on concrete Eff to express
-- "label in effect row"). For now: opaque.
axiom Trace            : Type
axiom Source.evalTrace : Nat → Comp → Result (Val × Trace)
axiom traceWithin      {Eff : Type} : Trace → Eff → Prop

-- isReturn: a Comp is "returned" iff it's `ret v` for some v.
def isReturn : Comp → Prop
  | .ret _ => True
  | _      => False

-- NotEvaluated: a syntactic over-approximation — `x` doesn't free-occur in `c`.
-- The semantic notion (`x`'s thunk is never forced) is the eventual target;
-- the syntactic version is a sound under-approximation suitable for the
-- `zero_usage_erasable` theorem statement.
axiom NotEvaluated     : Var → Comp → Prop


/-! ## 3. Core syntactic metatheory -/

-- [STD] Value substitution; grades compose multiplicatively.
-- The conclusion's `c` should read `[v/x] c` once subst is concrete;
-- placeholder shape preserves the type signature.
theorem subst_value
    (ρ : Mult) {Γ Δ : Ctx Eff Mult} {v : Val} {A : VTy Eff Mult}
    {c : Comp} {e : Eff} {B : CTy Eff Mult} :
    HasVTy Δ v A →
    HasCTy (Ctx.add Γ (Ctx.scale ρ Δ)) c e B →
    HasCTy (Ctx.add Γ (Ctx.scale ρ Δ)) c e B    -- ⟵ TODO: `[v/x] c`
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


/-! ## 5. Observational equivalence — `≈` IS PINNED HERE (do not redefine) -/

-- Helper terms used in §6.
axiom seqComp  : Comp → Comp → Comp
axiom idComp   : Comp
axiom recover  : Comp → Comp
axiom Cxt      : Type                       -- computation-to-computation contexts
axiom Cxt.plug : Cxt → Comp → Comp

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
axiom Stack       : Type                            -- abstract; concrete = EvalCtx
axiom Stack.plug  : Stack → Comp → Comp
axiom BaseRel     {Eff Mult : Type} : VTy Eff Mult → Val → Val → Prop
axiom BaseStackRel {Eff Mult : Type} : Nat → CTy Eff Mult → Stack → Stack → Prop
-- THUNK: returns (latent-effect φ, inner CTy). Torczon: φ lives on U.
axiom asThunk     {Eff Mult : Type} : VTy Eff Mult → Option (Eff × CTy Eff Mult)
-- RETURNER: returns (consumer-budget q, inner VTy). Torczon: q lives on F.
axiom asReturner  {Eff Mult : Type} : CTy Eff Mult → Option (Mult × VTy Eff Mult)
-- a control-stuck computation: operation in row `e` applied to a value, in
-- evaluation position, unhandled by the enclosing stack.
axiom raise       {Eff : Type} : Eff → Val → Comp
axiom opArgTy     {Eff Mult : Type} : Eff → VTy Eff Mult
axiom opResTy     {Eff Mult : Type} : Eff → VTy Eff Mult

-- Phase A part 1: LR mutual defs stubbed as axioms.
-- Phase B (PROOF_ORDER #1) will give real step-indexed definitions; this
-- requires `termination_by` hints (well-founded on Nat index) or Ahmed-style
-- WellFoundedRecursion. Shape preserved in comments below; the SIGNATURES
-- are the spec.

-- VALUE relation (their ⟦τ⟧, Fig 6). THUNK clause (Torczon U_φ):
--   ∀ m < n, ∀ c₁ c₂, v₁ = vthunk c₁ → v₂ = vthunk c₂ → Crel m B c₁ c₂   (asThunk A = some _)
--   BaseRel A v₁ v₂                                                          (otherwise)
axiom Vrel {Eff Mult : Type} [Semiring Eff] [Semiring Mult] [DecidableEq Mult] :
    Nat → VTy Eff Mult → Val → Val → Prop

-- SIMPLE-EXPRESSION relation (their 𝒮, Fig 7):
--   ∃ a₁ a₂, c₁ = raise e a₁ ∧ c₂ = raise e a₂
--     ∧ ▷ Vrel m (opArgTy e) a₁ a₂
--     ∧ ▷ Vrel m (opResTy e) r₁ r₂ → CoApprox (S₁[ret r₁]) (S₂[ret r₂])
axiom Srel {Eff Mult : Type} [Semiring Eff] [Semiring Mult] [DecidableEq Mult] :
    Nat → Eff → Stack → Stack → Comp → Comp → Prop

-- STACK relation (their 𝒦, Fig 7). The q=0 case is F-erasure.
--   asReturner B = some (q, A):
--     q = 0 → True
--     else: agree on RELATED RETURN values AND on RELATED CONTROL-STUCK ops
--   asReturner B = none → BaseStackRel n B S₁ S₂
axiom Krel {Eff Mult : Type} [Semiring Eff] [Semiring Mult] [DecidableEq Mult] :
    Nat → CTy Eff Mult → Stack → Stack → Prop

-- COMPUTATION relation = biorthogonal ⊤⊤-closure over related stacks.
--   ∀ S₁ S₂, Krel n B S₁ S₂ → CoApprox (S₁[c₁]) (S₂[c₂])
axiom Crel {Eff Mult : Type} [Semiring Eff] [Semiring Mult] [DecidableEq Mult] :
    Nat → CTy Eff Mult → Comp → Comp → Prop

-- [RISKY] Soundness: LR implies contextual approximation. PROVE THIS FIRST.
theorem lr_sound
    {c₁ c₂ : Comp} {B : CTy Eff Mult} :
    (∀ n, Crel n B c₁ c₂) → c₁ ⊑ c₂ := sorry

-- [KEY] Fundamental theorem.
theorem lr_fundamental
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
    {Eff : Type} [Semiring Eff] [AddGroup Eff] {c : Comp} :
    seqComp c (recover c) ≈ idComp := sorry


/-! ## 7. WasmFX target + compilation correctness (the unclaimed ground) -/

axiom Wasmfx.Module        : Type
axiom Wasmfx.Val           : Type
axiom Wasmfx.Ty            : Type
axiom Wasmfx.run           : Nat → Wasmfx.Module → Result Wasmfx.Val
axiom Wasmfx.WellTyped     : Wasmfx.Module → Prop
axiom Wasmfx.MentionsLocal : Wasmfx.Module → Var → Prop
axiom HandlerLawful        : Handler → Prop
axiom Wasmfx.HandlerEquiv  : Wasmfx.Module → Handler → Prop
axiom compileC             : Comp → Wasmfx.Module
axiom compileV             : Val  → Wasmfx.Val
axiom compileHandler       : Handler → Wasmfx.Module

-- [KEY] Type preservation under translation.
theorem compile_well_typed
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
    {Γ : Ctx Eff Mult} {x : Var} {A : VTy Eff Mult}
    {c : Comp} {e : Eff} {B : CTy Eff Mult} :
    HasCTy (Ctx.bind x (0 : Mult) A Γ) c e B →
    ¬ Wasmfx.MentionsLocal (compileC c) x := sorry

end Bang
