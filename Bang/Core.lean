/-
  Bang/Core.lean — type-level kernel.
  ──────────────────────────────────────
  The substrate every other Bang module imports:
    §0   grade-algebra variables (Eff / Mult typeclass bounds)
    §1.1 identifiers (Var, OpId)
    §1.2 term syntax (Val / Comp / Handler — mutual inductives)
    §1.3 CK-machine frames (Frame / EvalCtx)
    §1.4 type syntax (VTy / CTy — mutual inductives, Eff/Mult-parametrized)
    §1.5 typing-context split (GradeVec / TyCtx — ADR-0019)

  Nothing here proves anything; this file defines the alphabet. Operational
  semantics, typing judgments, LR machinery, compilation are in their own
  modules. Theorem STATEMENTS live in Bang/Spec.lean.
-/

import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Bang.EffectRow

namespace Bang

open Bang.EffectRow (Label)

/-! ## 0. Grade algebras

Following Torczon et al. (OOPSLA 2024, §1): the effect grade indexes the
**thunk** `U_φ B` (latent effect of the suspended computation, surfaced
when forced), and the multiplicity / coeffect grade indexes the **returner**
`F_q A` (consumer-side usage budget on the produced value).

Torczon is the operational/Coq substrate; for the denotational backstop
(graded monadic semantics + coherence of grading for CBPV) see
mcdermott-fscd25-grading-cbpv — the semantic layer Torczon's development
doesn't cover. Confirmed still-SOTA by the 2026-06-21 sweep.

EFFECT GRADE = `Lattice + OrderBot` (resolves Q1 in OPEN_QUESTIONS.md):
  - `⊥`     = no effects (the empty row)
  - `e₁ ⊔ e₂` = combined effects (join; idempotent commutative associative)
  - `≤`      = effect inclusion (sub-effecting)
Concrete instance: `Eff = Finset Label` (ADR-0001), which has the required
Mathlib instances natively.

MULTIPLICITY GRADE = `Semiring`. Concrete instance: `Bang.QTT`
({zero, one, omega}; see `Bang/Mult.lean`). -/

variable {Eff  : Type} [Lattice Eff] [OrderBot Eff]
variable {Mult : Type} [CommSemiring Mult] [DecidableEq Mult]


/-! ## 1. Syntax -/

/-! ### 1.1 Identifiers

`OpId`/`Label` are unchanged (they name *operations*, not bound variables).
The term-level variable is now a **de Bruijn index** (`Nat`), not a name —
see ADR-0020. There is no `Var` abbreviation anymore: a bound occurrence is
the offset to its binder (0 = nearest enclosing binder). -/

abbrev OpId := String


/-! ### 1.2 Term syntax (CBPV value/computation split, de Bruijn — ADR-0020)

Values inert; computations effectful. Adjunction crosses via `vthunk` /
`force`. Variables are de Bruijn indices: `vvar i` references the `i`-th
enclosing binder (0 = nearest). Binders (`lam`, `letC`-continuation) drop
their names — position *is* the identity, so capture and shadowing are
structural (ADR-0020, the 5-falsity chain).

Handler = value-level spec of how to handle a labelled operation
(state ℓ s₀ threads state; throws ℓ is zero-shot exception). Handlers do
NOT bind; their `Val` payload shifts under substitution like any value. -/

mutual
inductive Val : Type where
  | vunit  : Val
  | vint   : Int → Val
  | vvar   : Nat → Val                  -- de Bruijn index (0 = nearest binder)
  | vthunk : Comp → Val
  -- iso-recursive ADT value formers (ADR-0029). All are INERT values; their
  -- eliminators live in `Comp`. `fold`/`unfold` ERASE at runtime — `fold v`
  -- carries no tag beyond the sum's `inl`/`inr`.
  | inl    : Val → Val                  -- sum intro (left)  : A → A + B
  | inr    : Val → Val                  -- sum intro (right) : B → A + B
  | pair   : Val → Val → Val            -- product intro     : A → B → A × B
  | fold   : Val → Val                  -- μ intro (= a constructor): T[μX.T/X] → μX.T
  deriving Inhabited
inductive Comp : Type where
  | ret    : Val → Comp
  | letC   : Comp → Comp → Comp          -- letC M N: N binds index 0 (= M's value)
  | force  : Val → Comp
  | lam    : Comp → Comp                  -- lam M: M binds index 0 (= the argument)
  | app    : Comp → Val → Comp
  | up     : Label → OpId → Val → Comp
  | handle : Handler → Comp → Comp
  -- iso-recursive ADT eliminators (ADR-0029). Scrutinees are VALUES (the formers
  -- above), so these reduce immediately like `force (vthunk M)` — no eval-context
  -- frame is needed.
  | case   : Val → Comp → Comp → Comp     -- sum elim: case v N₁ N₂; each Nᵢ binds index 0
  | split  : Val → Comp → Comp            -- product elim: split v N; N binds idx 1 (fst), idx 0 (snd)
  | unfold : Val → Comp                   -- μ elim (= a match): unfold (fold v) ↦ ret v
  | oom    : Comp
  | wrong  : String → Comp
inductive Handler : Type where
  | state  : Label → Val → Handler
  | throws : Label → Handler
end


/-! ### 1.3 Operational machinery: evaluation contexts (CK frames)

Lexa OOPSLA'24 style; near-syntactic mapping to WasmFX typed continuations.
`letF` carries the continuation `N` (which binds index 0). -/

inductive Frame : Type where
  | letF    : Comp → Frame                -- let □; N   (N binds index 0)
  | appF    : Val → Frame                 -- □ v
  | handleF : Handler → Frame             -- handle h □
  deriving Inhabited

abbrev EvalCtx := List Frame   -- innermost frame first

/-- A CK-machine configuration: a focus computation under a frame stack (ADR-0023). -/
abbrev Config := EvalCtx × Comp


/-! ### 1.4 Type syntax (Torczon graded CBPV) -/

mutual
inductive VTy (Eff Mult : Type) : Type where
  | unit : VTy Eff Mult
  | int  : VTy Eff Mult
  | U    : Eff → CTy Eff Mult → VTy Eff Mult
  -- iso-recursive ADT type formers (ADR-0029). `mu A` binds a type-level de Bruijn
  -- recursion variable (`tvar 0` = the nearest enclosing μ); `tvar` is NOT a
  -- polymorphic ∀-variable (ADR-0027), so `μX. 1 + (Int × X)` is a CLOSED,
  -- monomorphic type. Inductive (least fixpoint) only — coinductive μ → Div (ADR-0028).
  | sum  : VTy Eff Mult → VTy Eff Mult → VTy Eff Mult   -- A + B
  | prod : VTy Eff Mult → VTy Eff Mult → VTy Eff Mult   -- A × B
  | mu   : VTy Eff Mult → VTy Eff Mult                  -- μX. A  (A under one type-level binder)
  | tvar : Nat → VTy Eff Mult                           -- type-level de Bruijn recursion var
inductive CTy (Eff Mult : Type) : Type where
  | F   : Mult → VTy Eff Mult → CTy Eff Mult
  -- `arr q A B` = `A →^q B` (Torczon `CAbs q' A B`): the argument multiplicity
  -- `q` records how much the function uses its argument, so `app` has something
  -- to scale the argument's grades by (ADR-0019).
  | arr : Mult → VTy Eff Mult → CTy Eff Mult → CTy Eff Mult
end


/-! ### 1.4a Type-level de Bruijn shift + substitution (ADR-0029, iso-recursive μ)

`unfold` at `μX.A` exposes `A[μX.A / X]` — the iso payoff is that this stays a
SYNTACTIC type operation (no coinductive equality). `tyShiftFrom`/`tySubst` are
the type-level analogues of the term-level `shiftFrom`/`substFrom`, but they cross
only `mu` binders (the sole type-level binder); every other former threads the
cutoff through unchanged. They live on `VTy`/`CTy` (mutual) because `U`/`arr`
nest computation types under value types. -/

mutual
/-- Increment free type-level recursion vars (`≥ c`) by 1; used to push a type
under one extra `mu`. -/
def VTy.tyShiftFrom {Eff Mult : Type} (c : Nat) : VTy Eff Mult → VTy Eff Mult
  | .unit       => .unit
  | .int        => .int
  | .U φ B       => .U φ (CTy.tyShiftFrom c B)
  | .sum A B     => .sum (VTy.tyShiftFrom c A) (VTy.tyShiftFrom c B)
  | .prod A B    => .prod (VTy.tyShiftFrom c A) (VTy.tyShiftFrom c B)
  | .mu A        => .mu (VTy.tyShiftFrom (c + 1) A)        -- mu binds one type var
  | .tvar i      => if i < c then .tvar i else .tvar (i + 1)
def CTy.tyShiftFrom {Eff Mult : Type} (c : Nat) : CTy Eff Mult → CTy Eff Mult
  | .F q A       => .F q (VTy.tyShiftFrom c A)
  | .arr q A B   => .arr q (VTy.tyShiftFrom c A) (CTy.tyShiftFrom c B)
end

mutual
/-- Replace type-level recursion var `k` with `T` (shifted under the `k` crossed
`mu` binders); decrement free vars `> k`. -/
def VTy.tySubstFrom {Eff Mult : Type} (k : Nat) (T : VTy Eff Mult) : VTy Eff Mult → VTy Eff Mult
  | .unit       => .unit
  | .int        => .int
  | .U φ B       => .U φ (CTy.tySubstFrom k T B)
  | .sum A B     => .sum (VTy.tySubstFrom k T A) (VTy.tySubstFrom k T B)
  | .prod A B    => .prod (VTy.tySubstFrom k T A) (VTy.tySubstFrom k T B)
  | .mu A        => .mu (VTy.tySubstFrom (k + 1) (VTy.tyShiftFrom 0 T) A)
  | .tvar i      =>
      if i = k then T
      else if i > k then .tvar (i - 1)
      else .tvar i
def CTy.tySubstFrom {Eff Mult : Type} (k : Nat) (T : VTy Eff Mult) : CTy Eff Mult → CTy Eff Mult
  | .F q A       => .F q (VTy.tySubstFrom k T A)
  | .arr q A B   => .arr q (VTy.tySubstFrom k T A) (CTy.tySubstFrom k T B)
end

/-- The μ-unrolling `A[μX.A / X]`: fill the nearest type-level recursion var
(index 0) with the whole `μX.A`, renumbering. This is the type `unfold` exposes. -/
abbrev VTy.unrollMu {Eff Mult : Type} (A : VTy Eff Mult) : VTy Eff Mult :=
  VTy.tySubstFrom 0 (VTy.mu A) A


/-! ### 1.5 Typing-context split — positional grade-vector + ambient type context
(ADR-0019's "grades split, types ambient" insight; ADR-0020 positional carrier)

Two independent **positional** components, indexed by de Bruijn position
(index `i` ↦ the `i`-th entry). Both are `List`s of the SAME length by
construction (every binder conses onto BOTH), so the de-Bruijn cons `ρ .: γ`
is just `::`, and the grade operations become *correct* (they extend in
lockstep):

  - `GradeVec := List Mult`  — the **resources**. Splits, scales, adds:
      `γ₁ + γ₂`  = `List.zipWith (· + ·)`  (correct: same length)
      `ρ • γ`    = `List.map (ρ * ·)`
    Torczon's `gradeVec := fin n → Q`, list-encoded.

  - `TyCtx := List VTy`  — the **ambient types**. Shared across a derivation;
    never scaled or added (types must *match*, not add). Torczon's
    `context := fin n → ValTy`. Lookup is `Γ.get? i`.

The ADR-0019 carrier (`Finsupp`, `Var →₀ Mult`) was the *named*-key alignment
fix; de Bruijn aligns positionally, so the carrier reverts to a list and the
five named side-conditions (closedness, grade-freshness, no-dup-keys, the two
`γ y = 0` invariants) become structural — they vanish. -/

abbrev GradeVec (Mult : Type) := List Mult

abbrev TyCtx (Eff Mult : Type) := List (VTy Eff Mult)

/-- Positional grade addition (de Bruijn `γ₁ Q+ γ₂`). Same-length lists. -/
def GradeVec.add {Mult : Type} [Add Mult] (γ₁ γ₂ : GradeVec Mult) : GradeVec Mult :=
  List.zipWith (· + ·) γ₁ γ₂

/-- Positional scalar action (de Bruijn `ρ Q* γ`). -/
def GradeVec.smul {Mult : Type} [Mul Mult] (ρ : Mult) (γ : GradeVec Mult) : GradeVec Mult :=
  γ.map (ρ * ·)

instance {Mult : Type} [Add Mult] : Add (GradeVec Mult) := ⟨GradeVec.add⟩
instance {Mult : Type} [Mul Mult] : HSMul Mult (GradeVec Mult) (GradeVec Mult) :=
  ⟨GradeVec.smul⟩

/-- The i-th basis vector of length `n`: grade `1` at position `i`, `0`
elsewhere (de Bruijn `T_Var`'s grade). -/
def GradeVec.basis {Mult : Type} [Zero Mult] [One Mult] (n i : Nat) : GradeVec Mult :=
  (List.range n).map (fun j => if j = i then (1 : Mult) else 0)

/-- The all-`0` grade vector of length `n` (de Bruijn `0s`). -/
def GradeVec.zeros {Mult : Type} [Zero Mult] (n : Nat) : GradeVec Mult :=
  List.replicate n (0 : Mult)


/-! ### 1.6 Effect-operation signatures (ADR-0022)

The interface a program's `effect` declarations present to the type system: each
operation `(ℓ : Label, op : OpId)` has an argument and a result type, and each label
embeds as a singleton effect row. Kept as a typeclass (not baked into `Eff`, which
stays the pure `[Lattice] [OrderBot]` row algebra of ADR-0001/0018) so the kernel is
parametric over the signature; a program supplies the instance.

`labelEff_ne_bot` (a label's effect is never the empty row) is what makes an unhandled
`up` untypable at `⊥`, so `progress`/`type_safety` hold for fully-handled programs
(ADR-0022 D3). Concrete instance for `EffRow = Finset Label`: `labelEff ℓ = {ℓ}`
(`labelEff_ne_bot` = `Finset.singleton_ne_empty`).

The `up` typing rule (`Bang/Syntax.lean`, ADR-0022 D2) and handler typing consume
this; the metatheory is parametric in `[EffSig Eff Mult]`, so no global instance is
needed to state or prove the theorems. -/
class EffSig (Eff Mult : Type) [Lattice Eff] [OrderBot Eff] where
  /-- The singleton effect row of a label (`ℓ ∈ φ` is `labelEff ℓ ≤ φ`). -/
  labelEff : Label → Eff
  /-- Operation argument type (`none` = `op` is NOT in label `ℓ`'s interface, ADR-0023 D6). -/
  opArg : Label → OpId → Option (VTy Eff Mult)
  /-- Operation result type (`none` = `op` is NOT in label `ℓ`'s interface). -/
  opRes : Label → OpId → Option (VTy Eff Mult)
  /-- A label's effect is non-empty — no operation lives in the empty row. -/
  labelEff_ne_bot : ∀ ℓ, labelEff ℓ ≠ (⊥ : Eff)
  /-- Label separation (ADR-0023 D6): a label embeds atomically, so it cannot hide inside a
  *different* label's row — it must be in the residual `φ`. Needed in the machine's deep-DISPATCH
  preservation (skipping a non-matching, different-label handler must not lose the performed label).
  Holds for `Finset` singletons (atoms of a distributive lattice). -/
  labelEff_sep : ∀ ℓ ℓ' (φ : Eff), labelEff ℓ ≤ labelEff ℓ' ⊔ φ → ℓ ≠ ℓ' → labelEff ℓ ≤ φ

end Bang
