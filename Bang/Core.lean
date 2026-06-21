/-
  Bang/Core.lean — type-level kernel.
  ──────────────────────────────────────
  The substrate every other Bang module imports:
    §0   grade-algebra variables (Eff / Mult typeclass bounds)
    §1.1 identifiers (Var, OpId)
    §1.2 term syntax (Val / Comp / Handler — mutual inductives)
    §1.3 CK-machine frames (Frame / EvalCtx)
    §1.4 type syntax (VTy / CTy — mutual inductives, Eff/Mult-parametrized)
    §1.5 Ctx + basic ops (empty, bind)

  Nothing here proves anything; this file defines the alphabet. Operational
  semantics, typing judgments, LR machinery, compilation are in their own
  modules. Theorem STATEMENTS live in Bang/Spec.lean.
-/

import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Finset.Basic
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
variable {Mult : Type} [Semiring Mult] [DecidableEq Mult]


/-! ## 1. Syntax -/

/-! ### 1.1 Identifiers -/

abbrev Var  := String
abbrev OpId := String


/-! ### 1.2 Term syntax (CBPV value/computation split)

Values inert; computations effectful. Adjunction crosses via `vthunk` /
`force`. Handler = value-level spec of how to handle a labelled operation
(state ℓ s₀ threads state; throws ℓ is zero-shot exception). -/

mutual
inductive Val : Type where
  | vunit  : Val
  | vint   : Int → Val
  | vvar   : Var → Val
  | vthunk : Comp → Val
  deriving Inhabited
inductive Comp : Type where
  | ret    : Val → Comp
  | letC   : Var → Comp → Comp → Comp
  | force  : Val → Comp
  | lam    : Var → Comp → Comp
  | app    : Comp → Val → Comp
  | up     : Label → OpId → Val → Comp
  | handle : Handler → Comp → Comp
  | oom    : Comp
  | wrong  : String → Comp
inductive Handler : Type where
  | state  : Label → Val → Handler
  | throws : Label → Handler
end


/-! ### 1.3 Operational machinery: evaluation contexts (CK frames)

Lexa OOPSLA'24 style; near-syntactic mapping to WasmFX typed continuations. -/

inductive Frame : Type where
  | letF    : Var → Comp → Frame        -- let x = □; body
  | appF    : Val → Frame                 -- □ v
  | handleF : Handler → Frame             -- handle h □
  deriving Inhabited

abbrev EvalCtx := List Frame   -- innermost frame first


/-! ### 1.4 Type syntax (Torczon graded CBPV) -/

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

List-based (FinMap deferred; see `docs/notes/OPEN_QUESTIONS.md` Q3).
Resource arithmetic (scale, add) lives in `Bang/Syntax.lean`. -/

abbrev Ctx (Eff Mult : Type) := List (Var × Mult × VTy Eff Mult)

namespace Ctx
  def empty {Eff Mult : Type} : Ctx Eff Mult := []
  def bind {Eff Mult : Type}
      (x : Var) (ρ : Mult) (A : VTy Eff Mult) (Γ : Ctx Eff Mult) : Ctx Eff Mult :=
    (x, ρ, A) :: Γ
end Ctx

end Bang
