/-
  Bang/LR.lean — logical relations + observational equivalence + recovery.
  ─────────────────────────────────────────────────────────────────────────
    §5 helpers — Stack, BaseRel, asThunk, asReturner, raise, opArgTy, opResTy
    §5 ⊑ / ≈ — ctxApprox, ctxEquiv, Converges, CoApprox, Cxt, Cxt.plug
    §5 LR — Vrel, Srel, Krel, Crel (axioms; PROOF_ORDER #1 will replace)
    §6 helpers — seqComp, idComp, recover

  Theorem STATEMENTS (lr_sound, lr_fundamental, seq_unit, group_recovers)
  live in Bang/Spec.lean. -/

import Bang.Core
import Bang.Syntax
import Bang.Operational

namespace Bang

variable {Eff  : Type} [Lattice Eff] [OrderBot Eff]
variable {Mult : Type} [Semiring Mult] [DecidableEq Mult]


/-! ## 5. Observational equivalence — `≈` is the spec notion of equality -/

-- §6 helpers (used by recovery theorems in Spec.lean):
axiom seqComp  : Comp → Comp → Comp
axiom idComp   : Comp
axiom recover  : Comp → Comp

-- Computation-to-computation contexts (for ctxApprox).
axiom Cxt      : Type
axiom Cxt.plug : Cxt → Comp → Comp

/-- Observation: fuel-bounded convergence to a returned value. -/
def Converges (c : Comp) : Prop := ∃ fuel v, Source.eval fuel c = Result.done v

/-- THE SPEC NOTION. Contextual approximation (`⊑`) and equivalence (`≈`). -/
def ctxApprox (c₁ c₂ : Comp) : Prop :=
  ∀ C : Cxt, Converges (Cxt.plug C c₁) → Converges (Cxt.plug C c₂)
def ctxEquiv (c₁ c₂ : Comp) : Prop := ctxApprox c₁ c₂ ∧ ctxApprox c₂ c₁
infixl:50 " ⊑ " => ctxApprox
infixl:50 " ≈ " => ctxEquiv

/-- Termination of c₁ implies termination of c₂ (Biernacki's `Obs`, approx form). -/
def CoApprox (c₁ c₂ : Comp) : Prop := Converges c₁ → Converges c₂


/-! ## 5.1 LR helpers (Phase B PROOF_ORDER #1 will concretize) -/

axiom Stack       : Type
axiom Stack.plug  : Stack → Comp → Comp
axiom BaseRel     {Eff Mult : Type} : VTy Eff Mult → Val → Val → Prop
axiom BaseStackRel {Eff Mult : Type} : Nat → CTy Eff Mult → Stack → Stack → Prop
axiom asThunk     {Eff Mult : Type} : VTy Eff Mult → Option (Eff × CTy Eff Mult)
axiom asReturner  {Eff Mult : Type} : CTy Eff Mult → Option (Mult × VTy Eff Mult)
axiom raise       {Eff : Type} : Eff → Val → Comp
axiom opArgTy     {Eff Mult : Type} : Eff → VTy Eff Mult
axiom opResTy     {Eff Mult : Type} : Eff → VTy Eff Mult


/-! ## 5.2 LR — Vrel / Srel / Krel / Crel

Phase A part 1 stubbed as axioms (the mutual block needs step-indexed
WellFoundedRecursion via Ahmed-style lex order on `(n, sizeOf type)`).
Phase B PROOF_ORDER #1 replaces with real defs; signatures are frozen.

See `docs/notes/tactics-survey.md` (C) for iris-lean ▷ modality option. -/

axiom Vrel {Eff Mult : Type} [Lattice Eff] [OrderBot Eff] [Semiring Mult] [DecidableEq Mult] :
    Nat → VTy Eff Mult → Val → Val → Prop
axiom Srel {Eff Mult : Type} [Lattice Eff] [OrderBot Eff] [Semiring Mult] [DecidableEq Mult] :
    Nat → Eff → Stack → Stack → Comp → Comp → Prop
axiom Krel {Eff Mult : Type} [Lattice Eff] [OrderBot Eff] [Semiring Mult] [DecidableEq Mult] :
    Nat → CTy Eff Mult → Stack → Stack → Prop
axiom Crel {Eff Mult : Type} [Lattice Eff] [OrderBot Eff] [Semiring Mult] [DecidableEq Mult] :
    Nat → CTy Eff Mult → Comp → Comp → Prop

end Bang
