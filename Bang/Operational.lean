/-
  Bang/Operational.lean — substitution + small-step operational semantics.
  ─────────────────────────────────────────────────────────────────────────
    §1.3a Substitution (Val.subst / Comp.subst / Handler.subst — mutual)
    §2    Source.step, Source.eval, Trace, traceWithin, isReturn, NotEvaluated, Result

  Theorem STATEMENTS (preservation, progress, type_safety, effect_sound,
  zero_usage_erasable) live in Bang/Spec.lean.
-/

import Bang.Core
import Bang.Syntax

namespace Bang

variable {Eff  : Type} [Semiring Eff] [PartialOrder Eff]
variable {Mult : Type} [Semiring Mult] [DecidableEq Mult]


/-! ### 1.3a Substitution (capture-avoiding, named binders)

Three mutual defs because:
  - `Val.vthunk` carries a `Comp` → needs `Comp.subst`
  - `Comp.handle` carries a `Handler` → needs `Handler.subst`
  - `Handler.state` carries a `Val` → needs `Val.subst`

At binders (`letC y _ _`, `lam y _`) we skip substitution into the scope
when `x = y` (bound y shadows outer x). Standard textbook shape;
α-renaming subtleties deferred (works for closed-program reductions). -/

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


/-! ## 2. Operational semantics (small-step + fuel-iterated) -/

inductive Result (α : Type) where
  | done : α → Result α
  | oom : Result α
  | stuck : Result α

/-! Source.step — substitution-based small-step semantics.

Reductions at the head:
  force (vthunk M)            ↦  M
  app   (lam x M) v           ↦  M[v/x]
  letC  x (ret v) N           ↦  N[v/x]
  handle h (ret v)            ↦  ret v                    (simplified return)
  handle (throws ℓ) (up ℓ "raise" v)   ↦  ret v            (zero-shot match)
  handle (state ℓ s) (up ℓ "get" _)    ↦  handle (state ℓ s) (ret s)
  handle (state ℓ _) (up ℓ "put" v)    ↦  handle (state ℓ v) (ret unit)

Search (no head redex): step into the leftmost subterm of letC / app / handle.

Simplifications (see `docs/notes/OPEN_QUESTIONS.md` Q6):
  - Handler return clauses are identity (real return is per-handler).
  - Operation propagation when handle doesn't catch → none (stuck).
    A CK-machine variant via Frame / EvalCtx is the eventual home. -/
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

/-- Source.eval: fuel-iterated step until we reach a returned value. -/
def Source.eval : Nat → Comp → Result Val
  | 0, _      => .oom
  | _ + 1, .ret v => .done v
  | n + 1, c  =>
      match Source.step c with
      | some c' => Source.eval n c'
      | none    => .stuck

-- Trace / evalTrace: still axiom; need concrete Eff to express
-- "label in row" (see `docs/notes/OPEN_QUESTIONS.md` Q1).
axiom Trace            : Type
axiom Source.evalTrace : Nat → Comp → Result (Val × Trace)
axiom traceWithin      {Eff : Type} : Trace → Eff → Prop

/-- isReturn: a Comp is "returned" iff it's `ret v` for some v. -/
def isReturn : Comp → Prop
  | .ret _ => True
  | _      => False

/-- NotEvaluated: real semantic notion (`x`'s thunk is never forced) needs
Source.step reachability analysis. Axiom for now. -/
axiom NotEvaluated     : Var → Comp → Prop

end Bang
