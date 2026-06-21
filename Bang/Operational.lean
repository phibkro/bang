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

variable {Eff  : Type} [Lattice Eff] [OrderBot Eff]
variable {Mult : Type} [Semiring Mult] [DecidableEq Mult]


/-! ### 1.3a Substitution (de Bruijn — ADR-0020)

De Bruijn indices make capture and shadowing structural; no name comparison,
no α-renaming. Standard two-step recipe (Pierce TAPL §6.2, autosubst):

  1. **shift** (a.k.a. lift) — `shiftFrom c t` increments every *free* index
     (one `≥ c`) by 1, leaving bound indices (`< c`) alone. Used to push a
     value under one extra binder. `c` is the cutoff = number of binders
     already crossed.

  2. **single substitution at a level** — `substFrom k v t` replaces de Bruijn
     index `k` with `v` (with `v` shifted up by `k` to account for the `k`
     binders between the redex and the occurrence), and *decrements* every
     index `> k` (the binder that introduced level `k` is being removed).

The β / let head-redex substitution `c[v]` is `Comp.subst v c := substFrom 0 v c`:
fill the nearest binder (index 0) with `v` and renumber the rest down.

Three mutual defs because `vthunk` carries a `Comp`, `handle` carries a
`Handler`, `state` carries a `Val`. Handlers do NOT bind, so their cutoff is
threaded through unchanged into the payload value. -/

mutual
/-- Increment free indices (`≥ c`) by 1. -/
def Val.shiftFrom (c : Nat) : Val → Val
  | .vunit       => .vunit
  | .vint n      => .vint n
  | .vvar i      => if i < c then .vvar i else .vvar (i + 1)
  | .vthunk M    => .vthunk (Comp.shiftFrom c M)
def Comp.shiftFrom (c : Nat) : Comp → Comp
  | .ret w       => .ret (Val.shiftFrom c w)
  | .letC M N    => .letC (Comp.shiftFrom c M) (Comp.shiftFrom (c + 1) N)  -- N binds 0
  | .force w     => .force (Val.shiftFrom c w)
  | .lam M       => .lam (Comp.shiftFrom (c + 1) M)                        -- M binds 0
  | .app M w     => .app (Comp.shiftFrom c M) (Val.shiftFrom c w)
  | .up ℓ op w   => .up ℓ op (Val.shiftFrom c w)
  | .handle h M  => .handle (Handler.shiftFrom c h) (Comp.shiftFrom c M)
  | .oom         => .oom
  | .wrong s     => .wrong s
def Handler.shiftFrom (c : Nat) : Handler → Handler
  | .state ℓ s   => .state ℓ (Val.shiftFrom c s)
  | .throws ℓ    => .throws ℓ
end

/-- `Val.shift = Val.shiftFrom 0` — push a closed-ish value under one binder. -/
abbrev Val.shift  : Val → Val  := Val.shiftFrom 0
abbrev Comp.shift : Comp → Comp := Comp.shiftFrom 0

mutual
/-- Replace de Bruijn level `k` with `v` (shifted under the `k` crossed
binders); decrement free indices `> k`. -/
def Val.substFrom (k : Nat) (v : Val) : Val → Val
  | .vunit       => .vunit
  | .vint n      => .vint n
  | .vvar i      =>
      if i = k then v
      else if i > k then .vvar (i - 1)       -- the level-k binder is gone; renumber down
      else .vvar i                            -- i < k: a deeper-bound var, untouched
  | .vthunk M    => .vthunk (Comp.substFrom k v M)
def Comp.substFrom (k : Nat) (v : Val) : Comp → Comp
  | .ret w       => .ret (Val.substFrom k v w)
  | .letC M N    => .letC (Comp.substFrom k v M) (Comp.substFrom (k + 1) (Val.shift v) N)
  | .force w     => .force (Val.substFrom k v w)
  | .lam M       => .lam (Comp.substFrom (k + 1) (Val.shift v) M)
  | .app M w     => .app (Comp.substFrom k v M) (Val.substFrom k v w)
  | .up ℓ op w   => .up ℓ op (Val.substFrom k v w)
  | .handle h M  => .handle (Handler.substFrom k v h) (Comp.substFrom k v M)
  | .oom         => .oom
  | .wrong s     => .wrong s
def Handler.substFrom (k : Nat) (v : Val) : Handler → Handler
  | .state ℓ s   => .state ℓ (Val.substFrom k v s)
  | .throws ℓ    => .throws ℓ
end

/-- The head-redex substitution `c[v]`: fill the nearest binder (index 0)
with `v`, renumbering. β / let reduce with this. -/
abbrev Comp.subst (v : Val) : Comp → Comp := Comp.substFrom 0 v
abbrev Val.subst  (v : Val) : Val  → Val  := Val.substFrom 0 v


/-! ## 2. Operational semantics (small-step + fuel-iterated) -/

inductive Result (α : Type) where
  | done : α → Result α
  | oom : Result α
  | stuck : Result α

/-! Source.step — substitution-based small-step semantics (de Bruijn).

Reductions at the head (`c[v]` = `Comp.subst v c` = fill index 0):
  force (vthunk M)            ↦  M
  app   (lam M) v             ↦  M[v]
  letC  (ret v) N             ↦  N[v]
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
  | .app (.lam M) v                            => some (Comp.subst v M)
  | .letC (.ret v) N                           => some (Comp.subst v N)
  | .handle _ (.ret v)                         => some (.ret v)
  | .handle (.throws ℓ) (.up ℓ' "raise" v)     =>
      if ℓ = ℓ' then some (.ret v) else none
  | .handle (.state ℓ s) (.up ℓ' "get" _)      =>
      if ℓ = ℓ' then some (.handle (.state ℓ s) (.ret s)) else none
  | .handle (.state ℓ _) (.up ℓ' "put" v)      =>
      if ℓ = ℓ' then some (.handle (.state ℓ v) (.ret .vunit)) else none
  | .letC M N                                  =>
      match Source.step M with
      | some M' => some (.letC M' N)
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

/-- NotEvaluated: real semantic notion (de Bruijn index `i`'s thunk is never
forced) needs Source.step reachability analysis. Axiom for now. -/
axiom NotEvaluated     : Nat → Comp → Prop

end Bang
