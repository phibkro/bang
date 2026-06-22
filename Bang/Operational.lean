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

open Bang.EffectRow (Label)

variable {Eff  : Type} [Lattice Eff] [OrderBot Eff]
variable {Mult : Type} [CommSemiring Mult] [DecidableEq Mult]


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

/-! ### CK machine (ADR-0023) — deep handlers over `EvalCtx × Comp`.

The substitution step (pre-ADR-0023, preserved in git) was a *shallow* handler: it caught an
operation only when it sat DIRECTLY under a `handle`. A well-typed body can nest an operation under
`letC`/`app` frames, and a deep handler must reach past them — and, for a zero-shot exception,
DISCARD the intervening continuation. A substitution step cannot express that; a stack can.

State = `Config := EvalCtx × Comp` (focus + frame stack, innermost frame first). Binding stays
substitution-based (this is a CK machine, not a CEK machine), so the focus is always closed.

```
PUSH      ⟨K, letC M N⟩          ↦ ⟨letF N :: K, M⟩          (focus the bound computation)
          ⟨K, app M v⟩           ↦ ⟨appF v :: K, M⟩
          ⟨K, handle h M⟩        ↦ ⟨handleF h :: K, M⟩
          ⟨K, force (vthunk M)⟩  ↦ ⟨K, M⟩
REDUCE    ⟨letF N :: K, ret v⟩   ↦ ⟨K, N[v]⟩                 (let bind)
          ⟨appF v :: K, lam M⟩   ↦ ⟨K, M[v]⟩                 (β)
          ⟨handleF h :: K, ret v⟩↦ ⟨K, ret v⟩                (handler return = identity, Q6 simpl.)
DISPATCH  ⟨K, up ℓ op v⟩         ↦ scan K for the nearest handling frame:
            throws ℓ ⊳ raise:    ↦ ⟨Kₒ, ret v⟩  (ABORT: discard the captured continuation Kᵢ)
            no handler in K:     ↦ stuck
```

`state` dispatch (resume, threading the stored state) is deferred (Q12/Q6) — it KEEPS `Kᵢ` instead of
discarding it; the search is identical. -/

/-- Does handler `h` catch operation `(ℓ, op)`? -/
def handlesOp : Handler → Label → OpId → Bool
  | .throws ℓ',   ℓ, op => (ℓ' = ℓ) && (op == "raise")
  | .state  ℓ' _, ℓ, op => (ℓ' = ℓ) && (op == "get" || op == "put")

/-- Deep-handler dispatch: walk the stack (innermost first) to the nearest frame catching `(ℓ, op)`.
`letF`/`appF` frames and non-matching `handleF` frames are skipped — for `throws` (zero-shot) the
skipped `letF`/`appF` frames ARE the discarded continuation. Reaching `[]` = unhandled = stuck. -/
def dispatch : EvalCtx → Label → OpId → Val → Option Config
  | [], _, _, _ => none
  | (.handleF h :: K), ℓ, op, v =>
      if handlesOp h ℓ op then
        match h with
        | .throws _  => some (K, .ret v)      -- abort to the outer stack with the payload
        | .state _ _ => none                  -- state resumption deferred (Q12)
      else dispatch K ℓ op v
  | (_ :: K), ℓ, op, v => dispatch K ℓ op v   -- skip letF/appF (captured continuation)

/-- One machine transition. `none` = stuck (terminal `⟨[], ret v⟩`, or genuinely wrong). -/
def Source.step : Config → Option Config
  -- PUSH
  | (K, .letC M N)          => some (.letF N :: K, M)
  | (K, .app M v)           => some (.appF v :: K, M)
  | (K, .handle h M)        => some (.handleF h :: K, M)
  | (K, .force (.vthunk M)) => some (K, M)
  -- REDUCE
  | (.letF N :: K, .ret v)  => some (K, Comp.subst v N)
  | (.appF v :: K, .lam M)  => some (K, Comp.subst v M)
  | (.handleF _ :: K, .ret v) => some (K, .ret v)
  -- DISPATCH
  | (K, .up ℓ op v)         => dispatch K ℓ op v
  -- stuck
  | _                       => none

/-- Plug a focus back into its evaluation context (the inverse of decomposition). -/
def plug : EvalCtx → Comp → Comp
  | [], c            => c
  | .letF N :: K, c  => plug K (.letC c N)
  | .appF v :: K, c  => plug K (.app c v)
  | .handleF h :: K, c => plug K (.handle h c)

/-- Run a config to a returned value. `⟨[], ret v⟩` = done; `step = none` on a non-terminal = stuck. -/
def Config.run : Nat → Config → Result Val
  | 0, _              => .oom
  | _ + 1, ([], .ret v) => .done v
  | n + 1, cfg        =>
      match Source.step cfg with
      | some cfg' => Config.run n cfg'
      | none      => .stuck

/-- Source.eval: load the closed program into `⟨[], c⟩` and run the machine. Signature unchanged
(ADR-0023 D3), so `type_safety`'s frozen statement is untouched. -/
def Source.eval (fuel : Nat) (c : Comp) : Result Val := Config.run fuel ([], c)

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
