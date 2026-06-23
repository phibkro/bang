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
  | .inl w       => .inl (Val.shiftFrom c w)
  | .inr w       => .inr (Val.shiftFrom c w)
  | .pair w₁ w₂  => .pair (Val.shiftFrom c w₁) (Val.shiftFrom c w₂)
  | .fold w      => .fold (Val.shiftFrom c w)
def Comp.shiftFrom (c : Nat) : Comp → Comp
  | .ret w       => .ret (Val.shiftFrom c w)
  | .letC M N    => .letC (Comp.shiftFrom c M) (Comp.shiftFrom (c + 1) N)  -- N binds 0
  | .force w     => .force (Val.shiftFrom c w)
  | .lam M       => .lam (Comp.shiftFrom (c + 1) M)                        -- M binds 0
  | .app M w     => .app (Comp.shiftFrom c M) (Val.shiftFrom c w)
  | .up ℓ op w   => .up ℓ op (Val.shiftFrom c w)
  | .handle h M  => .handle (Handler.shiftFrom c h) (Comp.shiftFrom c M)
  -- ADT eliminators: each `case` branch binds one (idx 0); `split` binds two (idx 1, 0).
  | .case w N₁ N₂ => .case (Val.shiftFrom c w) (Comp.shiftFrom (c + 1) N₁) (Comp.shiftFrom (c + 1) N₂)
  | .split w N   => .split (Val.shiftFrom c w) (Comp.shiftFrom (c + 2) N)
  | .unfold w    => .unfold (Val.shiftFrom c w)
  | .oom         => .oom
  | .wrong s     => .wrong s
def Handler.shiftFrom (c : Nat) : Handler → Handler
  | .state ℓ s   => .state ℓ (Val.shiftFrom c s)
  | .throws ℓ    => .throws ℓ
  -- transaction's heap cells are CLOSED values (the CK focus is always closed, ADR-0025/0030), so
  -- shift is the IDENTITY on them. We leave `Θ` untouched (rather than `Θ.map (shiftFrom c)`): a
  -- recursive `List.map (Val.shiftFrom c)` call would force the `shiftFrom` mutual block onto
  -- well-founded recursion, breaking the `rfl`-reduction the kernel demos + metatheory rely on. The
  -- identity is SOUND for closed heaps (the only heaps a well-typed `transaction` frame carries).
  | .transaction ℓ Θ => .transaction ℓ Θ
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
  | .inl w       => .inl (Val.substFrom k v w)
  | .inr w       => .inr (Val.substFrom k v w)
  | .pair w₁ w₂  => .pair (Val.substFrom k v w₁) (Val.substFrom k v w₂)
  | .fold w      => .fold (Val.substFrom k v w)
def Comp.substFrom (k : Nat) (v : Val) : Comp → Comp
  | .ret w       => .ret (Val.substFrom k v w)
  | .letC M N    => .letC (Comp.substFrom k v M) (Comp.substFrom (k + 1) (Val.shift v) N)
  | .force w     => .force (Val.substFrom k v w)
  | .lam M       => .lam (Comp.substFrom (k + 1) (Val.shift v) M)
  | .app M w     => .app (Comp.substFrom k v M) (Val.substFrom k v w)
  | .up ℓ op w   => .up ℓ op (Val.substFrom k v w)
  | .handle h M  => .handle (Handler.substFrom k v h) (Comp.substFrom k v M)
  -- ADT eliminators: `case` branches descend under one binder, `split` under two.
  | .case w N₁ N₂ => .case (Val.substFrom k v w)
      (Comp.substFrom (k + 1) (Val.shift v) N₁) (Comp.substFrom (k + 1) (Val.shift v) N₂)
  | .split w N   => .split (Val.substFrom k v w) (Comp.substFrom (k + 2) (Val.shift (Val.shift v)) N)
  | .unfold w    => .unfold (Val.substFrom k v w)
  | .oom         => .oom
  | .wrong s     => .wrong s
def Handler.substFrom (k : Nat) (v : Val) : Handler → Handler
  | .state ℓ s   => .state ℓ (Val.substFrom k v s)
  | .throws ℓ    => .throws ℓ
  -- heap cells are CLOSED ⇒ subst is the identity; leave `Θ` untouched (keeps structural recursion,
  -- so the `substFrom` family still reduces by `rfl`). Sound for closed heaps (ADR-0030).
  | .transaction ℓ Θ => .transaction ℓ Θ
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
  -- transaction (ADR-0030): catches the three stm ops on its own label.
  | .transaction ℓ' _, ℓ, op =>
      (ℓ' = ℓ) && (op == "newTVar" || op == "readTVar" || op == "writeTVar")

/-- Split a stack at the nearest frame catching `(ℓ, op)`: returns `(Kᵢ, h, Kₒ)` with
`K = Kᵢ ++ handleF h :: Kₒ`, `Kᵢ` containing no catching frame (the inner captured continuation),
and `h` the catching handler. `none` = no handler in `K` (unhandled). The recursion is the SAME walk
ADR-0023's `dispatch` did; it now also RETURNS the inner prefix `Kᵢ` (kept by `state`, discarded by
`throws`). -/
def splitAt : EvalCtx → Label → OpId → Option (EvalCtx × Handler × EvalCtx)
  | [], _, _ => none
  | (.handleF h :: K), ℓ, op =>
      if handlesOp h ℓ op then some ([], h, K)
      else (splitAt K ℓ op).map (fun (Kᵢ, h', Kₒ) => (Frame.handleF h :: Kᵢ, h', Kₒ))
  | (fr :: K), ℓ, op =>
      (splitAt K ℓ op).map (fun (Kᵢ, h', Kₒ) => (fr :: Kᵢ, h', Kₒ))

/-- Read TVar index `i` (a payload `vint i`) out of a value; `none` if the payload is malformed. -/
def tvarIdx : Val → Option Nat
  | .vint n => if n ≥ 0 then some n.toNat else none
  | _       => none

/-- Update heap cell `i` to `w` (out-of-range = unchanged; the type system guarantees in-range). -/
def storeSet (Θ : Store) (i : Nat) (w : Val) : Store := List.set Θ i w

/-- Deep-handler dispatch (ADR-0025 generalizes ADR-0023 to KEEP the captured continuation for
resumptive handlers). Split the stack at the nearest catching frame, then:

  - `throws ℓ`: ZERO-SHOT abort. Discard `Kᵢ` and the handler frame; the payload `v` becomes the
    focus over the outer stack `Kₒ`. (ADR-0023, unchanged behaviour.)
  - `state ℓ s`: ONE-SHOT RESUME (ADR-0025). KEEP `Kᵢ` and reinstall a (deep) `state ℓ s'` frame so
    the next operation is handled too:
      · `get`: return the stored `s` to `Kᵢ`, state unchanged (`s' = s`, focus `ret s`);
      · `put w`: store the payload `w`, return `unit` to `Kᵢ` (`s' = w`, focus `ret unit`).
    The resumed stack is `Kᵢ ++ handleF (state ℓ s') :: Kₒ`.
  - `transaction ℓ Θ`: ONE-SHOT RESUME threading the list-heap (ADR-0030) — `state` generalized to a
    list. `newTVar`/`readTVar`/`writeTVar` reinstall a deep `transaction ℓ Θ'` frame with the heap
    grown/read/updated. Rollback is FREE: abort is a foreign `throws` escaping this frame, so `Θ'`
    is discarded with the frame (never commits). A malformed/out-of-range TVar payload yields `oom`.

Reaching `[]` (no catching frame) = unhandled = stuck (`none`). The CK focus stays CLOSED: the stored
`s`/payload `w`/heap cells are closed values (the focus is always closed), so resumption threads no
open term and no variable budget — the grade vectors stay `[]` (ADR-0025 §grade discipline). -/
def dispatchOn (op : OpId) (v : Val) : EvalCtx × Handler × EvalCtx → Option Config
  | (Kᵢ, h, Kₒ) =>
      match h with
      | .throws _   => some (Kₒ, .ret v)                                        -- ABORT
      | .state ℓ' s =>
          if op == "get" then
            some (Kᵢ ++ Frame.handleF (.state ℓ' s) :: Kₒ, .ret s)             -- RESUME with s
          else
            some (Kᵢ ++ Frame.handleF (.state ℓ' v) :: Kₒ, .ret .vunit)        -- RESUME with unit
      -- transaction (ADR-0030): the multi-cell generalization of `state`. RESUME threading the
      -- updated heap (KEEP `Kᵢ`, reinstall a deep `transaction ℓ' Θ'` frame), exactly the ADR-0025
      -- state-resume pattern with a list-heap. Rollback is FREE: an abort is a zero-shot `throws`
      -- that escapes this frame (handled by the throws arm above over a DIFFERENT label), so the
      -- threaded `Θ'` is discarded with the frame and never commits.
      | .transaction ℓ' Θ =>
          if op == "newTVar" then
            -- allocate: append the initial value `v`; the new TVar's index is the old length.
            some (Kᵢ ++ Frame.handleF (.transaction ℓ' (Θ ++ [v])) :: Kₒ, .ret (.vint Θ.length))
          else if op == "readTVar" then
            -- read: payload `vint i`; return cell `i` (oom on a malformed/out-of-range index).
            match tvarIdx v with
            | some i =>
                match Θ[i]? with
                | some cell => some (Kᵢ ++ Frame.handleF (.transaction ℓ' Θ) :: Kₒ, .ret cell)
                | none      => some (Kₒ, .oom)
            | none => some (Kₒ, .oom)
          else
            -- writeTVar: payload `pair (vint i) w`; store `w` at cell `i`, return unit.
            match v with
            | .pair iv w =>
                match tvarIdx iv with
                | some i => some (Kᵢ ++ Frame.handleF (.transaction ℓ' (storeSet Θ i w)) :: Kₒ, .ret .vunit)
                | none   => some (Kₒ, .oom)
            | _ => some (Kₒ, .oom)

def dispatch (K : EvalCtx) (ℓ : Label) (op : OpId) (v : Val) : Option Config :=
  (splitAt K ℓ op).bind (dispatchOn op v)

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
  -- ADT eliminators (ADR-0029): scrutinees are values, so these reduce in place.
  | (K, .case (.inl v) N₁ _)  => some (K, Comp.subst v N₁)   -- sum: left branch
  | (K, .case (.inr v) _ N₂)  => some (K, Comp.subst v N₂)   -- sum: right branch
  | (K, .split (.pair v w) N) => some (K, Comp.subst v (Comp.subst (Val.shift w) N))  -- product
  | (K, .unfold (.fold v))    => some (K, .ret v)            -- μ: fold/unfold erase
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
