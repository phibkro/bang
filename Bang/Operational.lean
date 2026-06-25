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
  | .perform cap ℓ op w   => .perform cap ℓ op (Val.shiftFrom c w)
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
  | .perform cap ℓ op w   => .perform cap ℓ op (Val.substFrom k v w)
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

/-! ### 1.3b Subst-after-shift cancellation (the autosubst β-identity)

`substFrom k v (shiftFrom k t) = t` — UNCONDITIONALLY (no typing), for every term `t`, cutoff `k`,
and filler `v`. The standard de Bruijn "weaken-then-substitute is the identity" law (Pierce TAPL §6.2
shift/subst calculus; autosubst's `subst_shift`): the shift opens a fresh slot at level `k` that the
immediately-following subst-at-`k` fills back, and every other index round-trips through the
`if i < c`/`if i = k`/`if i > k` arithmetic to itself. It is the operational core of `seq_unit`:
`(Comp.shift c).subst v = c`, i.e. the `letC (ret v) (shift c) ↦ (shift c)[v] = c` head-reduction. -/
mutual
theorem Val.substFrom_shiftFrom (k : Nat) (v : Val) :
    ∀ t : Val, Val.substFrom k v (Val.shiftFrom k t) = t
  | .vunit       => rfl
  | .vint _      => rfl
  | .vvar i      => by
      -- i < k: shift fixes it (vvar i), then subst: i ≠ k and ¬ i > k ⇒ vvar i.
      -- i ≥ k: shift bumps to i+1, then subst: i+1 ≠ k and i+1 > k ⇒ vvar ((i+1)-1) = vvar i.
      by_cases hi : i < k
      · simp only [Val.shiftFrom, if_pos hi, Val.substFrom,
          if_neg (Nat.ne_of_lt hi), if_neg (Nat.not_lt.mpr (Nat.le_of_lt hi))]
      · simp only [Val.shiftFrom, if_neg hi, Val.substFrom,
          if_neg (by omega : i + 1 ≠ k), if_pos (by omega : i + 1 > k), Nat.add_sub_cancel]
  | .vthunk M    => by simp only [Val.shiftFrom, Val.substFrom, Comp.substFrom_shiftFrom k v M]
  | .inl w       => by simp only [Val.shiftFrom, Val.substFrom, Val.substFrom_shiftFrom k v w]
  | .inr w       => by simp only [Val.shiftFrom, Val.substFrom, Val.substFrom_shiftFrom k v w]
  | .pair w₁ w₂  => by
      simp only [Val.shiftFrom, Val.substFrom,
        Val.substFrom_shiftFrom k v w₁, Val.substFrom_shiftFrom k v w₂]
  | .fold w      => by simp only [Val.shiftFrom, Val.substFrom, Val.substFrom_shiftFrom k v w]

theorem Comp.substFrom_shiftFrom (k : Nat) (v : Val) :
    ∀ t : Comp, Comp.substFrom k v (Comp.shiftFrom k t) = t
  | .ret w       => by simp only [Comp.shiftFrom, Comp.substFrom, Val.substFrom_shiftFrom k v w]
  | .letC M N    => by
      simp only [Comp.shiftFrom, Comp.substFrom,
        Comp.substFrom_shiftFrom k v M, Comp.substFrom_shiftFrom (k + 1) (Val.shift v) N]
  | .force w     => by simp only [Comp.shiftFrom, Comp.substFrom, Val.substFrom_shiftFrom k v w]
  | .lam M       => by
      simp only [Comp.shiftFrom, Comp.substFrom, Comp.substFrom_shiftFrom (k + 1) (Val.shift v) M]
  | .app M w     => by
      simp only [Comp.shiftFrom, Comp.substFrom,
        Comp.substFrom_shiftFrom k v M, Val.substFrom_shiftFrom k v w]
  | .perform cap ℓ op w   => by simp only [Comp.shiftFrom, Comp.substFrom, Val.substFrom_shiftFrom k v w]
  | .handle h M  => by
      simp only [Comp.shiftFrom, Comp.substFrom,
        Handler.substFrom_shiftFrom k v h, Comp.substFrom_shiftFrom k v M]
  | .case w N₁ N₂ => by
      simp only [Comp.shiftFrom, Comp.substFrom, Val.substFrom_shiftFrom k v w,
        Comp.substFrom_shiftFrom (k + 1) (Val.shift v) N₁,
        Comp.substFrom_shiftFrom (k + 1) (Val.shift v) N₂]
  | .split w N   => by
      simp only [Comp.shiftFrom, Comp.substFrom, Val.substFrom_shiftFrom k v w,
        Comp.substFrom_shiftFrom (k + 2) (Val.shift (Val.shift v)) N]
  | .unfold w    => by simp only [Comp.shiftFrom, Comp.substFrom, Val.substFrom_shiftFrom k v w]
  | .oom         => rfl
  | .wrong _     => rfl

theorem Handler.substFrom_shiftFrom (k : Nat) (v : Val) :
    ∀ h : Handler, Handler.substFrom k v (Handler.shiftFrom k h) = h
  | .state ℓ s       => by simp only [Handler.shiftFrom, Handler.substFrom, Val.substFrom_shiftFrom k v s]
  | .throws _        => rfl
  -- heap left untouched by both shift and subst (closed cells, ADR-0030) ⇒ identity is definitional.
  | .transaction _ _ => rfl
end

/-- `(Comp.shift c).subst v = c` — the cutoff-0 instance of `Comp.substFrom_shiftFrom`, the exact
shape `seq_unit` needs for the `letC (ret v) (shift c) ↦ c` head-reduction. -/
theorem Comp.subst_shift (v : Val) (c : Comp) : Comp.subst v (Comp.shift c) = c :=
  Comp.substFrom_shiftFrom 0 v c


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

/-- The label a handler discharges (its first field). `handlesOp h ℓ op = true → h.label = ℓ`. -/
def Handler.label : Handler → Label
  | .throws ℓ => ℓ
  | .state ℓ _ => ℓ
  | .transaction ℓ _ => ℓ

/-- Does handler `h` catch operation `(ℓ, op)`? -/
def handlesOp : Handler → Label → OpId → Bool
  | .throws ℓ',   ℓ, op => (ℓ' = ℓ) && (op == "raise")
  | .state  ℓ' _, ℓ, op => (ℓ' = ℓ) && (op == "get" || op == "put")
  -- transaction (ADR-0030): catches the three stm ops on its own label.
  | .transaction ℓ' _, ℓ, op =>
      (ℓ' = ℓ) && (op == "newTVar" || op == "readTVar" || op == "writeTVar")

/-- `handlesOp` forces the label match: a catching handler's `label` IS the dispatched `ℓ`. -/
theorem handlesOp_label {h : Handler} {ℓ : Label} {op : OpId} (hc : handlesOp h ℓ op = true) :
    h.label = ℓ := by
  cases h <;> simp only [handlesOp, Bool.and_eq_true, decide_eq_true_eq] at hc <;>
    simp only [Handler.label] <;> exact hc.1

/-- Split a stack at the nearest frame catching `(ℓ, op)`: returns `(Kᵢ, h, Kₒ)` with
`K = Kᵢ ++ handleF h :: Kₒ`, `Kᵢ` containing no catching frame (the inner captured continuation),
and `h` the catching handler. `none` = no handler in `K` (unhandled). The recursion is the SAME walk
ADR-0023's `dispatch` did; it now also RETURNS the inner prefix `Kᵢ` (kept by `state`, discarded by
`throws`).

ADR-0045 1b: `splitAt` is now LEGACY for `Source.step` (which dispatches via `staticSplit`), but
STAYS because the CalcVM's `unwindFind` analogue + the LR's `krelS_splitAt_decomp` still reference its
shape (B2/B3 re-index them onto `staticSplit`). -/
def splitAt : EvalCtx → Label → OpId → Option (EvalCtx × Handler × EvalCtx)
  | [], _, _ => none
  | (.handleF h :: K), ℓ, op =>
      if handlesOp h ℓ op then some ([], h, K)
      else (splitAt K ℓ op).map (fun (Kᵢ, h', Kₒ) => (Frame.handleF h :: Kᵢ, h', Kₒ))
  | (fr :: K), ℓ, op =>
      (splitAt K ℓ op).map (fun (Kᵢ, h', Kₒ) => (fr :: Kᵢ, h', Kₒ))

/-! ### STATIC dispatch (ADR-0045 1b) — capability-passing, label-blind

`staticSplit K cap` walks OUT `cap`-many `handleF` frames; the `(cap+1)`-th `handleF` IS the handler,
taken WITHOUT a `handlesOp` test (the capability already named it). `letF`/`appF` frames are part of
the captured continuation and skipped transparently. Returns `(Kᵢ, h, Kₒ)` exactly like `splitAt`, so
`dispatchOn` (which routes by the RESOLVED handler `h`, label-carrying) is unchanged. Lifted verbatim
from `static-dispatch-spike` (`Bang/StaticSpike.lean`). -/
def staticSplit : EvalCtx → Nat → Option (EvalCtx × Handler × EvalCtx)
  | [], _ => none
  | (.handleF h :: K), 0 => some ([], h, K)              -- THIS handler: cap exhausted, take it
  | (.handleF h :: K), (c+1) =>                          -- skip one handler frame (cap counts down)
      (staticSplit K c).map (fun (Kᵢ, h', Kₒ) => (Frame.handleF h :: Kᵢ, h', Kₒ))
  | (fr :: K), c =>                                      -- non-handler frame: transparent, keep walking
      (staticSplit K c).map (fun (Kᵢ, h', Kₒ) => (fr :: Kᵢ, h', Kₒ))

/-- The cap resolves to an in-scope handler frame: walking out `cap`-many `handleF` frames reaches a
`handleF`. Non-`handleF` frames are transparent. This is `staticSplit`'s well-scopedness SIDE — a pure
`Nat`/`List` structural recursion, decidable (no polymorphism). Lifted from `setrow-tension-spike`. -/
def CapResolves : EvalCtx → Nat → Prop
  | [], _ => False                                   -- ran off the stack: out of scope
  | (.handleF _ :: _), 0 => True                     -- cap exhausted AT a handler: in scope
  | (.handleF _ :: K), (c+1) => CapResolves K c      -- skip one handler, cap counts down
  | (_ :: K), c => CapResolves K c                   -- transparent frame: keep walking

/-- The kind-match refinement: the resolved handler handles `(ℓ, op)` (the RIGHT kind). Reuses the real
`handlesOp`. Lifted from `setrow-tension-spike`. -/
def CapResolvesKind : EvalCtx → Nat → Label → OpId → Prop
  | [], _, _, _ => False
  | (.handleF h :: _), 0, ℓ, op => handlesOp h ℓ op = true
  | (.handleF _ :: K), (c+1), ℓ, op => CapResolvesKind K c ℓ op
  | (_ :: K), c, ℓ, op => CapResolvesKind K c ℓ op

/-- ◊4.5b-answertrack SCOPED-SEAM (ADR-0043): `(ℓ, op)` does NOT "pass through" a non-catching handler
before reaching its catcher — the captured continuation up to the catching handler contains NO handler
frame. Mirrors `splitAt`'s recursion: a `handleF h` frame must either CATCH `(ℓ, op)` (split point,
`Kᵢ = []`) or have NO catcher below it (`splitAt K = none`, op unhandled = stuck). The EXCLUDED edge
(`splitAt`-wrap-MISS) is exactly `¬ NoWrapMiss`: a non-catching `handleF` with a deeper catcher — the
captured continuation then wraps that handler, the inverse-strip case `krelS_splitAt_decomp` cannot
certify (answer-determinism FALSE). COVERED: every op caught by the NEAREST enclosing handler. -/
def NoWrapMiss : EvalCtx → Label → OpId → Prop
  | [], _, _ => True
  | (.handleF h :: K), ℓ, op =>
      handlesOp h ℓ op = true ∨ splitAt K ℓ op = none
  | (_ :: K), ℓ, op => NoWrapMiss K ℓ op

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
            -- read (ADR-0030 amendment, TVarRef = int, TOTAL store): payload `vint i`; return cell `i`,
            -- or the DEFAULT `vint 0` if out of range. NEVER ooms — `oom` is the fuel sentinel, so a
            -- bad read producing it would be untypable (preservation gap). The store is conceptually a
            -- total `Loc → Val` map (`getD` with `vint 0`); source refs come only from `newTVar`, so
            -- the default path is source-unreachable but kernel-total. Heap unchanged on read.
            some (Kᵢ ++ Frame.handleF (.transaction ℓ' Θ) :: Kₒ,
                  .ret (Θ.getD ((tvarIdx v).getD 0) (.vint 0)))
          else
            -- writeTVar (ADR-0030, total store): payload `pair (vint i) w`; store `w` at cell `i`, return
            -- unit. `storeSet`/`List.set` is a no-op out of range, so this is TOTAL and never ooms. A
            -- malformed payload (not `pair (vint _) _`) is a type-safe no-op resume (source-unreachable
            -- since the payload type is `prod int S`).
            match v with
            | .pair iv w =>
                some (Kᵢ ++ Frame.handleF (.transaction ℓ' (storeSet Θ ((tvarIdx iv).getD 0) w)) :: Kₒ,
                      .ret .vunit)
            | _ => some (Kᵢ ++ Frame.handleF (.transaction ℓ' Θ) :: Kₒ, .ret .vunit)

def dispatch (K : EvalCtx) (ℓ : Label) (op : OpId) (v : Val) : Option Config :=
  (splitAt K ℓ op).bind (dispatchOn op v)

/-- STATIC dispatch (ADR-0045 1b): resolve the handler by CAPABILITY (`staticSplit K cap`), then route
the resolved `(Kᵢ, h, Kₒ)` through the UNCHANGED `dispatchOn` (which reads the handler's kind/label).
This is what `Source.step` now uses for `perform`; `dispatch` (label search) is retired to legacy. -/
def staticDispatch (K : EvalCtx) (cap : Nat) (op : OpId) (v : Val) : Option Config :=
  (staticSplit K cap).bind (dispatchOn op v)

/-! ### Well-capped judgement (ADR-0045 B3a) — the cap-scoping invariant `HasConfig` carries

★★ B3a SECOND WALL (build-grounded, BLOCKS preservation) — caps must be LEXICAL, not dynamic. ★★
This `WellCapped` predicate is the CORRECT invariant shape, but it is NOT preserved under `Source.step`
while `Comp.subst`/`shiftFrom` leave the `cap` field UNSHIFTED. The decisive finding:
`WCVal Σ v → WCVal (handleF h :: Σ) v` is FALSE (build-confirmed `wc_fails_after_migration`) — a
thunk's `perform 0` ("nearest handler") that MIGRATES under a fresh `handle h` (via `letC`/β subst into
a `vvar 0` position beneath an `h`-wrapper) now resolves to `h`, the WRONG handler. A reachable
well-typed program then DIVERGES: `handle (state 1 5) (let c={get} in handle (throws 2) ($c))` yields a
WRONG value, not `5` (build-confirmed) — the get mis-dispatches to the inner `throws`. The OLD dynamic
LABEL search handled this correctly (it skipped the wrong-label `throws`); the static CAP does not,
because `perform 0` is dynamic-nearest, not lexical. FIX (build-confirmed `res5`): the cap must be
SHIFTED to skip handlers it crosses — i.e. `handle` must be a CAP-BINDER in `shiftFrom`/`substFrom`
(lexical capabilities, Lexa/Effekt-style). That is a kernel SUBSTITUTION change + an ADR decision,
beyond B3a's "minimal Σ" scope. REPORTED to lead; preservation of `WellCapped` resumes once caps are
lexical (then `WCVal Σ v → WCVal (handleF h::Σ) v` holds because the shifted cap compensates).

ORIGINAL B3a design intent (valid once caps are lexical):
The B1 wall: static dispatch needs every `perform cap`'s `cap` to RESOLVE (`CapResolvesKind`) against
the handler-context it faces at dispatch, but typing is cap-irrelevant, so this must enter as a
SEPARATE structural invariant. `WellCapped` is that invariant. It is folded INTO `HasConfig` (so the
frozen `preservation`/`progress` statements stand byte-identical) and added as a premise to
`type_safety` (the only frozen statement over `HasCTy [] []` rather than `HasConfig`).

`Σ : EvalCtx` is the handler-context a computation faces — innermost-first, exactly the runtime stack
a focus dispatches against. `WCComp Σ M` checks every `perform` in `M` against `Σ` extended by the
syntactic `handle` wrappers above it (a `handle h M'` pushes `handleF h` onto `Σ` for `M'`). The cap
counts only `handleF` frames (it skips letF/appF — `CapResolvesKind`), so threading the full `Σ`
(handlers + plumbing) is faithful: a stored `letF`/`appF` continuation is checked against the SAME `Σ`
it will face when it becomes the focus (the intervening plumbing frame is popped first). -/

mutual
/-- Every `perform` in `M` resolves (kind-correctly) against the handler-context `Sg` extended by `M`'s
own enclosing `handle` wrappers. Structural recursion mirroring `Comp`; `handle h M'` extends `Sg` with
`handleF h`. `letC`/`app`/`case`/`split` descend with `Sg` unchanged (their frames are cap-transparent,
so a perform buried under them dispatches against the same `Sg`). -/
def WCComp (Sg : EvalCtx) : Comp → Prop
  | .ret v          => WCVal Sg v
  | .letC M N       => WCComp Sg M ∧ WCComp Sg N
  | .force v        => WCVal Sg v
  | .lam M          => WCComp Sg M
  | .app M v        => WCComp Sg M ∧ WCVal Sg v
  | .perform cap ℓ op v => CapResolvesKind Sg cap ℓ op ∧ WCVal Sg v
  | .handle h M     => WCHandler Sg h ∧ WCComp (Frame.handleF h :: Sg) M
  | .case v N₁ N₂   => WCVal Sg v ∧ WCComp Sg N₁ ∧ WCComp Sg N₂
  | .split v N      => WCVal Sg v ∧ WCComp Sg N
  | .unfold v       => WCVal Sg v
  | .oom            => True
  | .wrong _        => True
/-- A value is well-capped iff every `Comp` it thunks is (a `vthunk M` faces a FRESH handler-context
when forced — the stack at its force site — so it is checked against `[]`, the empty context: a thunk
body's caps must be self-contained, since `force` discards the ambient stack for the thunk's own
dispatch... no: `force (vthunk M)` steps to `(K, M)`, so `M` faces the AMBIENT `K`. Hence check against
`Sg`.). -/
def WCVal (Sg : EvalCtx) : Val → Prop
  | .vunit       => True
  | .vint _      => True
  | .vvar _      => True
  | .vthunk M    => WCComp Sg M
  | .inl w       => WCVal Sg w
  | .inr w       => WCVal Sg w
  | .pair w₁ w₂  => WCVal Sg w₁ ∧ WCVal Sg w₂
  | .fold w      => WCVal Sg w
/-- A handler's payload value is well-capped (state's stored value, transaction's heap cells). -/
def WCHandler (Sg : EvalCtx) : Handler → Prop
  | .throws _       => True
  | .state _ s      => WCVal Sg s
  | .transaction _ Θ => ∀ c ∈ Θ, WCVal Sg c
end

/-- A frame STACK is well-capped: each stored continuation/argument/handler is well-capped against the
context BELOW it (the tail it will face after the frame is consumed). Innermost-first: the head frame
sits on `K`, so its payload faces `K` (a `letF N` continuation `N`, once reached, dispatches against
`K`; an `appF v` argument is a value; a `handleF h` payload faces `K`). -/
def WCStack : EvalCtx → Prop
  | [] => True
  | .letF N :: K   => WCComp K N ∧ WCStack K
  | .appF v :: K   => WCVal K v ∧ WCStack K
  | .handleF h :: K => WCHandler K h ∧ WCStack K

/-- The config-level well-capped invariant: the focus is well-capped against the stack, and the stack's
stored continuations are well-capped against their tails. This is what `HasConfig` carries (B3a). -/
def WellCapped : Config → Prop
  | (K, M) => WCComp K M ∧ WCStack K

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
  -- DISPATCH (ADR-0045 1b): STATIC — resolve by `cap`, route by resolved handler. `ℓ` is now inert in
  -- the STEP (it lives in the row + on the resolved handler); `staticDispatch` uses `cap`, not `ℓ`.
  | (K, .perform cap _ op v)  => staticDispatch K cap op v
  -- stuck
  | _                       => none

/-- Fill a single frame's hole with a focus — the one-step node a `plug` builds for a frame, and
the redex a PUSH step undoes (`step (K, fr.wrapStep c) = (fr :: K, c)`). -/
def Frame.wrapStep : Frame → Comp → Comp
  | .letF N,    c => .letC c N
  | .appF v,    c => .app c v
  | .handleF h, c => .handle h c

/-- Plug a focus back into its evaluation context (the inverse of decomposition). -/
def plug : EvalCtx → Comp → Comp
  | [], c            => c
  | .letF N :: K, c  => plug K (.letC c N)
  | .appF v :: K, c  => plug K (.app c v)
  | .handleF h :: K, c => plug K (.handle h c)

/-- `plug` peels its head frame via `wrapStep` (the structural identity `run_plug` inducts on). -/
theorem plug_cons (fr : Frame) (K : EvalCtx) (c : Comp) :
    plug (fr :: K) c = plug K (fr.wrapStep c) := by cases fr <;> rfl

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

/-- `Config.run` unfolds one step on a NON-returning config: when `cfg` is not `([], ret v)` the
machine takes a `Source.step`. Bridges the equation compiler's overlapping `([], ret v)` /
catch-all arms so callers can reason about a single transition. -/
theorem Config.run_step (n : Nat) (cfg : Config)
    (hne : ∀ v, cfg ≠ ([], Comp.ret v)) :
    Config.run (n + 1) cfg =
      (match Source.step cfg with | some cfg' => Config.run n cfg' | none => .stuck) := by
  obtain ⟨K, c⟩ := cfg
  match K, c with
  | [], .ret v => exact absurd rfl (hne v)
  | [], .letC _ _ | [], .app _ _ | [], .handle _ _ | [], .force _ | [], .perform _ _ _ _
  | [], .lam _ | [], .case _ _ _ | [], .split _ _ | [], .unfold _ | [], .oom | [], .wrong _
  | _ :: _, _ => rfl

/-- Fuel monotonicity: a config that runs to `done w` keeps running to `done w` with MORE fuel.
Standard "more fuel never hurts a terminating run" — induct on `n`, threading the single transition
through `Config.run_step`. -/
theorem Config.run_done_add (k : Nat) :
    ∀ (n : Nat) (cfg : Config) (w : Val),
      Config.run n cfg = Result.done w → Config.run (n + k) cfg = Result.done w := by
  intro n
  induction n with
  | zero => intro cfg w h; rw [show Config.run 0 cfg = Result.oom from rfl] at h; exact absurd h (by simp)
  | succ m ih =>
    intro cfg w h
    by_cases hret : ∃ v, cfg = ([], Comp.ret v)
    · obtain ⟨v, rfl⟩ := hret
      -- ([], ret v): both runs hit the `done` arm; (m+1)+k = (m+k)+1 still returns v.
      have hwv : Result.done w = Result.done v := by
        rw [← h]; rfl
      rw [show m + 1 + k = (m + k) + 1 by omega]
      show Result.done v = Result.done w
      exact hwv.symm
    · push_neg at hret
      rw [Config.run_step m cfg hret] at h
      rw [show m + 1 + k = (m + k) + 1 by omega, Config.run_step (m + k) cfg hret]
      cases hstep : Source.step cfg with
      | none => rw [hstep] at h; exact absurd h (by simp)
      | some cfg' =>
          rw [hstep] at h
          show Config.run (m + k) cfg' = Result.done w
          exact ih cfg' w h

-- Trace / evalTrace: still axiom; need concrete Eff to express
-- "label in row" (see `docs/notes/OPEN_QUESTIONS.md` Q1).
axiom Trace            : Type
axiom Source.evalTrace : Nat → Comp → Result (Val × Trace)
axiom traceWithin      {Eff : Type} : Trace → Eff → Prop

/-- isReturn: a Comp is "returned" iff it's `ret v` for some v. -/
def isReturn : Comp → Prop
  | .ret _ => True
  | _      => False

-- `NotEvaluated` (the coeffect-erasure notion: de Bruijn index `i`'s binder is never *evaluated*)
-- is DEFINED in `Bang/LR.lean` (§5.0b), where the observational equivalence `≈` it is phrased over
-- lives. A 0-graded var is still SUBSTITUTED syntactically (and type-checks — QTT permits 0-graded
-- occurrences); only its *evaluation* is absent, so the faithful notion is semantic, not structural.

end Bang
