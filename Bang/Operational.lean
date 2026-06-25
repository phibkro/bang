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
  | .vcap n ℓ    => .vcap n ℓ                          -- a capability is a closed identity (no var)
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
  | .perform cp op w   => .perform (Val.shiftFrom c cp) op (Val.shiftFrom c w)  -- cap is a value (ADR-0054)
  | .handle h M  => .handle (Handler.shiftFrom c h) (Comp.shiftFrom (c + 1) M)  -- handle BINDS the cap at 0
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
  | .vcap n ℓ    => .vcap n ℓ                  -- a capability is a closed identity (no var to subst)
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
  | .perform cp op w   => .perform (Val.substFrom k v cp) op (Val.substFrom k v w)  -- cap is a value (ADR-0054)
  -- ADR-0054: `handle` BINDS the capability at index 0, so `M` substitutes at the shifted cutoff `k+1`
  -- with the lifted filler (exactly like `lam`/`letC`). The capability reference is an ordinary value
  -- (`vvar`/`vcap`), so it rides substitution UNCHANGED — no special cap-shift (that machinery is gone).
  | .handle h M  => .handle (Handler.substFrom k v h) (Comp.substFrom (k + 1) (Val.shift v) M)
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
  | .vcap _ _    => rfl
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
  | .perform cp op w   => by simp only [Comp.shiftFrom, Comp.substFrom,
      Val.substFrom_shiftFrom k v cp, Val.substFrom_shiftFrom k v w]
  | .handle h M  => by
      -- ADR-0054: `handle` binds the capability ⇒ body recurses at `k+1` with the lifted filler (like `lam`).
      simp only [Comp.shiftFrom, Comp.substFrom,
        Handler.substFrom_shiftFrom k v h, Comp.substFrom_shiftFrom (k + 1) (Val.shift v) M]
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
  | (.handleF m h :: K), ℓ, op =>
      if handlesOp h ℓ op then some ([], h, K)
      else (splitAt K ℓ op).map (fun (Kᵢ, h', Kₒ) => (Frame.handleF m h :: Kᵢ, h', Kₒ))
  | (fr :: K), ℓ, op =>
      (splitAt K ℓ op).map (fun (Kᵢ, h', Kₒ) => (fr :: Kᵢ, h', Kₒ))

/-- ADR-0054 IDENTITY dispatch: split the stack at the `handleF` whose IDENTITY is `n` (the capability's
generative name). Unlike `splitAt`'s label search, this MATCHES the unique identity — migration-invariant
(a match never re-counts, so it never shifts). Mirror of `scratch/IdentityKernelProbe.splitAtId`. -/
def splitAtId : EvalCtx → Nat → Option (EvalCtx × Handler × EvalCtx)
  | [], _ => none
  | (.handleF m h :: K), n =>
      if m = n then some ([], h, K)
      else (splitAtId K n).map (fun x => (Frame.handleF m h :: x.1, x.2.1, x.2.2))
  | (fr :: K), n => (splitAtId K n).map (fun x => (fr :: x.1, x.2.1, x.2.2))

/-- ◊4.5b-answertrack SCOPED-SEAM (ADR-0043): `(ℓ, op)` does NOT "pass through" a non-catching handler
before reaching its catcher — the captured continuation up to the catching handler contains NO handler
frame. Mirrors `splitAt`'s recursion: a `handleF h` frame must either CATCH `(ℓ, op)` (split point,
`Kᵢ = []`) or have NO catcher below it (`splitAt K = none`, op unhandled = stuck). The EXCLUDED edge
(`splitAt`-wrap-MISS) is exactly `¬ NoWrapMiss`: a non-catching `handleF` with a deeper catcher — the
captured continuation then wraps that handler, the inverse-strip case `krelS_splitAt_decomp` cannot
certify (answer-determinism FALSE). COVERED: every op caught by the NEAREST enclosing handler. -/
def NoWrapMiss : EvalCtx → Label → OpId → Prop
  | [], _, _ => True
  | (.handleF _ h :: K), ℓ, op =>
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
def dispatchOn (n : Nat) (op : OpId) (v : Val) : EvalCtx × Handler × EvalCtx → Option Config
  | (Kᵢ, h, Kₒ) =>
      match h with
      | .throws _   => some (Kₒ, .ret v)                                        -- ABORT
      | .state ℓ' s =>
          if op == "get" then
            some (Kᵢ ++ Frame.handleF n (.state ℓ' s) :: Kₒ, .ret s)             -- RESUME with s
          else
            some (Kᵢ ++ Frame.handleF n (.state ℓ' v) :: Kₒ, .ret .vunit)        -- RESUME with unit
      -- transaction (ADR-0030): the multi-cell generalization of `state`. RESUME threading the
      -- updated heap (KEEP `Kᵢ`, reinstall a deep `transaction ℓ' Θ'` frame), exactly the ADR-0025
      -- state-resume pattern with a list-heap. Rollback is FREE: an abort is a zero-shot `throws`
      -- that escapes this frame (handled by the throws arm above over a DIFFERENT label), so the
      -- threaded `Θ'` is discarded with the frame and never commits.
      | .transaction ℓ' Θ =>
          if op == "newTVar" then
            -- allocate: append the initial value `v`; the new TVar's index is the old length.
            some (Kᵢ ++ Frame.handleF n (.transaction ℓ' (Θ ++ [v])) :: Kₒ, .ret (.vint Θ.length))
          else if op == "readTVar" then
            -- read (ADR-0030 amendment, TVarRef = int, TOTAL store): payload `vint i`; return cell `i`,
            -- or the DEFAULT `vint 0` if out of range. NEVER ooms — `oom` is the fuel sentinel, so a
            -- bad read producing it would be untypable (preservation gap). The store is conceptually a
            -- total `Loc → Val` map (`getD` with `vint 0`); source refs come only from `newTVar`, so
            -- the default path is source-unreachable but kernel-total. Heap unchanged on read.
            some (Kᵢ ++ Frame.handleF n (.transaction ℓ' Θ) :: Kₒ,
                  .ret (Θ.getD ((tvarIdx v).getD 0) (.vint 0)))
          else
            -- writeTVar (ADR-0030, total store): payload `pair (vint i) w`; store `w` at cell `i`, return
            -- unit. `storeSet`/`List.set` is a no-op out of range, so this is TOTAL and never ooms. A
            -- malformed payload (not `pair (vint _) _`) is a type-safe no-op resume (source-unreachable
            -- since the payload type is `prod int S`).
            match v with
            | .pair iv w =>
                some (Kᵢ ++ Frame.handleF n (.transaction ℓ' (storeSet Θ ((tvarIdx iv).getD 0) w)) :: Kₒ,
                      .ret .vunit)
            | _ => some (Kᵢ ++ Frame.handleF n (.transaction ℓ' Θ) :: Kₒ, .ret .vunit)

/-- ADR-0054: the kernel's effect dispatch — resolve the capability's IDENTITY `n`, then route the
matched `(Kᵢ, h, Kₒ)` through `dispatchOn n` (which reinstalls `handleF n` on a resumptive RESUME). -/
def idDispatch (K : EvalCtx) (n : Nat) (op : OpId) (v : Val) : Option Config :=
  (splitAtId K n).bind (dispatchOn n op v)

/-! ### Absolute (level-from-root) cap resolution (ADR-0053).

The cap field of `perform` is a ROOT-LEVEL (counted from the program root / stack bottom; `lvl = 0`
is the OUTERMOST handler), NOT a de-Bruijn outward index. Root-levels are migration-INVARIANT: a
cap-carrying thunk cannot escape its handler (the `LWT` return-escape gate, ADR-0045 D), so a pending
`perform`'s target handler is always still on the stack when it fires, and migration only pushes
handlers ABOVE the target — never pops below it. So crossing a `handle` does NOT shift the cap
(`Comp.substFrom` leaves it untouched), which DISSOLVES the de-Bruijn shift wall (ADR-0050) by
construction. Resolution converts the root-level to the top-index `staticSplit` consumes:
`topIndex = handlerCount K - 1 - lvl`. The conversion modulus is `handlerCount` (= `handlersOf` length,
the single source of truth — `handlerCount_eq_handlersOf_length`). Verified sorry-free in the de-risk
probe (`scratch/AbsoluteCapsStepProbe.lean`); the bricks live in `Metatheory.lean`. -/

/-- Number of `handleF` frames in a context — the level↔index conversion modulus. Equal to
`(handlersOf K).length` (`handlerCount_eq_handlersOf_length`), so the modulus reuses the existing
handler skeleton rather than introducing a second notion. -/
def handlerCount : EvalCtx → Nat
  | [] => 0
  | .handleF _ _ :: K => handlerCount K + 1
  | .letF _ :: K => handlerCount K
  | .appF _ :: K => handlerCount K

@[simp] theorem handlerCount_letF (N : Comp) (K : EvalCtx) :
    handlerCount (Frame.letF N :: K) = handlerCount K := rfl
@[simp] theorem handlerCount_appF (v : Val) (K : EvalCtx) :
    handlerCount (Frame.appF v :: K) = handlerCount K := rfl
@[simp] theorem handlerCount_handleF (n : Nat) (h : Handler) (K : EvalCtx) :
    handlerCount (Frame.handleF n h :: K) = handlerCount K + 1 := rfl

/-- Resolve an absolute root-LEVEL against the runtime stack: convert to the top-index `staticSplit`
expects (`handlerCount K - 1 - lvl`), then reuse `staticSplit`. `lvl < handlerCount K` is
well-scopedness (an in-range level always resolves — `absSplit_isSome_of_lt`). -/
def handlersOf : EvalCtx → EvalCtx
  | [] => []
  | .handleF n h :: K => Frame.handleF n h :: handlersOf K
  | .letF _ :: K => handlersOf K
  | .appF _ :: K => handlersOf K

/-- `handlersOf` distributes over append. -/
theorem handlersOf_append (K K' : EvalCtx) : handlersOf (K ++ K') = handlersOf K ++ handlersOf K' := by
  induction K with
  | nil => rfl
  | cons fr K ih => cases fr <;> simp only [handlersOf, List.cons_append, ih]

/-- `handlersOf` preserves the handler count (it drops only `letF`/`appF`, keeps every `handleF`). -/
theorem handlerCount_handlersOf (K : EvalCtx) : handlerCount (handlersOf K) = handlerCount K := by
  induction K with
  | nil => rfl
  | cons fr K ih => cases fr <;> simp [handlersOf, handlerCount, ih]

theorem handlerCount_eq_handlersOf_length (K : EvalCtx) :
    handlerCount K = (handlersOf K).length := by
  induction K with
  | nil => rfl
  | cons fr K ih => cases fr <;> simp [handlerCount, handlersOf, ih]



/-- **The non-escape invariant** (ADR-0054 COLLAPSE). Under capability-passing, cap-resolution is a
TYPING property (`c : Cap ℓ` + lexical scope ⟹ the binding `handle` encloses the `perform` ⟹ its handler
is on the stack), so the positional `WellCapped`/`LWConfig` invariant DISSOLVES into the type system. The
SOLE remaining structural obligation is NON-ESCAPE: a capability does not outlive its handler's dynamic
extent. **FIRST CUT = `True`** — inc 4 (Metatheory) pins the exact form, revealed by what `preservation`/
`progress` need (the thunk-escape case is the subtle part — the old `preservation_returnEscape_TODO`,
now the whole invariant rather than one clause). See ADR-0054 amendment. -/
def NonEscape (_cfg : Config) : Prop := True

/-- **Configuration typing** (ADR-0054 COLLAPSE): the typing CORE (`HasConfigTy`) PLUS the `NonEscape`
invariant (replacing the positional `LWConfig`, which is now subsumed by typing — the capability's `Cap ℓ`
type carries the resolution). Folding it in HERE keeps the frozen `preservation`/`progress` statements —
stated over `HasConfig` — BYTE-IDENTICAL. -/
def HasConfig [EffSig Eff Mult] (cfg : Config) (eo : Eff) (Co : CTy Eff Mult) : Prop :=
  HasConfigTy cfg eo Co ∧ NonEscape cfg


/-! ### WC under VARIABLE shift + substitution (ADR-0045 B3a)

`WCComp`/`WCVal` read the context only via caps, which the VARIABLE shift/subst never touch — so they
are invariant under `shiftFrom` (var shift). And `handlesOp` is invariant under `substFrom` (subst
changes only handler payloads). These feed the substitution lemma. -/

@[simp] theorem handlesOp_substFrom (k : Nat) (v : Val) (h : Handler) (ℓ : Label) (op : OpId) :
    handlesOp (Handler.substFrom k v h) ℓ op = handlesOp h ℓ op := by cases h <;> rfl


/-- One machine transition. `none` = stuck (terminal `⟨[], ret v⟩`, or genuinely wrong). -/
def Source.step : Config → Option Config
  -- PUSH
  | (K, .letC M N)          => some (.letF N :: K, M)
  | (K, .app M v)           => some (.appF v :: K, M)
  | (K, .handle h M)        =>
      -- ADR-0054: mint a fresh identity `n = handlerCount K` (Fork ii), push `handleF n h`, and
      -- substitute the capability value `vcap n h.label` for the handle-bound var 0 in the body.
      some (.handleF (handlerCount K) h :: K, Comp.subst (.vcap (handlerCount K) h.label) M)
  | (K, .force (.vthunk M)) => some (K, M)
  -- REDUCE
  | (.letF N :: K, .ret v)  => some (K, Comp.subst v N)
  | (.appF v :: K, .lam M)  => some (K, Comp.subst v M)
  | (.handleF _ _ :: K, .ret v) => some (K, .ret v)
  -- ADT eliminators (ADR-0029): scrutinees are values, so these reduce in place.
  | (K, .case (.inl v) N₁ _)  => some (K, Comp.subst v N₁)   -- sum: left branch
  | (K, .case (.inr v) _ N₂)  => some (K, Comp.subst v N₂)   -- sum: right branch
  | (K, .split (.pair v w) N) => some (K, Comp.subst v (Comp.subst (Val.shift w) N))  -- product
  | (K, .unfold (.fold v))    => some (K, .ret v)            -- μ: fold/unfold erase
  -- DISPATCH (ADR-0054): IDENTITY — the capability `vcap n _` names handler `n`; match it, route by the
  -- resolved handler (`dispatchOn` reinstalls `handleF n` on a resumptive resume).
  | (K, .perform (.vcap n _) op v) => idDispatch K n op v
  -- stuck
  | _                       => none

/-- Fill a single frame's hole with a focus — the one-step node a `plug` builds for a frame, and
the redex a PUSH step undoes (`step (K, fr.wrapStep c) = (fr :: K, c)`). -/
def Frame.wrapStep : Frame → Comp → Comp
  | .letF N,    c => .letC c N
  | .appF v,    c => .app c v
  | .handleF _ h, c => .handle h c

/-- Plug a focus back into its evaluation context (the inverse of decomposition). -/
def plug : EvalCtx → Comp → Comp
  | [], c            => c
  | .letF N :: K, c  => plug K (.letC c N)
  | .appF v :: K, c  => plug K (.app c v)
  | .handleF _ h :: K, c => plug K (.handle h c)

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

/-- **THE typed return-escape obligation (ADR-0045 R1, the documented scoped sorry).**

`LWConfig` is preserved by every non-`handleF`-ret `Source.step` transition. The cases divide:

  • **FORCED-thunk fragment** (PUSH letC/app/handle · force · the β-redexes case/split/lam/unfold ·
    letF-ret of a CAPABILITY-FREE value): these THREAD — a capability whose thunk is FORCED (or a value
    that carries none) re-establishes `LWConfig` via `LWT`-substitution (the cap-shift keystone handles
    migration; cf. the `WCComp.subst` machinery). The cap-assignment suite (ADR-0045 Resolution
    evidence) confirms this fragment is accepted: capMigrate / cellComp / stateCell / throws / the STM
    ledger all stay well-typed.

  • **RETURN-ESCAPE of a CAPABILITY-CARRYING value** (a `ret`/`letF`-ret threading a value whose thunk
    holds a LIVE-effect cap PAST its handler): the seqEscape/ledger FORK. Build-settled (ADR-0045
    Resolution): a purely UNTYPED config invariant CANNOT certify it without OVER-rejecting the safe
    ledger (which returns a cap-FREE `vint` out of a `transaction`) — the distinction is the escaping
    value's TYPE (`U φ C` with `φ ≠ ⊥` vs `int`/`unit`). The non-escape check is therefore TYPE-DIRECTED
    and belongs in the typed-LR re-index (`Vτ/Cτ/Tτ`), a type-premise on `ret`/`letC` constraining ONLY
    `U φ C` values. (A) lazy refuted (`progB` well-typed-but-stuck); (C) untyped tightening over-rejects
    the ledger; (D) typed adopted.

The single scoped boundary: `preservation_proof`'s `LWConfig` re-establishment routes here for the
non-`handleF`-ret cases. Its `sorry` is the typed-LR obligation — a deferred type-premise (ADR-0045
Resolution + `paths/PATH-cap-assignment-spike.md` NEXT), NOT a wall. `handleF_ret` (by construction)
and `progress_proof` are axiom-clean and independent of it. -/
theorem preservation_returnEscape_TODO
    {cfg cfg' : Config} (_hne : NonEscape cfg) (_hstep : Source.step cfg = some cfg') :
    NonEscape cfg' := trivial   -- ADR-0054 inc 3: NonEscape := True (first cut); inc 4 gives it real content

/-! ### Lexical-cap regression demos (ADR-0045 amendment) — REAL artifacts, build-gated.

These `#guard`s are the migration-is-correct evidence (ADR-0054). The `get`-thunk's capability is a
`vvar` bound by its target `handle`; forced under unrelated `throws` handlers, identity dispatch reaches
the right handler by MATCH (no re-count → migration-invariant). `handle` BINDS a capability at index 0,
so de-Bruijn indices count it. Labels are `Nat` (`EffectRow.Label`). -/

/-- `Source.eval` yields exactly `done (vint n)` (Bool; `Result`/`Val` derive only `Inhabited`). -/
private def yieldsInt (fuel : Nat) (c : Comp) (n : Int) : Bool :=
  match Source.eval fuel c with | .done (.vint m) => m == n | _ => false

/-- 1-deep migration: a `{get}` thunk targeting the OUTER state (its cap = `vvar 0` in the state's body),
forced under one fresh `throws`; identity dispatch reaches the outer state = 5. -/
private def capMigrate1 : Comp :=
  .handle (.state 1 (.vint 5))
    (.letC (.ret (.vthunk (.perform (.vvar 0) "get" .vunit)))
      (.handle (.throws 2) (.force (.vvar 1))))
#guard yieldsInt 200 capMigrate1 5

/-- 2-deep migration: the thunk crosses TWO fresh `throws` handlers; identity dispatch still reaches the
outer state = 9 (a match never shifts, however deep the migration). -/
private def capMigrate2 : Comp :=
  .handle (.state 1 (.vint 9))
    (.letC (.ret (.vthunk (.perform (.vvar 0) "get" .vunit)))
      (.handle (.throws 2) (.handle (.throws 3) (.force (.vvar 2)))))
#guard yieldsInt 300 capMigrate2 9

/-- ★ THE INSERT-BELOW-TARGET WITNESS (the program that broke ABSOLUTE caps, ADR-0053): a thunk that
handles its OWN `state` and reads it, forced under an unrelated outer `throws`. Identity dispatch reaches
the thunk's OWN state = 7 (absolute caps mis-resolved this to the throws). The fix, in the kernel. -/
private def capMigrateInternal : Comp :=
  .app (.lam (.handle (.throws 2) (.force (.vvar 1))))
    (.vthunk (.handle (.state 1 (.vint 7)) (.perform (.vvar 0) "get" .vunit)))
#guard yieldsInt 200 capMigrateInternal 7

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
  | [], .letC _ _ | [], .app _ _ | [], .handle _ _ | [], .force _ | [], .perform _ _ _
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
