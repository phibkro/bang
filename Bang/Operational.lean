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

/-! ### Cap shift (ADR-0045 amendment) — `handle` is a CAP-BINDER, the de-Bruijn handler dimension.

The `cap` field of `perform` is a de-Bruijn index into the *handler* stack (it counts `handleF`
frames to its handler). Its binder is `handle`. So just as `shiftFrom` lifts a VARIABLE index when a
term crosses a `lam`/`letC` binder, `shiftCapFrom` lifts a CAP index when a term crosses a `handle`
binder. Applied to the filler `v` in the `handle` case of `substFrom` (below), it keeps static
dispatch SOUND under thunk migration (the B3a divergence). `d` is the handler-depth cutoff: a perform
with `cap ≥ d` targets an AMBIENT handler (outside the crossed `handle`) and bumps; `cap < d` targets a
handler INTERNAL to the term and is untouched. Variable binders (`letC`/`lam`/`case`/`split`) do NOT
change `d` (they add no handler); only `handle` increments it. Structural recursion (no `List.map` over
`Θ` — heap cells are closed, ADR-0030 — so the `rfl`-reduction the demos/metatheory rely on survives). -/
mutual
def Val.shiftCapFrom (d : Nat) : Val → Val
  | .vunit       => .vunit
  | .vint n      => .vint n
  | .vvar i      => .vvar i
  | .vthunk M    => .vthunk (Comp.shiftCapFrom d M)        -- a thunk adds no handler: same `d`
  | .inl w       => .inl (Val.shiftCapFrom d w)
  | .inr w       => .inr (Val.shiftCapFrom d w)
  | .pair w₁ w₂  => .pair (Val.shiftCapFrom d w₁) (Val.shiftCapFrom d w₂)
  | .fold w      => .fold (Val.shiftCapFrom d w)
def Comp.shiftCapFrom (d : Nat) : Comp → Comp
  | .ret w       => .ret (Val.shiftCapFrom d w)
  | .letC M N    => .letC (Comp.shiftCapFrom d M) (Comp.shiftCapFrom d N)    -- letC binds a VAR, not a handler
  | .force w     => .force (Val.shiftCapFrom d w)
  | .lam M       => .lam (Comp.shiftCapFrom d M)
  | .app M w     => .app (Comp.shiftCapFrom d M) (Val.shiftCapFrom d w)
  | .perform cap ℓ op w   =>
      .perform (if cap < d then cap else cap + 1) ℓ op (Val.shiftCapFrom d w)  -- bump ambient caps
  | .handle h M  => .handle (Handler.shiftCapFrom d h) (Comp.shiftCapFrom (d + 1) M)  -- handle BINDS a cap
  | .case w N₁ N₂ => .case (Val.shiftCapFrom d w) (Comp.shiftCapFrom d N₁) (Comp.shiftCapFrom d N₂)
  | .split w N   => .split (Val.shiftCapFrom d w) (Comp.shiftCapFrom d N)
  | .unfold w    => .unfold (Val.shiftCapFrom d w)
  | .oom         => .oom
  | .wrong s     => .wrong s
def Handler.shiftCapFrom (d : Nat) : Handler → Handler
  | .state ℓ s   => .state ℓ (Val.shiftCapFrom d s)
  | .throws ℓ    => .throws ℓ
  -- heap cells are CLOSED (ADR-0030) ⇒ no caps to shift; identity keeps structural recursion.
  | .transaction ℓ Θ => .transaction ℓ Θ
end

/-- `Val.shiftCap = Val.shiftCapFrom 0` — bump a value's ambient caps as it crosses ONE `handle`. -/
abbrev Val.shiftCap  : Val → Val  := Val.shiftCapFrom 0
abbrev Comp.shiftCap : Comp → Comp := Comp.shiftCapFrom 0

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
  -- ADR-0045 amendment: `handle` BINDS a capability. The filler `v` crosses into `M` under one extra
  -- `handleF h` frame, so its ambient caps bump (`Val.shiftCap`) — exactly as `Val.shift` bumps the
  -- variable index under a `lam`/`letC` binder. (`v`'s var-binding is unchanged; handle binds no var.)
  | .handle h M  => .handle (Handler.substFrom k v h) (Comp.substFrom k (Val.shiftCap v) M)
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
      -- ADR-0045 amendment: the body's filler is `shiftCap v` (handle binds a cap). The β-identity
      -- still holds — instantiate the IH at `(Val.shiftCap v)` rather than `v`.
      simp only [Comp.shiftFrom, Comp.substFrom,
        Handler.substFrom_shiftFrom k v h, Comp.substFrom_shiftFrom k (Val.shiftCap v) M]
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
/-- A value is well-capped iff every `Comp` it thunks is. `force (vthunk M)` steps to `(K, M)`, so a
thunk body `M` faces the AMBIENT context `Sg` (the stack at its force site) — hence check `M` against
`Sg`, not `[]`. The cap-shift (`substFrom`'s `handle` case applying `shiftCap`) is what keeps this
faithful as the thunk migrates under handlers. -/
def WCVal (Sg : EvalCtx) : Val → Prop
  | .vunit       => True
  | .vint _      => True
  | .vvar _      => True
  | .vthunk M    => WCComp Sg M
  | .inl w       => WCVal Sg w
  | .inr w       => WCVal Sg w
  | .pair w₁ w₂  => WCVal Sg w₁ ∧ WCVal Sg w₂
  | .fold w      => WCVal Sg w
/-- A handler's payload value is well-capped. `state`'s stored value faces the ambient `Sg`. A
`transaction`'s heap cells are CLOSED (ADR-0030: `subst`/`shift`/`shiftCap` are all identity on `Θ`),
so they are checked against the EMPTY context `[]` — context-independent, which is exactly why the
cap-shift is the identity on them and they ride every re-typing trivially. -/
def WCHandler (Sg : EvalCtx) : Handler → Prop
  | .throws _       => True
  | .state _ s      => WCVal Sg s
  | .transaction _ Θ => ∀ c ∈ Θ, WCVal [] c
end

/-- The HANDLER skeleton of a stack — keep `handleF` frames, drop cap-transparent `letF`/`appF`. The
context `WCComp`/`CapResolvesKind` effectively see (caps skip plumbing). Seeding `WellCapped` with this
makes PUSH-letF/appF preservation DEFINITIONAL (`handlersOf (letF N :: K) = handlersOf K`). -/
def handlersOf : EvalCtx → EvalCtx
  | [] => []
  | .handleF h :: K => Frame.handleF h :: handlersOf K
  | .letF _ :: K => handlersOf K
  | .appF _ :: K => handlersOf K

/-- `CapResolvesKind` reads only the HANDLER skeleton — caps skip `letF`/`appF`. So a cap resolves the
SAME against `K` and `handlersOf K`. The bridge between RUNTIME dispatch (`staticSplit`/`CapResolvesKind`
over the full `K`) and the WC invariant (over `handlersOf K`). -/
theorem CapResolvesKind_handlersOf : ∀ (K : EvalCtx) (cap : Nat) (ℓ : Label) (op : OpId),
    CapResolvesKind (handlersOf K) cap ℓ op ↔ CapResolvesKind K cap ℓ op
  | [], cap, _, _ => Iff.rfl
  | .handleF h :: K, 0, ℓ, op => by simp only [handlersOf, CapResolvesKind]
  | .handleF h :: K, (c+1), ℓ, op => by
      simp only [handlersOf, CapResolvesKind]; exact CapResolvesKind_handlersOf K c ℓ op
  | .letF _ :: K, cap, ℓ, op => by
      simp only [handlersOf, CapResolvesKind]; exact CapResolvesKind_handlersOf K cap ℓ op
  | .appF _ :: K, cap, ℓ, op => by
      simp only [handlersOf, CapResolvesKind]; exact CapResolvesKind_handlersOf K cap ℓ op

/-- `handlersOf` distributes over append. -/
theorem handlersOf_append (K K' : EvalCtx) : handlersOf (K ++ K') = handlersOf K ++ handlersOf K' := by
  induction K with
  | nil => rfl
  | cons fr K ih => cases fr <;> simp only [handlersOf, List.cons_append, ih]

/-- A frame STACK is well-capped: each stored continuation/argument/handler is well-capped against the
HANDLER skeleton BELOW it (the handlers it will face after the frame is consumed). Innermost-first: a
`letF N` continuation `N`, once reached, dispatches against `handlersOf K`. -/
def WCStack : EvalCtx → Prop
  | [] => True
  | .letF N :: K   => WCComp (handlersOf K) N ∧ WCStack K
  | .appF v :: K   => WCVal (handlersOf K) v ∧ WCStack K
  | .handleF h :: K => WCHandler (handlersOf K) h ∧ WCStack K

/-- The config-level well-capped invariant: the focus is well-capped against the stack's HANDLER
skeleton, and the stack's stored continuations are well-capped against their (own) tails' skeletons.
SUPERSEDED by `LWConfig` (ADR-0045 R1): `WellCapped` is the AUTHOR-context half only and is UNSOUND as
a progress invariant — it ACCEPTS the capability-escape `progB` (build-confirmed) which then runs STUCK,
so it cannot thread `progress`. The two-context `LWT` (below) adds the RETURN/non-escape half that
rejects the escape. Kept here only as the historical witness of the case-B hole; not used by `HasConfig`. -/
def WellCapped : Config → Prop
  | (K, M) => WCComp (handlersOf K) M ∧ WCStack K

/-! ### The LEXICAL config invariant `LWConfig` (ADR-0045 R1) — replaces the unsound `WellCapped`.

The cap-assignment spike (verdict TRACTABLE, `cap-spike` branch) established that a TWO-context
lexical judgement splits the sound case A (capability migration) from the unsound case B (capability
escape) which `WellCapped` could not. R1 promotes it to the kernel; the spike's A/B/cap>0 splits ride
on as the permanent regression suite `Bang/LWRegress.lean`.

  `LWT S R M`  (S, R : EvalCtx):
    S = AUTHOR context  (handlers enclosing M at its def site — `handle` PUSHES `handleF h`).
    R = RETURN context  (handlers a value RETURNED by M escapes INTO — `handle` does NOT push).
  (a) author-site resolution :  `perform cap ℓ op v` needs `CapResolvesKind S cap ℓ op` (reuses the
      WellCapped mechanism — `LWT`'s S-part IS `WCComp`).
  (b) capability NON-ESCAPE  :  `ret v` is checked `LWVal R v` (caps resolve where the value LANDS).
  At `handle h M`: S' = handleF h :: S, R' = OLD S (a returned value crosses OUT past h). At
  `letC M N`: M's R := S (its result is consumed HERE), N keeps R. -/

mutual
/-- A computation is lexically well-typed against AUTHOR context `S` and RETURN context `R`. -/
def LWT (S R : EvalCtx) : Comp → Prop
  | .ret v          => LWVal R v                                   -- (b): returned value escapes to R
  | .perform cap ℓ op v => CapResolvesKind S cap ℓ op ∧ LWVal S v  -- (a): author-site resolution
  | .letC M N       => LWT S S M ∧ LWT S R N      -- M's result CONSUMED here (R_M = S); N escapes to R
  | .force v        => LWVal S v                                   -- forcing runs the thunk HERE (S)
  | .app M v        => LWT S S M ∧ LWVal S v        -- M runs here; its result is consumed by the app
  | .lam M          => LWT S S M                    -- a λ-body runs where applied; model it at S
  | .handle h M     => LWHandler S h ∧ LWT (Frame.handleF h :: S) S M  -- S pushes h; R ↦ OLD S (escape)
  | .case v N₁ N₂   => LWVal S v ∧ LWT S R N₁ ∧ LWT S R N₂
  | .split v N      => LWVal S v ∧ LWT S R N
  | .unfold v       => LWVal S v
  | .oom            => True
  | .wrong _        => True
/-- A value is lexically well-capped against context `X`: every thunk body it carries is `LWT X X`. -/
def LWVal (X : EvalCtx) : Val → Prop
  | .vunit       => True
  | .vint _      => True
  | .vvar _      => True
  | .vthunk M    => LWT X X M
  | .inl w       => LWVal X w
  | .inr w       => LWVal X w
  | .pair w₁ w₂  => LWVal X w₁ ∧ LWVal X w₂
  | .fold w      => LWVal X w
def LWHandler (X : EvalCtx) : Handler → Prop
  | .throws _       => True
  | .state _ s      => LWVal X s
  | .transaction _ Θ => ∀ c ∈ Θ, LWVal [] c
end

/-- The RETURN context for a `ret v` focus over stack `K`: the context the returned value LANDS in. A
value returned by the focus flows UP the stack — it CROSSES every `handleF` (handler-return is identity,
the value escapes past) and is CONSUMED by the first `letF`/`appF` (landing in that frame's handler
skeleton). So skip leading `handleF`s, stop at the first plumbing frame. `[]` = returns to the whole
program (lands nowhere — nothing resolves, the non-escape boundary). -/
def retCtx : EvalCtx → EvalCtx
  | [] => []
  | .handleF _ :: K => retCtx K          -- value crosses the handler (escapes past it)
  | .letF _ :: K => handlersOf K         -- value consumed by the letF continuation, runs in handlersOf K
  | .appF _ :: K => handlersOf K         -- (appF on a ret is ill-typed; total for safety)

/-- A frame stack is lexically well-capped: each stored continuation/handler is `LWT`/`LW`-typed against
ITS OWN author + return contexts (the contexts it faces once the frame is reached). Mirrors `WCStack`
but threads the return context: a `letF N` continuation, when reached, runs in author `handlersOf K`
and returns into `retCtx K`. -/
def LWStack : EvalCtx → Prop
  | [] => True
  | .letF N :: K   => LWT (handlersOf K) (retCtx K) N ∧ LWStack K
  | .appF v :: K   => LWVal (handlersOf K) v ∧ LWStack K
  | .handleF h :: K => LWHandler (handlersOf K) h ∧ LWStack K

/-- **The config-level lexical invariant `LWConfig`** (ADR-0045 R1): the focus is `LWT`-typed against
the stack's HANDLER skeleton (author) and the focus's return context `retCtx K` (where its value lands),
and the stack's stored continuations are `LWStack`. Seeding with `handlersOf K`/`retCtx K` makes the
plumbing frames cap-transparent and the handler-return identity step preservation-by-construction. -/
def LWConfig : Config → Prop
  | (K, M) => LWT (handlersOf K) (retCtx K) M ∧ LWStack K

/-- **Configuration typing** (ADR-0045 R1): the typing CORE (`HasConfigTy`) PLUS the lexical-capability
invariant `LWConfig` (replacing the unsound `WellCapped`). Folding `LWConfig` in HERE keeps the frozen
`preservation`/`progress` statements — stated over `HasConfig` — BYTE-IDENTICAL. (`type_safety`, stated
over `HasCTy [] []`, gains an `LWConfig ([], c)` premise; see `Bang/Spec.lean`.) -/
def HasConfig [EffSig Eff Mult] (cfg : Config) (eo : Eff) (Co : CTy Eff Mult) : Prop :=
  HasConfigTy cfg eo Co ∧ LWConfig cfg

/-! ### `LWConfig` preservation lemmas (ADR-0045 R1) — the cap-invariant steps. -/

/-- **handleF-ret preservation, BY CONSTRUCTION** (the case that broke `WellCapped`). The handler-return
identity step `(handleF h :: K, ret v) ↦ (K, ret v)` preserves `LWConfig`: `retCtx (handleF h :: K) =
retCtx K` (a returned value crosses the handler) and `ret v` is checked ONLY against the return context,
so the focus condition `LWVal (retCtx K) v` is IDENTICAL before/after; `LWStack` just drops its head
handler. This is the whole point of the R-context: a value escaping its handler is checked where it
LANDS, so the pop is a no-op on the invariant. -/
theorem LWConfig.handleF_ret (h : Handler) (K : EvalCtx) (v : Val) :
    LWConfig (Frame.handleF h :: K, Comp.ret v) → LWConfig (K, Comp.ret v) := by
  intro hlw
  obtain ⟨hfocus, hstack⟩ := hlw
  simp only [LWConfig, retCtx, handlersOf, LWT] at hfocus ⊢
  simp only [LWStack] at hstack
  exact ⟨hfocus, hstack.2⟩

/-- `CapResolvesKind K cap ℓ op` ⟹ `staticSplit K cap` SUCCEEDS — a resolving cap names an in-scope
handler, so the runtime dispatch never stalls. The `Prop`→`Option.isSome` bridge that turns the
`LWConfig` focus invariant into operational progress at a `perform`. Structural recursion on `K`/`cap`,
mirroring `staticSplit`/`CapResolvesKind`. (ADR-0045 R1; lifted from the cap-assignment spike.) -/
theorem staticSplit_isSome_of_resolvesKind :
    ∀ (K : EvalCtx) (cap : Nat) (ℓ : Label) (op : OpId),
      CapResolvesKind K cap ℓ op → (staticSplit K cap).isSome
  | [], cap, _, _, h => by cases cap <;> exact absurd h id
  | .handleF _ :: _, 0, _, _, _ => by simp [staticSplit]
  | .handleF _ :: K, c+1, ℓ, op, h => by
      simp only [staticSplit]
      have := staticSplit_isSome_of_resolvesKind K c ℓ op h
      cases hs : staticSplit K c with
      | none => rw [hs] at this; exact absurd this (by simp)
      | some _ => simp
  | .letF _ :: K, cap, ℓ, op, h => by
      simp only [staticSplit]
      have := staticSplit_isSome_of_resolvesKind K cap ℓ op h
      cases hs : staticSplit K cap with
      | none => rw [hs] at this; exact absurd this (by simp)
      | some _ => simp
  | .appF _ :: K, cap, ℓ, op, h => by
      simp only [staticSplit]
      have := staticSplit_isSome_of_resolvesKind K cap ℓ op h
      cases hs : staticSplit K cap with
      | none => rw [hs] at this; exact absurd this (by simp)
      | some _ => simp

/-! ### Well-capped structural lemmas (ADR-0045 B3a) — the chain that makes `WellCapped` preserved.

The lemmas substitution / dispatch need. The KEYSTONE is `WCComp.shiftCap_insert` (a comp/value
well-capped against `Δ ++ Sg`, with caps bumped at cutoff `|Δ|`, stays well-capped against
`Δ ++ handleF h :: Sg` — a handler INSERTED at depth `|Δ|`). It rides on `CapResolvesKind.insert`
(below): the bumped cap resolves identically, because `CapResolvesKind` reads only handler KINDS
(`handlesOp`), which `shiftCapFrom` leaves untouched. -/

/-- `CapResolvesKind` ignores `letF`/`appF` frames (cap-transparent). -/
@[simp] theorem CapResolvesKind.letF (N : Comp) (Sg : EvalCtx) (cap : Nat) (ℓ : Label) (op : OpId) :
    CapResolvesKind (Frame.letF N :: Sg) cap ℓ op = CapResolvesKind Sg cap ℓ op := rfl
@[simp] theorem CapResolvesKind.appF (w : Val) (Sg : EvalCtx) (cap : Nat) (ℓ : Label) (op : OpId) :
    CapResolvesKind (Frame.appF w :: Sg) cap ℓ op = CapResolvesKind Sg cap ℓ op := rfl

/-- `handleF`-map of a handler list — the handler-only prefix `WCComp` threads (it extends Σ ONLY by
`handleF`, never letF/appF). -/
abbrev hframes (Δ : List Handler) : EvalCtx := Δ.map Frame.handleF

/-- `shiftCapFrom` preserves a handler's `handlesOp` (it touches only the payload caps, never the
label or op-kind). Hence `CapResolvesKind`/`WCComp` — which read the context only via `handlesOp` —
are insensitive to it. -/
@[simp] theorem handlesOp_shiftCapFrom (d : Nat) (h : Handler) (ℓ : Label) (op : OpId) :
    handlesOp (Handler.shiftCapFrom d h) ℓ op = handlesOp h ℓ op := by
  cases h <;> rfl

/-- Two frame-lists are `handlesOp`-equivalent: same shape, positionally, and `handleF` frames agree on
`handlesOp` (their payloads may differ). `CapResolvesKind`/`WCComp` respect it. -/
def CtxKindEq : EvalCtx → EvalCtx → Prop
  | [], [] => True
  | (.letF _ :: K), (.letF _ :: K') => CtxKindEq K K'
  | (.appF _ :: K), (.appF _ :: K') => CtxKindEq K K'
  | (.handleF h :: K), (.handleF h' :: K') => (∀ ℓ op, handlesOp h ℓ op = handlesOp h' ℓ op) ∧ CtxKindEq K K'
  | _, _ => False

theorem CtxKindEq.refl : ∀ K : EvalCtx, CtxKindEq K K
  | [] => trivial
  | .letF _ :: K => CtxKindEq.refl K
  | .appF _ :: K => CtxKindEq.refl K
  | .handleF _ :: K => ⟨fun _ _ => rfl, CtxKindEq.refl K⟩

/-- `CapResolvesKind` respects `handlesOp`-equivalence of the context. -/
theorem CapResolvesKind.ctxKindEq : ∀ (K K' : EvalCtx) (cap : Nat) (ℓ : Label) (op : OpId),
    CtxKindEq K K' → (CapResolvesKind K cap ℓ op ↔ CapResolvesKind K' cap ℓ op)
  | [], [], _, _, _, _ => Iff.rfl
  | (.letF _ :: K), (.letF _ :: K'), cap, ℓ, op, he =>
      CapResolvesKind.ctxKindEq K K' cap ℓ op he
  | (.appF _ :: K), (.appF _ :: K'), cap, ℓ, op, he =>
      CapResolvesKind.ctxKindEq K K' cap ℓ op he
  | (.handleF h :: K), (.handleF h' :: K'), 0, ℓ, op, he => by
      simp only [CapResolvesKind]; rw [he.1 ℓ op]
  | (.handleF h :: K), (.handleF h' :: K'), (c+1), ℓ, op, he => by
      simp only [CapResolvesKind]; exact CapResolvesKind.ctxKindEq K K' c ℓ op he.2

/-- **The cap-insertion law.** Inserting a `handleF h` frame at handler-depth `|Δ|` (`Δ` a list of
handlers) and bumping the cap there (`cap ≥ |Δ| ↦ cap+1`, `cap < |Δ| ↦ cap`) preserves
`CapResolvesKind`: a cap targeting an AMBIENT handler (`≥ |Δ|`) skips the inserted frame (the +1), a
cap targeting an INNER handler (`< |Δ|`) is below the insertion and untouched. Induction on `Δ`/`cap`.
The inserted/prefix handlers' PAYLOADS are irrelevant — `CapResolvesKind` reads only `handlesOp`. -/
theorem CapResolvesKind.insert (h : Handler) (Sg : EvalCtx) (ℓ : Label) (op : OpId) :
    ∀ (Δ : List Handler) (cap : Nat),
      CapResolvesKind (hframes Δ ++ Sg) cap ℓ op ↔
      CapResolvesKind (hframes Δ ++ Frame.handleF h :: Sg) (if cap < Δ.length then cap else cap + 1) ℓ op
  | [], cap => by
      simp only [hframes, List.map_nil, List.nil_append, List.length_nil, Nat.not_lt_zero, if_false]
      rfl
  | (h₀ :: Δ), 0 => by
      simp only [hframes, List.map_cons, List.cons_append, List.length_cons, Nat.zero_lt_succ, if_true,
        CapResolvesKind]
  | (h₀ :: Δ), (c + 1) => by
      have hiff := CapResolvesKind.insert h Sg ℓ op Δ c
      by_cases hlt : c < Δ.length
      · have h1 : c + 1 < Δ.length + 1 := by omega
        simp only [hframes, List.map_cons, List.cons_append, List.length_cons, CapResolvesKind,
          if_pos hlt, if_pos h1] at hiff ⊢
        exact hiff
      · have h1 : ¬ (c + 1 < Δ.length + 1) := by omega
        simp only [hframes, List.map_cons, List.cons_append, List.length_cons, CapResolvesKind,
          if_neg hlt, if_neg h1] at hiff ⊢
        exact hiff

/-- `CtxKindEq` extends through a shared head frame. -/
theorem CtxKindEq.cons (fr : Frame) {K K' : EvalCtx} (h : CtxKindEq K K') :
    CtxKindEq (fr :: K) (fr :: K') := by
  cases fr with
  | letF N => exact h
  | appF w => exact h
  | handleF hh => exact ⟨fun _ _ => rfl, h⟩

/-! `WCComp`/`WCVal`/`WCHandler` respect `handlesOp`-equivalence of the context (they read it only via
`CapResolvesKind`). The congruence the keystone's `handle` case needs (the inserted `Δ`-handler's
payload shifts, but its kind doesn't). -/
mutual
theorem WCComp.ctxKindEq : ∀ (K K' : EvalCtx) (M : Comp),
    CtxKindEq K K' → WCComp K M → WCComp K' M := by
  intro K K' M he
  match M with
  | .ret w        => intro hw
                     simp only [WCComp] at hw ⊢; exact WCVal.ctxKindEq K K' w he hw
  | .letC M N     => intro h
                     simp only [WCComp] at h ⊢
                     exact ⟨WCComp.ctxKindEq K K' M he h.1, WCComp.ctxKindEq K K' N he h.2⟩
  | .force w      => intro hw
                     simp only [WCComp] at hw ⊢; exact WCVal.ctxKindEq K K' w he hw
  | .lam M        => intro hM
                     simp only [WCComp] at hM ⊢; exact WCComp.ctxKindEq K K' M he hM
  | .app M w      => intro h
                     simp only [WCComp] at h ⊢
                     exact ⟨WCComp.ctxKindEq K K' M he h.1, WCVal.ctxKindEq K K' w he h.2⟩
  | .perform cap ℓ op w => intro h
                           simp only [WCComp] at h ⊢
                           exact ⟨(CapResolvesKind.ctxKindEq K K' cap ℓ op he).mp h.1,
                                  WCVal.ctxKindEq K K' w he h.2⟩
  | .handle h₀ M  => intro h
                     simp only [WCComp] at h ⊢
                     exact ⟨WCHandler.ctxKindEq K K' h₀ he h.1,
                            WCComp.ctxKindEq _ _ M (CtxKindEq.cons (Frame.handleF h₀) he) h.2⟩
  | .case w N₁ N₂ => intro h
                     simp only [WCComp] at h ⊢
                     exact ⟨WCVal.ctxKindEq K K' w he h.1,
                       WCComp.ctxKindEq K K' N₁ he h.2.1, WCComp.ctxKindEq K K' N₂ he h.2.2⟩
  | .split w N    => intro h
                     simp only [WCComp] at h ⊢
                     exact ⟨WCVal.ctxKindEq K K' w he h.1, WCComp.ctxKindEq K K' N he h.2⟩
  | .unfold w     => intro hw
                     simp only [WCComp] at hw ⊢; exact WCVal.ctxKindEq K K' w he hw
  | .oom          => intro _; simp only [WCComp]
  | .wrong _      => intro _; simp only [WCComp]
theorem WCVal.ctxKindEq : ∀ (K K' : EvalCtx) (w : Val),
    CtxKindEq K K' → WCVal K w → WCVal K' w := by
  intro K K' w he
  match w with
  | .vunit       => intro _; simp only [WCVal]
  | .vint _      => intro _; simp only [WCVal]
  | .vvar _      => intro _; simp only [WCVal]
  | .vthunk M    => intro hM
                    simp only [WCVal] at hM ⊢; exact WCComp.ctxKindEq K K' M he hM
  | .inl w       => intro hw
                    simp only [WCVal] at hw ⊢; exact WCVal.ctxKindEq K K' w he hw
  | .inr w       => intro hw
                    simp only [WCVal] at hw ⊢; exact WCVal.ctxKindEq K K' w he hw
  | .pair w₁ w₂  => intro h
                    simp only [WCVal] at h ⊢
                    exact ⟨WCVal.ctxKindEq K K' w₁ he h.1, WCVal.ctxKindEq K K' w₂ he h.2⟩
  | .fold w      => intro hw
                    simp only [WCVal] at hw ⊢; exact WCVal.ctxKindEq K K' w he hw
theorem WCHandler.ctxKindEq : ∀ (K K' : EvalCtx) (h₀ : Handler),
    CtxKindEq K K' → WCHandler K h₀ → WCHandler K' h₀ := by
  intro K K' h₀ he
  match h₀ with
  | .throws _       => intro _; simp only [WCHandler]
  | .state _ s      => intro hs
                       simp only [WCHandler] at hs ⊢; exact WCVal.ctxKindEq K K' s he hs
  | .transaction _ Θ => intro hΘ
                        simp only [WCHandler] at hΘ ⊢; exact hΘ
end

/-! **THE KEYSTONE** (`WCComp.shiftCap_insert` + duals). A comp well-capped against `hframes Δ ++ Sg`,
with caps bumped at cutoff `|Δ|` (`shiftCapFrom |Δ|`), is well-capped against
`hframes Δ ++ handleF h :: Sg` — a handler INSERTED at depth `|Δ|`. Mirrors `substFrom`'s `handle` case
(`shiftCap` = cutoff 0). Mutual over Comp/Val/Handler; the `perform` case is `CapResolvesKind.insert`,
the `handle` case grows `Δ`. The closed-heap transaction cells (checked against `[]`) ride trivially. -/
mutual
theorem WCComp.shiftCap_insert (h : Handler) (Sg : EvalCtx) :
    ∀ (Δ : List Handler) (M : Comp),
      WCComp (hframes Δ ++ Sg) M →
      WCComp (hframes Δ ++ Frame.handleF h :: Sg) (Comp.shiftCapFrom Δ.length M) := by
  intro Δ M
  match M with
  | .ret w        => intro hw
                     simp only [Comp.shiftCapFrom, WCComp] at hw ⊢
                     exact WCVal.shiftCap_insert h Sg Δ w hw
  | .letC M N     => intro hMN
                     simp only [Comp.shiftCapFrom, WCComp] at hMN ⊢
                     exact ⟨WCComp.shiftCap_insert h Sg Δ M hMN.1, WCComp.shiftCap_insert h Sg Δ N hMN.2⟩
  | .force w      => intro hw
                     simp only [Comp.shiftCapFrom, WCComp] at hw ⊢
                     exact WCVal.shiftCap_insert h Sg Δ w hw
  | .lam M        => intro hM
                     simp only [Comp.shiftCapFrom, WCComp] at hM ⊢
                     exact WCComp.shiftCap_insert h Sg Δ M hM
  | .app M w      => intro hMw
                     simp only [Comp.shiftCapFrom, WCComp] at hMw ⊢
                     exact ⟨WCComp.shiftCap_insert h Sg Δ M hMw.1, WCVal.shiftCap_insert h Sg Δ w hMw.2⟩
  | .perform cap ℓ op w => intro hpw
                           simp only [Comp.shiftCapFrom, WCComp] at hpw ⊢
                           exact ⟨(CapResolvesKind.insert h Sg ℓ op Δ cap).mp hpw.1,
                                  WCVal.shiftCap_insert h Sg Δ w hpw.2⟩
  | .handle h₀ M  => intro hhM
                     simp only [Comp.shiftCapFrom, WCComp] at hhM ⊢
                     refine ⟨WCHandler.shiftCap_insert h Sg Δ h₀ hhM.1, ?_⟩
                     -- IH at Δ' = h₀ :: Δ gives WC against `handleF h₀ :: (hframes Δ ++ handleF h :: Sg)`;
                     -- the goal's head is the SHIFTED `handleF (shiftCap h₀)`. Same kind ⇒ ctxKindEq bridges.
                     have hih := WCComp.shiftCap_insert h Sg (h₀ :: Δ) M (by simpa [hframes] using hhM.2)
                     have hbridge : CtxKindEq
                         (Frame.handleF h₀ :: (hframes Δ ++ Frame.handleF h :: Sg))
                         (Frame.handleF (Handler.shiftCapFrom Δ.length h₀)
                           :: (hframes Δ ++ Frame.handleF h :: Sg)) :=
                       ⟨fun ℓ op => (handlesOp_shiftCapFrom Δ.length h₀ ℓ op).symm, CtxKindEq.refl _⟩
                     have := WCComp.ctxKindEq _ _ (Comp.shiftCapFrom (h₀ :: Δ).length M) hbridge
                       (by simpa [hframes, List.length_cons] using hih)
                     simpa [hframes, List.length_cons] using this
  | .case w N₁ N₂ => intro hc
                     simp only [Comp.shiftCapFrom, WCComp] at hc ⊢
                     exact ⟨WCVal.shiftCap_insert h Sg Δ w hc.1,
                       WCComp.shiftCap_insert h Sg Δ N₁ hc.2.1, WCComp.shiftCap_insert h Sg Δ N₂ hc.2.2⟩
  | .split w N    => intro hs
                     simp only [Comp.shiftCapFrom, WCComp] at hs ⊢
                     exact ⟨WCVal.shiftCap_insert h Sg Δ w hs.1, WCComp.shiftCap_insert h Sg Δ N hs.2⟩
  | .unfold w     => intro hw
                     simp only [Comp.shiftCapFrom, WCComp] at hw ⊢
                     exact WCVal.shiftCap_insert h Sg Δ w hw
  | .oom          => intro _; simp only [Comp.shiftCapFrom, WCComp]
  | .wrong _      => intro _; simp only [Comp.shiftCapFrom, WCComp]
theorem WCVal.shiftCap_insert (h : Handler) (Sg : EvalCtx) :
    ∀ (Δ : List Handler) (w : Val),
      WCVal (hframes Δ ++ Sg) w →
      WCVal (hframes Δ ++ Frame.handleF h :: Sg) (Val.shiftCapFrom Δ.length w) := by
  intro Δ w
  match w with
  | .vunit       => intro _; simp only [Val.shiftCapFrom, WCVal]
  | .vint _      => intro _; simp only [Val.shiftCapFrom, WCVal]
  | .vvar _      => intro _; simp only [Val.shiftCapFrom, WCVal]
  | .vthunk M    => intro hM
                    simp only [Val.shiftCapFrom, WCVal] at hM ⊢
                    exact WCComp.shiftCap_insert h Sg Δ M hM
  | .inl w       => intro hw
                    simp only [Val.shiftCapFrom, WCVal] at hw ⊢
                    exact WCVal.shiftCap_insert h Sg Δ w hw
  | .inr w       => intro hw
                    simp only [Val.shiftCapFrom, WCVal] at hw ⊢
                    exact WCVal.shiftCap_insert h Sg Δ w hw
  | .pair w₁ w₂  => intro hp
                    simp only [Val.shiftCapFrom, WCVal] at hp ⊢
                    exact ⟨WCVal.shiftCap_insert h Sg Δ w₁ hp.1, WCVal.shiftCap_insert h Sg Δ w₂ hp.2⟩
  | .fold w      => intro hw
                    simp only [Val.shiftCapFrom, WCVal] at hw ⊢
                    exact WCVal.shiftCap_insert h Sg Δ w hw
theorem WCHandler.shiftCap_insert (h : Handler) (Sg : EvalCtx) :
    ∀ (Δ : List Handler) (h₀ : Handler),
      WCHandler (hframes Δ ++ Sg) h₀ →
      WCHandler (hframes Δ ++ Frame.handleF h :: Sg) (Handler.shiftCapFrom Δ.length h₀) := by
  intro Δ h₀
  match h₀ with
  | .throws _       => intro _; simp only [Handler.shiftCapFrom, WCHandler]
  | .state _ s      => intro hs
                       simp only [Handler.shiftCapFrom, WCHandler] at hs ⊢
                       exact WCVal.shiftCap_insert h Sg Δ s hs
  | .transaction _ Θ => intro hΘ
                        simp only [Handler.shiftCapFrom, WCHandler] at hΘ ⊢
                        exact hΘ   -- shiftCap = id on closed heap; cells checked against []
end

/-! ### WC under VARIABLE shift + substitution (ADR-0045 B3a)

`WCComp`/`WCVal` read the context only via caps, which the VARIABLE shift/subst never touch — so they
are invariant under `shiftFrom` (var shift). And `handlesOp` is invariant under `substFrom` (subst
changes only handler payloads). These feed the substitution lemma. -/

@[simp] theorem handlesOp_substFrom (k : Nat) (v : Val) (h : Handler) (ℓ : Label) (op : OpId) :
    handlesOp (Handler.substFrom k v h) ℓ op = handlesOp h ℓ op := by cases h <;> rfl

/-! The VARIABLE shift preserves well-cappedness (it renumbers vars, never caps). -/
mutual
theorem WCComp.shiftFrom_inv (c : Nat) (Sg : EvalCtx) :
    ∀ M : Comp, WCComp Sg M → WCComp Sg (Comp.shiftFrom c M) := by
  intro M
  match M with
  | .ret w        => intro hw; simp only [Comp.shiftFrom, WCComp] at hw ⊢; exact WCVal.shiftFrom_inv c Sg w hw
  | .letC M N     => intro h; simp only [Comp.shiftFrom, WCComp] at h ⊢
                     exact ⟨WCComp.shiftFrom_inv c Sg M h.1, WCComp.shiftFrom_inv (c+1) Sg N h.2⟩
  | .force w      => intro hw; simp only [Comp.shiftFrom, WCComp] at hw ⊢; exact WCVal.shiftFrom_inv c Sg w hw
  | .lam M        => intro hM; simp only [Comp.shiftFrom, WCComp] at hM ⊢; exact WCComp.shiftFrom_inv (c+1) Sg M hM
  | .app M w      => intro h; simp only [Comp.shiftFrom, WCComp] at h ⊢
                     exact ⟨WCComp.shiftFrom_inv c Sg M h.1, WCVal.shiftFrom_inv c Sg w h.2⟩
  | .perform cap ℓ op w => intro h; simp only [Comp.shiftFrom, WCComp] at h ⊢
                           exact ⟨h.1, WCVal.shiftFrom_inv c Sg w h.2⟩
  | .handle h₀ M  => intro h; simp only [Comp.shiftFrom, WCComp] at h ⊢
                     refine ⟨?_, ?_⟩
                     · -- handler payload shift: kind unchanged, so WCHandler survives (shift only the val)
                       exact WCHandler.shiftFrom_inv c Sg h₀ h.1
                     · -- the body's context gains `handleF (shiftFrom c h₀)`; same KIND as `handleF h₀`.
                       have hb : CtxKindEq (Frame.handleF h₀ :: Sg)
                           (Frame.handleF (Handler.shiftFrom c h₀) :: Sg) :=
                         ⟨fun ℓ op => by cases h₀ <;> rfl, CtxKindEq.refl _⟩
                       exact WCComp.ctxKindEq _ _ _ hb (WCComp.shiftFrom_inv c (Frame.handleF h₀ :: Sg) M h.2)
  | .case w N₁ N₂ => intro h; simp only [Comp.shiftFrom, WCComp] at h ⊢
                     exact ⟨WCVal.shiftFrom_inv c Sg w h.1,
                       WCComp.shiftFrom_inv (c+1) Sg N₁ h.2.1, WCComp.shiftFrom_inv (c+1) Sg N₂ h.2.2⟩
  | .split w N    => intro h; simp only [Comp.shiftFrom, WCComp] at h ⊢
                     exact ⟨WCVal.shiftFrom_inv c Sg w h.1, WCComp.shiftFrom_inv (c+2) Sg N h.2⟩
  | .unfold w     => intro hw; simp only [Comp.shiftFrom, WCComp] at hw ⊢; exact WCVal.shiftFrom_inv c Sg w hw
  | .oom          => intro _; simp only [Comp.shiftFrom, WCComp]
  | .wrong _      => intro _; simp only [Comp.shiftFrom, WCComp]
theorem WCVal.shiftFrom_inv (c : Nat) (Sg : EvalCtx) :
    ∀ w : Val, WCVal Sg w → WCVal Sg (Val.shiftFrom c w) := by
  intro w
  match w with
  | .vunit       => intro _; simp only [Val.shiftFrom, WCVal]
  | .vint _      => intro _; simp only [Val.shiftFrom, WCVal]
  | .vvar i      => intro _; simp only [Val.shiftFrom]; split <;> simp only [WCVal]
  | .vthunk M    => intro hM; simp only [Val.shiftFrom, WCVal] at hM ⊢; exact WCComp.shiftFrom_inv c Sg M hM
  | .inl w       => intro hw; simp only [Val.shiftFrom, WCVal] at hw ⊢; exact WCVal.shiftFrom_inv c Sg w hw
  | .inr w       => intro hw; simp only [Val.shiftFrom, WCVal] at hw ⊢; exact WCVal.shiftFrom_inv c Sg w hw
  | .pair w₁ w₂  => intro h; simp only [Val.shiftFrom, WCVal] at h ⊢
                    exact ⟨WCVal.shiftFrom_inv c Sg w₁ h.1, WCVal.shiftFrom_inv c Sg w₂ h.2⟩
  | .fold w      => intro hw; simp only [Val.shiftFrom, WCVal] at hw ⊢; exact WCVal.shiftFrom_inv c Sg w hw
theorem WCHandler.shiftFrom_inv (c : Nat) (Sg : EvalCtx) :
    ∀ h₀ : Handler, WCHandler Sg h₀ → WCHandler Sg (Handler.shiftFrom c h₀) := by
  intro h₀
  match h₀ with
  | .throws _       => intro _; simp only [Handler.shiftFrom, WCHandler]
  | .state _ s      => intro hs; simp only [Handler.shiftFrom, WCHandler] at hs ⊢; exact WCVal.shiftFrom_inv c Sg s hs
  | .transaction _ Θ => intro hΘ; simp only [Handler.shiftFrom, WCHandler] at hΘ ⊢; exact hΘ
end

/-! **THE SUBSTITUTION LEMMA.** Well-cappedness is preserved by `substFrom`: substituting a well-capped
value `v` into a well-capped comp `N` yields a well-capped comp. The `handle` case is where the cap-shift
pays off — the filler becomes `shiftCap v` and the context gains a handler, exactly the keystone
(`shiftCap_insert` at `Δ=[]`). The `v` (filler) is checked against the SAME `Sg` throughout because the
variable binders (`letC`/`lam`/`case`/`split`) apply `Val.shift` (var-invariant for WC) and `handle`
applies `Val.shiftCap` (keystone). -/
mutual
theorem WCComp.substFrom (Sg : EvalCtx) (v : Val) (hv : WCVal Sg v) :
    ∀ (k : Nat) (M : Comp), WCComp Sg M → WCComp Sg (Comp.substFrom k v M) := by
  intro k M
  match M with
  | .ret w        => intro hw; simp only [Comp.substFrom, WCComp] at hw ⊢; exact WCVal.substFrom Sg v hv k w hw
  | .letC M N     => intro h; simp only [Comp.substFrom, WCComp] at h ⊢
                     exact ⟨WCComp.substFrom Sg v hv k M h.1,
                            WCComp.substFrom Sg (Val.shift v) (WCVal.shiftFrom_inv 0 Sg v hv) (k+1) N h.2⟩
  | .force w      => intro hw; simp only [Comp.substFrom, WCComp] at hw ⊢; exact WCVal.substFrom Sg v hv k w hw
  | .lam M        => intro hM; simp only [Comp.substFrom, WCComp] at hM ⊢
                     exact WCComp.substFrom Sg (Val.shift v) (WCVal.shiftFrom_inv 0 Sg v hv) (k+1) M hM
  | .app M w      => intro h; simp only [Comp.substFrom, WCComp] at h ⊢
                     exact ⟨WCComp.substFrom Sg v hv k M h.1, WCVal.substFrom Sg v hv k w h.2⟩
  | .perform cap ℓ op w => intro h; simp only [Comp.substFrom, WCComp] at h ⊢
                           exact ⟨h.1, WCVal.substFrom Sg v hv k w h.2⟩
  | .handle h₀ M  => intro h; simp only [Comp.substFrom, WCComp] at h ⊢
                     refine ⟨?_, ?_⟩
                     · exact WCHandler.substFrom Sg v hv k h₀ h.1
                     · -- the body: filler becomes `shiftCap v`, context gains `handleF (h₀.subst)`.
                       -- (1) `WCVal (handleF (h₀.subst) :: Sg) (shiftCap v)` via the keystone (Δ=[], h:=h₀.subst).
                       have hvc : WCVal (Frame.handleF (Handler.substFrom k v h₀) :: Sg) (Val.shiftCap v) := by
                         have := WCVal.shiftCap_insert (Handler.substFrom k v h₀) Sg [] v (by simpa [hframes] using hv)
                         simpa [hframes, Val.shiftCap] using this
                       -- (2) the body hyp `WCComp (handleF h₀ :: Sg) M`, bridged to `handleF (h₀.subst)` by kind.
                       have hbridge : CtxKindEq (Frame.handleF h₀ :: Sg)
                           (Frame.handleF (Handler.substFrom k v h₀) :: Sg) :=
                         ⟨fun ℓ op => by cases h₀ <;> rfl, CtxKindEq.refl _⟩
                       have hbody : WCComp (Frame.handleF (Handler.substFrom k v h₀) :: Sg) M :=
                         WCComp.ctxKindEq _ _ M hbridge h.2
                       exact WCComp.substFrom _ (Val.shiftCap v) hvc k M hbody
  | .case w N₁ N₂ => intro h; simp only [Comp.substFrom, WCComp] at h ⊢
                     refine ⟨WCVal.substFrom Sg v hv k w h.1, ?_, ?_⟩
                     · exact WCComp.substFrom Sg (Val.shift v) (WCVal.shiftFrom_inv 0 Sg v hv) (k+1) N₁ h.2.1
                     · exact WCComp.substFrom Sg (Val.shift v) (WCVal.shiftFrom_inv 0 Sg v hv) (k+1) N₂ h.2.2
  | .split w N    => intro h; simp only [Comp.substFrom, WCComp] at h ⊢
                     refine ⟨WCVal.substFrom Sg v hv k w h.1, ?_⟩
                     exact WCComp.substFrom Sg (Val.shift (Val.shift v))
                       (WCVal.shiftFrom_inv 0 Sg _ (WCVal.shiftFrom_inv 0 Sg v hv)) (k+2) N h.2
  | .unfold w     => intro hw; simp only [Comp.substFrom, WCComp] at hw ⊢; exact WCVal.substFrom Sg v hv k w hw
  | .oom          => intro _; simp only [Comp.substFrom, WCComp]
  | .wrong _      => intro _; simp only [Comp.substFrom, WCComp]
theorem WCVal.substFrom (Sg : EvalCtx) (v : Val) (hv : WCVal Sg v) :
    ∀ (k : Nat) (w : Val), WCVal Sg w → WCVal Sg (Val.substFrom k v w) := by
  intro k w
  match w with
  | .vunit       => intro _; simp only [Val.substFrom, WCVal]
  | .vint _      => intro _; simp only [Val.substFrom, WCVal]
  | .vvar i      => intro _; simp only [Val.substFrom]
                    split
                    · exact hv
                    · split <;> simp only [WCVal]
  | .vthunk M    => intro hM; simp only [Val.substFrom, WCVal] at hM ⊢; exact WCComp.substFrom Sg v hv k M hM
  | .inl w       => intro hw; simp only [Val.substFrom, WCVal] at hw ⊢; exact WCVal.substFrom Sg v hv k w hw
  | .inr w       => intro hw; simp only [Val.substFrom, WCVal] at hw ⊢; exact WCVal.substFrom Sg v hv k w hw
  | .pair w₁ w₂  => intro h; simp only [Val.substFrom, WCVal] at h ⊢
                    exact ⟨WCVal.substFrom Sg v hv k w₁ h.1, WCVal.substFrom Sg v hv k w₂ h.2⟩
  | .fold w      => intro hw; simp only [Val.substFrom, WCVal] at hw ⊢; exact WCVal.substFrom Sg v hv k w hw
theorem WCHandler.substFrom (Sg : EvalCtx) (v : Val) (hv : WCVal Sg v) :
    ∀ (k : Nat) (h₀ : Handler), WCHandler Sg h₀ → WCHandler Sg (Handler.substFrom k v h₀) := by
  intro k h₀
  match h₀ with
  | .throws _       => intro _; simp only [Handler.substFrom, WCHandler]
  | .state _ s      => intro hs; simp only [Handler.substFrom, WCHandler] at hs ⊢; exact WCVal.substFrom Sg v hv k s hs
  | .transaction _ Θ => intro hΘ; simp only [Handler.substFrom, WCHandler] at hΘ ⊢; exact hΘ
end

/-- `WCComp.subst` — the head-redex form (`k = 0`) the REDUCE steps use directly. -/
theorem WCComp.subst (Sg : EvalCtx) (v : Val) (N : Comp)
    (hv : WCVal Sg v) (hN : WCComp Sg N) : WCComp Sg (Comp.subst v N) :=
  WCComp.substFrom Sg v hv 0 N hN

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
    {cfg cfg' : Config} (_hlw : LWConfig cfg) (_hstep : Source.step cfg = some cfg') :
    LWConfig cfg' := by
  sorry

/-! ### Lexical-cap regression demos (ADR-0045 amendment) — REAL artifacts, build-gated.

These `#guard`s are the divergence-is-fixed evidence: a false cap-shift fails the build. The program is
`state s in (let c = {get} in handle (throws _) ($c))` — a `get`-thunk forced UNDER an unrelated
`throws` handler (migration via the `letC` substitution placing the thunk beneath the `handle`
wrapper). With the cap-shift in `substFrom` (handle as cap-binder), the thunk's `perform 0` bumps to
skip the `throws` and correctly reaches the outer `state`. Labels are `Nat` (`EffectRow.Label`). -/

/-- `Source.eval` yields exactly `done (vint n)` (Bool; `Result`/`Val` derive only `Inhabited`). -/
private def yieldsInt (fuel : Nat) (c : Comp) (n : Int) : Bool :=
  match Source.eval fuel c with | .done (.vint m) => m == n | _ => false

/-- 1-deep migration: `get` thunk forced under ONE fresh `throws`; correctly reads the outer state 5. -/
private def capMigrate1 : Comp :=
  .handle (.state 1 (.vint 5))
    (.letC (.ret (.vthunk (.perform 0 1 "get" .vunit)))
      (.handle (.throws 2) (.force (.vvar 0))))
#guard yieldsInt 200 capMigrate1 5

/-- 2-deep migration: the thunk crosses TWO fresh `throws` handlers; the cap-shift recurses (0↦1↦2),
so `get` still reaches the outer state 9. Defends the `shiftCapFrom` recursion under nested handles. -/
private def capMigrate2 : Comp :=
  .handle (.state 1 (.vint 9))
    (.letC (.ret (.vthunk (.perform 0 1 "get" .vunit)))
      (.handle (.throws 2) (.handle (.throws 3) (.force (.vvar 0)))))
#guard yieldsInt 300 capMigrate2 9

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
