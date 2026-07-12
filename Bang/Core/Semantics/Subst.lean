module

public import Bang.Core.IR
public import Bang.Core.Typing

/-!
  Bang/Operational/Subst.lean — de Bruijn substitution + shift (ADR-0020).
  ─────────────────────────────────────────────────────────────────────────
    §1.3a  Val/Comp/Handler.shiftFrom · substFrom · subst · shift (mutual)
    §1.3b  subst-after-shift cancellation (the autosubst β-identity)

  The substitution FOUNDATION of the operational hub — imported by Dispatch,
  Eval, Invariants. Split out of the former monolithic Bang/Operational.lean
  (the fan-in-11 hub) per core-overview.md §6; behavior-preserving MOVE.
-/

namespace Bang

open Bang.EffectRow (Label)

variable {Eff  : Type} [Lattice Eff] [OrderBot Eff]
variable {Mult : Type} [CommSemiring Mult] [DecidableEq Mult]

@[expose] public section

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
/-- Increment a computation's free indices (`≥ c`) by 1, crossing each binder. -/
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
  | .binop op w₁ w₂ => .binop op (Val.shiftFrom c w₁) (Val.shiftFrom c w₂)  -- δ-rule: operands are values, no binders
  | .oom         => .oom
  | .wrong s     => .wrong s
/-- Increment a handler's carried free indices (`≥ c`) by 1; handlers do not bind. -/
def Handler.shiftFrom (c : Nat) : Handler → Handler
  | .state ℓ s   => .state ℓ (Val.shiftFrom c s)
  | .throws ℓ    => .throws ℓ
  -- transaction's heap cells are CLOSED values (the CK focus is always closed, ADR-0025/0030), so
  -- shift is the IDENTITY on them. We leave `Θ` untouched (rather than `Θ.map (shiftFrom c)`): a
  -- recursive `List.map (Val.shiftFrom c)` call would force the `shiftFrom` mutual block onto
  -- well-founded recursion, breaking the `rfl`-reduction the kernel demos + metatheory rely on. The
  -- identity is SOUND for closed heaps (the only heaps a well-typed `transaction` frame carries).
  | .transaction ℓ Θ => .transaction ℓ Θ
  -- custom (ADR-0085 #44 STAGE 1): IDENTITY, like `transaction`. The carried param + clause `Comp`s are
  -- treated as CLOSED (the CK focus is always closed, ADR-0025/0030), so shift is the identity — and,
  -- as with `transaction`'s heap, descending (here into a `OpId → Option Comp` FUNCTION) would force the
  -- mutual `shiftFrom` block onto well-founded recursion, breaking the `rfl`-reduction the kernel relies
  -- on. Sound this stage: custom is untyped (stage 3), so no typed program's substitution observes it.
  | .custom ℓ p clauses => .custom ℓ p clauses
  -- customUpd (ADR-0107 D5): IDENTITY, byte-identical to `custom` (same closed-fields discipline).
  | .customUpd ℓ p clauses => .customUpd ℓ p clauses
end

/-- `Val.shift = Val.shiftFrom 0` — push a closed-ish value under one binder. -/
abbrev Val.shift  : Val → Val  := Val.shiftFrom 0
/-- `Comp.shift = Comp.shiftFrom 0` — push a computation under one binder. -/
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
/-- Substitute `v` for de Bruijn level `k` in a computation, shifting `v` under
each crossed binder and renumbering free indices `> k`. -/
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
  | .binop op w₁ w₂ => .binop op (Val.substFrom k v w₁) (Val.substFrom k v w₂)  -- δ-rule: operands are values, no binders
  | .oom         => .oom
  | .wrong s     => .wrong s
/-- Substitute `v` for level `k` in a handler's carried values; handlers do not bind. -/
def Handler.substFrom (k : Nat) (v : Val) : Handler → Handler
  | .state ℓ s   => .state ℓ (Val.substFrom k v s)
  | .throws ℓ    => .throws ℓ
  -- heap cells are CLOSED ⇒ subst is the identity; leave `Θ` untouched (keeps structural recursion,
  -- so the `substFrom` family still reduces by `rfl`). Sound for closed heaps (ADR-0030).
  | .transaction ℓ Θ => .transaction ℓ Θ
  -- custom (ADR-0085 #44 STAGE 1): IDENTITY, like `transaction` — the carried param + clauses are
  -- treated as closed (keeps the `substFrom` family structurally `rfl`-reducing; descending into the
  -- `OpId → Option Comp` function would break it). Sound this stage: custom is untyped, unobservable
  -- by any typed program's substitution. Real param/clause substitution is a stage-2/3 concern.
  | .custom ℓ p clauses => .custom ℓ p clauses
  -- customUpd (ADR-0107 D5): IDENTITY, byte-identical to `custom`.
  | .customUpd ℓ p clauses => .customUpd ℓ p clauses
end

/-- The head-redex substitution `c[v]`: fill the nearest binder (index 0)
with `v`, renumbering. β / let reduce with this. -/
abbrev Comp.subst (v : Val) : Comp → Comp := Comp.substFrom 0 v
/-- Fill a value's nearest binder (index 0) with `v`, renumbering. -/
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

-- public (was private): consumed by the env/closure machine's `Comp.ScopedC.substFrom_eq`
-- (task #15 retired the transplanted copy in favour of this single source).
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
  | .binop op w₁ w₂ => by
      simp only [Comp.shiftFrom, Comp.substFrom,
        Val.substFrom_shiftFrom k v w₁, Val.substFrom_shiftFrom k v w₂]
  | .oom         => rfl
  | .wrong _     => rfl

-- public (was private): consumed transitively via `Comp.substFrom_shiftFrom` by the machine (task #15).
theorem Handler.substFrom_shiftFrom (k : Nat) (v : Val) :
    ∀ h : Handler, Handler.substFrom k v (Handler.shiftFrom k h) = h
  | .state ℓ s       => by simp only [Handler.shiftFrom, Handler.substFrom, Val.substFrom_shiftFrom k v s]
  | .throws _        => rfl
  -- heap left untouched by both shift and subst (closed cells, ADR-0030) ⇒ identity is definitional.
  | .transaction _ _ => rfl
  -- custom: both shift and subst are the identity (ADR-0085 stage 1) ⇒ round-trip is definitional.
  | .custom _ _ _    => rfl
  | .customUpd _ _ _ => rfl   -- customUpd (ADR-0107 D5): identity like `custom`
end

/-- `(Comp.shift c).subst v = c` — the cutoff-0 instance of `Comp.substFrom_shiftFrom`, the exact
shape `seq_unit` needs for the `letC (ret v) (shift c) ↦ c` head-reduction. -/
theorem Comp.subst_shift (v : Val) (c : Comp) : Comp.subst v (Comp.shift c) = c :=
  Comp.substFrom_shiftFrom 0 v c


/-! ### 1.3c Closing substitutions (`closeC` · `Val.Closed` · the substitution-swap engine)

Hoisted here (task #15) from `Bang/Meta/LR.lean`/`Bang/Meta/BinaryLR.lean`: this is PURE de-Bruijn
substitution machinery (no logical-relation dependency), so it belongs in the substitution foundation
next to `substFrom`/`shiftFrom`, not in the LR. Two downstream consumers share it — the LR's
`EnvRel`/fundamental theorem (`closeC`, referenced by the FROZEN `lr_fundamental` in `Spec.lean`, which
imports this via `Core.Semantics`) and the env/closure machine's `substEnv` correspondence
(`Bang/Backend/EnvMachine.lean`, whose former transplanted duplicate is retired against these names).
Single source of truth for the closing-substitution calculus (ADR-0094 hoist).

The faithfulness anchor (why closedness is a real invariant, not an artifact): the CK machine's focus is
always a CLOSED term, and every value it RETURNS or PLUGS is closed (ADR-0025/0030 — the same
closed-cell invariant `Handler.shiftFrom`/`substFrom` exploit on heap cells). -/

/-- A value is `Closed` when every `shiftFrom` cutoff fixes it (no free de Bruijn index is exposed).
The semantic analogue of `Metatheory.HasVTy.shift_closed`'s conclusion. -/
def Val.Closed (v : Val) : Prop := ∀ k, Val.shiftFrom k v = v

/-- The k=0 instance: a closed value is fixed by `Val.shift`. This is the vanishing-shift fact
`closeC_subst_comm` consumes (`Comp.substFrom 1 (Val.shift v) N = Comp.substFrom 1 v N`). -/
theorem Val.Closed.shift {v : Val} (h : Val.Closed v) : Val.shift v = v := h 0

/-- A closed value is fixed by `Val.shiftFrom` at EVERY cutoff (the defining property, named). -/
theorem Val.Closed.shiftFrom_eq {v : Val} (h : Val.Closed v) (k : Nat) : Val.shiftFrom k v = v := h k

/-- A closed value is fixed by `Val.substFrom` at every cutoff, for any filler. Closed = shift-fixed at
`k` ⇒ `substFrom k w v = substFrom k w (shiftFrom k v) = v` via the subst-after-shift cancellation
(`Val.substFrom_shiftFrom`). This is what the substitution-swap lemma consumes when it traverses INTO a
closed filler. -/
theorem Val.Closed.subst_at {v : Val} (h : Val.Closed v) (k : Nat) (w : Val) :
    Val.substFrom k w v = v := by
  conv_lhs => rw [← h.shiftFrom_eq k]
  exact Val.substFrom_shiftFrom k w v

/-- Closedness is inherited by an injection's payload: `Closed (inl w) → Closed w` (and `inr`). The
constructor `shiftFrom`s structurally, so the payload's shift-invariance follows by injectivity. -/
theorem Val.Closed.inl_inv {w : Val} (h : Val.Closed (Val.inl w)) : Val.Closed w := by
  intro k; have := h k; rw [Val.shiftFrom, Val.inl.injEq] at this; exact this
theorem Val.Closed.inr_inv {w : Val} (h : Val.Closed (Val.inr w)) : Val.Closed w := by
  intro k; have := h k; rw [Val.shiftFrom, Val.inr.injEq] at this; exact this
/-- A pair's components are each closed. -/
theorem Val.Closed.pair_inv {a b : Val} (h : Val.Closed (Val.pair a b)) :
    Val.Closed a ∧ Val.Closed b := by
  constructor <;> intro k <;> (have := h k; rw [Val.shiftFrom, Val.pair.injEq] at this)
  exacts [this.1, this.2]
/-- A `fold`'s payload is closed (the μ-intro analogue of `inl_inv`). -/
theorem Val.Closed.fold_inv {w : Val} (h : Val.Closed (Val.fold w)) : Val.Closed w := by
  intro k; have := h k; rw [Val.shiftFrom, Val.fold.injEq] at this; exact this

/-- Apply a closing environment δ to a computation: substitute index 0 with `δ[0]` (renumbering),
then recurse on the tail (each `Comp.subst` removes the nearest binder). `closeC [] c = c`. -/
def closeC : List Val → Comp → Comp
  | [],      c => c
  | v :: δ,  c => closeC δ (Comp.subst v c)

/-- Apply a closing environment δ to a value (the value-level `closeC`). -/
def closeV : List Val → Val → Val
  | [],      v => v
  | u :: δ,  v => closeV δ (Val.subst u v)

@[simp] theorem closeC_nil (c : Comp) : closeC [] c = c := rfl
@[simp] theorem closeV_nil (v : Val) : closeV [] v = v := rfl

/-- Shift a value under `d` binders (`Val.shift` iterated `d` times) — the cutoff-0 weakening a filler
undergoes when `closeC` descends `d` binders. `shiftN 0 v = v`. -/
def shiftN : Nat → Val → Val
  | 0,     v => v
  | d + 1, v => Val.shift (shiftN d v)

@[simp] theorem shiftN_zero (v : Val) : shiftN 0 v = v := rfl

/-- A closed value is fixed by `shiftN d` (induction on `d`, each step is `Val.Closed.shift`). -/
theorem shiftN_closed {v : Val} (h : Val.Closed v) : ∀ d, shiftN d v = v
  | 0     => rfl
  | d + 1 => by
      show Val.shift (shiftN d v) = v
      rw [shiftN_closed h d, h.shift]

/-- Apply a closing environment δ to a computation that sits UNDER `d` fresh binders: each filler `v`
substitutes at level `d` (the binders shift the environment up by `d`), weakened by `shiftN d`.
`closeCUnderBinders 0 = closeC`; `closeCUnderBinders d [] c = c`. The binder-side fold the distribution
lemmas peel `closeC` into. -/
def closeCUnderBinders (d : Nat) : List Val → Comp → Comp
  | [],     c => c
  | v :: δ, c => closeCUnderBinders d δ (Comp.substFrom d (shiftN d v) c)

@[simp] theorem closeCUnderBinders_nil (d : Nat) (c : Comp) : closeCUnderBinders d [] c = c := rfl

/-- `closeCUnderBinders 0` is exactly `closeC` (level-0 subst, no weakening). -/
theorem closeCUnderBinders_zero (δ : List Val) (c : Comp) : closeCUnderBinders 0 δ c = closeC δ c := by
  induction δ generalizing c with
  | nil => rfl
  | cons v δ ih => simp only [closeCUnderBinders, closeC, Comp.subst, shiftN]; exact ih _

@[simp] theorem closeC_ret (δ : List Val) (w : Val) :
    closeC δ (Comp.ret w) = Comp.ret (closeV δ w) := by
  induction δ generalizing w with
  | nil => rfl
  | cons v δ ih => simp only [closeC, closeV, Comp.subst, Comp.substFrom]; exact ih _

@[simp] theorem closeC_force (δ : List Val) (w : Val) :
    closeC δ (Comp.force w) = Comp.force (closeV δ w) := by
  induction δ generalizing w with
  | nil => rfl
  | cons v δ ih => simp only [closeC, closeV, Comp.subst, Comp.substFrom]; exact ih _

@[simp] theorem closeC_app (δ : List Val) (M : Comp) (w : Val) :
    closeC δ (Comp.app M w) = Comp.app (closeC δ M) (closeV δ w) := by
  induction δ generalizing M w with
  | nil => rfl
  | cons v δ ih => simp only [closeC, closeV, Comp.subst, Comp.substFrom]; exact ih _ _

@[simp] theorem closeC_perform (δ : List Val) (cp : Val) (op : OpId) (w : Val) :
    closeC δ (Comp.perform cp op w) = Comp.perform (closeV δ cp) op (closeV δ w) := by
  induction δ generalizing cp w with
  | nil => rfl
  | cons v δ ih => simp only [closeC, closeV, Comp.subst, Comp.substFrom]; exact ih _ _

@[simp] theorem closeC_unfold (δ : List Val) (w : Val) :
    closeC δ (Comp.unfold w) = Comp.unfold (closeV δ w) := by
  induction δ generalizing w with
  | nil => rfl
  | cons v δ ih => simp only [closeC, closeV, Comp.subst, Comp.substFrom]; exact ih _

/-- `closeC` distributes through a `throws` handler. ADR-0054: `handle` BINDS the capability at index 0,
so the body `M` sits under ONE binder and closes via `closeCUnderBinders 1 δ M` (mirror `closeC_lam`);
the no-shift win materializes here — the LR handler arms match this directly (ADR-0050 wall dissolved).
The handler `throws ℓ` carries no value (`Handler.substFrom _ (throws ℓ) = throws ℓ`). -/
@[simp] theorem closeC_handleThrows (δ : List Val) (ℓ : Label) (M : Comp) :
    closeC δ (Comp.handle (Handler.throws ℓ) M)
      = Comp.handle (Handler.throws ℓ) (closeCUnderBinders 1 δ M) := by
  induction δ generalizing M with
  | nil => rfl
  | cons v δ ih =>
    simp only [closeC, closeCUnderBinders, Comp.subst, Comp.substFrom, Handler.substFrom, shiftN]
    exact ih _

/-- ◊4.5 RESUME INFRA: `closeC` distributes through a `state ℓ s` handler. The `state` handler CARRIES a
value `s` (`Handler.substFrom k v (state ℓ s) = state ℓ (substFrom k v s)`), so the stored value closes
at level 0 (the handler does not bind). ADR-0054: the body `M` is under the cap-binder, so it closes via
`closeCUnderBinders 1 δ M`. -/
@[simp] theorem closeC_handleState (δ : List Val) (ℓ : Label) (s : Val) (M : Comp) :
    closeC δ (Comp.handle (Handler.state ℓ s) M)
      = Comp.handle (Handler.state ℓ (closeV δ s)) (closeCUnderBinders 1 δ M) := by
  induction δ generalizing s M with
  | nil => rfl
  | cons v δ ih =>
    simp only [closeC, closeV, closeCUnderBinders, Comp.subst, Val.subst, Comp.substFrom,
      Handler.substFrom, shiftN]
    exact ih _ _

/-- ◊4.5 RESUME INFRA: `closeC` distributes through a `transaction ℓ Θ` handler. The heap cells are
treated as CLOSED (ADR-0030: `Handler.substFrom _ (transaction ℓ Θ) = transaction ℓ Θ`, identity), so
the heap is untouched. ADR-0054: the body `M` is under the cap-binder, so it closes via
`closeCUnderBinders 1 δ M`. -/
@[simp] theorem closeC_handleTransaction (δ : List Val) (ℓ : Label) (Θ : Store) (M : Comp) :
    closeC δ (Comp.handle (Handler.transaction ℓ Θ) M)
      = Comp.handle (Handler.transaction ℓ Θ) (closeCUnderBinders 1 δ M) := by
  induction δ generalizing M with
  | nil => rfl
  | cons v δ ih =>
    simp only [closeC, closeCUnderBinders, Comp.subst, Comp.substFrom, Handler.substFrom, shiftN]
    exact ih _

/-- ◊4.5b #44 STAGE 5: `closeC` distributes through a `custom ℓ p cl` handler. The param + clause bodies
are treated as CLOSED (ADR-0085 stage 1: `Handler.substFrom _ (custom …) = custom …`, identity — like
`transaction`), so they are untouched; the body `M` closes under the cap-binder via `closeCUnderBinders 1`. -/
@[simp] theorem closeC_handleCustom (δ : List Val) (ℓ : Label) (p : Val) (cl : List (OpId × Comp)) (M : Comp) :
    closeC δ (Comp.handle (Handler.custom ℓ p cl) M)
      = Comp.handle (Handler.custom ℓ p cl) (closeCUnderBinders 1 δ M) := by
  induction δ generalizing M with
  | nil => rfl
  | cons v δ ih =>
    simp only [closeC, closeCUnderBinders, Comp.subst, Comp.substFrom, Handler.substFrom, shiftN]
    exact ih _

@[simp] theorem closeV_vunit (δ : List Val) : closeV δ Val.vunit = Val.vunit := by
  induction δ with
  | nil => rfl
  | cons v δ ih => simp only [closeV, Val.subst, Val.substFrom]; exact ih

@[simp] theorem closeV_vint (δ : List Val) (i : Int) : closeV δ (Val.vint i) = Val.vint i := by
  induction δ with
  | nil => rfl
  | cons v δ ih => simp only [closeV, Val.subst, Val.substFrom]; exact ih

/-- Closing a CLOSED value is the identity: each `Val.subst` in the fold leaves a closed value fixed
(`Val.Closed.subst_at` at cutoff 0). -/
theorem closeV_closed {v : Val} (hv : Val.Closed v) : ∀ δ : List Val, closeV δ v = v
  | []      => rfl
  | u :: δ  => by
      rw [closeV, show Val.subst u v = v from hv.subst_at 0 u]; exact closeV_closed hv δ

/-! ### B.1a″ Shift/subst commutation for a CLOSED filler

The standard de Bruijn shift-after-subst commutation, specialized to a CLOSED filler `u` (so the filler
needs no shifting): for `i ≤ k`,
  `shiftFrom k (substFrom i u t) = substFrom i u (shiftFrom (k+1) t)`.
This is what lets `closeV`/`closeC` over a closed length-`Γ` environment produce a CLOSED term (the
`ret`/`case`/`split`/`vthunk` closedness obligations of the fundamental theorem). Mutual structural
induction; `i ≤ k` so the binder cases step both cutoffs uniformly (`i+1 ≤ k+1`). -/
-- ADR-0054/0055 identity dispatch: caps don't shift on handle-crossing, so the `handle` arm recurses
-- at the filler `u` UNCHANGED — no `shiftCap`, no `CapClosed` (the cap-shift theory is fully deleted).
mutual
theorem Val.shiftFrom_substFrom_closed :
    ∀ {u : Val}, Val.Closed u → ∀ (k i : Nat), i ≤ k → ∀ (t : Val),
      Val.shiftFrom k (Val.substFrom i u t) = Val.substFrom i u (Val.shiftFrom (k + 1) t)
  | _, _,  _, _, _,    .vunit => rfl
  | _, _,  _, _, _,    .vint _ => rfl
  | _, _,  _, _, _,    .vcap _ _ => rfl   -- a capability is shift/subst-fixed (closed identity, ADR-0054)
  | u, hu, k, i, hik,  .vvar j => by
      -- arithmetic: the subst removes index i; the shift bumps indices ≥ k+1. With i ≤ k they don't
      -- interfere, and at j = i the closed filler u is shift-fixed.
      rcases Nat.lt_trichotomy j i with hji | hji | hji
      · -- j < i ≤ k: subst leaves vvar j (j<i); shift k leaves it (j<k); RHS shift(k+1) + subst leave it.
        rw [Val.substFrom, if_neg (by omega), if_neg (by omega),
          Val.shiftFrom, if_pos (by omega : j < k),
          Val.shiftFrom, if_pos (by omega : j < k + 1),
          Val.substFrom, if_neg (by omega), if_neg (by omega)]
      · -- j = i: subst → u (closed, shift-fixed); RHS shift (k+1) leaves vvar i (i ≤ k < k+1) then subst → u.
        subst hji
        rw [Val.substFrom, if_pos rfl, hu.shiftFrom_eq,
          Val.shiftFrom, if_pos (by omega : j < k + 1), Val.substFrom, if_pos rfl]
      · -- j > i: subst → vvar (j-1); shift depends on j-1 vs k. RHS: shift (k+1) of vvar j, then subst.
        rw [Val.substFrom, if_neg (by omega), if_pos (by omega : j > i)]
        rcases Nat.lt_or_ge j (k + 1) with hjk | hjk
        · -- j < k+1 ⟹ j-1 < k: shift leaves vvar (j-1); RHS shift leaves vvar j, subst → vvar (j-1).
          rw [Val.shiftFrom, if_pos (by omega : j - 1 < k),
            Val.shiftFrom, if_pos (by omega : j < k + 1),
            Val.substFrom, if_neg (by omega), if_pos (by omega : j > i)]
        · -- j ≥ k+1 ⟹ j-1 ≥ k: shift bumps to vvar j; RHS shift bumps to vvar (j+1), subst → vvar j.
          rw [Val.shiftFrom, if_neg (by omega : ¬ j - 1 < k),
            Val.shiftFrom, if_neg (by omega : ¬ j < k + 1),
            Val.substFrom, if_neg (by omega), if_pos (by omega : j + 1 > i),
            show j - 1 + 1 = j + 1 - 1 by omega]
  | u, hu, k, i, hik,  .vthunk M => by
      simp only [Val.shiftFrom, Val.substFrom]
      rw [Comp.shiftFrom_substFrom_closed hu k i hik M]
  | u, hu, k, i, hik,  .inl w => by
      simp only [Val.shiftFrom, Val.substFrom]; rw [Val.shiftFrom_substFrom_closed hu k i hik w]
  | u, hu, k, i, hik,  .inr w => by
      simp only [Val.shiftFrom, Val.substFrom]; rw [Val.shiftFrom_substFrom_closed hu k i hik w]
  | u, hu, k, i, hik,  .pair a b => by
      simp only [Val.shiftFrom, Val.substFrom]
      rw [Val.shiftFrom_substFrom_closed hu k i hik a, Val.shiftFrom_substFrom_closed hu k i hik b]
  | u, hu, k, i, hik,  .fold w => by
      simp only [Val.shiftFrom, Val.substFrom]; rw [Val.shiftFrom_substFrom_closed hu k i hik w]

theorem Comp.shiftFrom_substFrom_closed :
    ∀ {u : Val}, Val.Closed u → ∀ (k i : Nat), i ≤ k → ∀ (t : Comp),
      Comp.shiftFrom k (Comp.substFrom i u t) = Comp.substFrom i u (Comp.shiftFrom (k + 1) t)
  | u, hu, k, i, hik, .ret w => by
      simp only [Comp.shiftFrom, Comp.substFrom]; rw [Val.shiftFrom_substFrom_closed hu k i hik w]
  | u, hu, k, i, hik, .binop op a b => by
      simp only [Comp.shiftFrom, Comp.substFrom]
      rw [Val.shiftFrom_substFrom_closed hu k i hik a, Val.shiftFrom_substFrom_closed hu k i hik b]
  | u, hu, k, i, hik, .letC M N => by
      simp only [Comp.shiftFrom, Comp.substFrom, hu.shift]
      rw [Comp.shiftFrom_substFrom_closed hu k i hik M,
        Comp.shiftFrom_substFrom_closed hu (k + 1) (i + 1) (by omega) N]
  | u, hu, k, i, hik, .force w => by
      simp only [Comp.shiftFrom, Comp.substFrom]; rw [Val.shiftFrom_substFrom_closed hu k i hik w]
  | u, hu, k, i, hik, .lam M => by
      simp only [Comp.shiftFrom, Comp.substFrom, hu.shift]
      rw [Comp.shiftFrom_substFrom_closed hu (k + 1) (i + 1) (by omega) M]
  | u, hu, k, i, hik, .app M w => by
      simp only [Comp.shiftFrom, Comp.substFrom]
      rw [Comp.shiftFrom_substFrom_closed hu k i hik M, Val.shiftFrom_substFrom_closed hu k i hik w]
  | u, hu, k, i, hik, .perform cp op w => by
      simp only [Comp.shiftFrom, Comp.substFrom]
      rw [Val.shiftFrom_substFrom_closed hu k i hik cp, Val.shiftFrom_substFrom_closed hu k i hik w]
  | u, hu, k, i, hik, .handle h M => by
      -- ADR-0054: `handle` BINDS the capability at index 0, so the body `M` descends under one binder
      -- (`k+1`/`i+1`), exactly like `lam`/`letC`; the handler `h` does NOT bind (stays at `k`). Closed
      -- filler is shift-fixed (`hu.shift`).
      simp only [Comp.shiftFrom, Comp.substFrom, hu.shift]
      rw [Handler.shiftFrom_substFrom_closed hu k i hik h,
        Comp.shiftFrom_substFrom_closed hu (k + 1) (i + 1) (by omega) M]
  | u, hu, k, i, hik, .case w N₁ N₂ => by
      simp only [Comp.shiftFrom, Comp.substFrom, hu.shift]
      rw [Val.shiftFrom_substFrom_closed hu k i hik w,
        Comp.shiftFrom_substFrom_closed hu (k + 1) (i + 1) (by omega) N₁,
        Comp.shiftFrom_substFrom_closed hu (k + 1) (i + 1) (by omega) N₂]
  | u, hu, k, i, hik, .split w N => by
      simp only [Comp.shiftFrom, Comp.substFrom, hu.shift]
      rw [Val.shiftFrom_substFrom_closed hu k i hik w,
        Comp.shiftFrom_substFrom_closed hu (k + 2) (i + 2) (by omega) N]
  | u, hu, k, i, hik, .unfold w => by
      simp only [Comp.shiftFrom, Comp.substFrom]; rw [Val.shiftFrom_substFrom_closed hu k i hik w]
  | _, _, _, _, _, .oom => rfl
  | _, _, _, _, _, .wrong _ => rfl

theorem Handler.shiftFrom_substFrom_closed :
    ∀ {u : Val}, Val.Closed u → ∀ (k i : Nat), i ≤ k → ∀ (h : Handler),
      Handler.shiftFrom k (Handler.substFrom i u h) = Handler.substFrom i u (Handler.shiftFrom (k + 1) h)
  | u, hu, k, i, hik, .state ℓ s => by
      simp only [Handler.shiftFrom, Handler.substFrom]; rw [Val.shiftFrom_substFrom_closed hu k i hik s]
  | _, _, _, _, _, .throws _ => rfl
  | _, _, _, _, _, .transaction _ _ => rfl
  | _, _, _, _, _, .custom _ _ _ => rfl   -- shift/subst both identity on custom (ADR-0085 stage 1)
  | _, _, _, _, _, .customUpd _ _ _ => rfl   -- customUpd (ADR-0107 D5): identity like `custom`
end

/-- `v` is SCOPED IN `m`: no free de Bruijn index `≥ m` is exposed (`shiftFrom k` fixes `v` for `k ≥ m`).
`ScopedIn 0 = Closed`. A well-typed value `HasVTy γ Γ v A` is `ScopedIn Γ.length` (`HasVTy.shift_closed`),
so the fundamental induction gets its scope bound from typing, not a fresh syntactic analysis. -/
def Val.ScopedIn (m : Nat) (v : Val) : Prop := ∀ k, m ≤ k → Val.shiftFrom k v = v

/-- Substituting the level-0 binder of an `(m+1)`-scoped value with a CLOSED filler drops the scope to
`m`. Uses the shift/subst commutation: `shiftFrom k (subst u v) = subst u (shiftFrom (k+1) v) = subst u v`
for `k ≥ m` (since `v` is `(m+1)`-scoped and `k+1 ≥ m+1`). -/
theorem Val.ScopedIn.subst_closed {m : Nat} {u v : Val} (hu : Val.Closed u)
    (hv : Val.ScopedIn (m + 1) v) : Val.ScopedIn m (Val.subst u v) := by
  intro k hk
  rw [Val.subst, Val.shiftFrom_substFrom_closed hu k 0 (Nat.zero_le k) v, hv (k + 1) (by omega)]


/-! ADR-0054/0055 (identity dispatch): the whole cap-shift theory is DELETED — `shiftCapFrom`/`shiftCap`
on `Val/Comp/Handler`, the `shiftCapFrom_shiftFrom`/`_swap` commutations, the `Closed.shiftCap` helper,
and the route-A `Val.CapScopedIn`/`Val.CapClosed` family (`closeV_capClosed_scoped`). Caps are now
identity-keyed (a global-fresh `Nat` minted at `handle`), not positional: `substFrom` leaves the
`handle` body's caps UNCHANGED, so there is no shift↔subst commutation to maintain and the LR handler
arms close on the UNSHIFTED `closeC δ M` (`closeC_handle*`). Route-A `CapClosed` was build-refuted
(ADR-0050); the residual shift-only lemmas were swept here (inc-5). -/

/-- Closing a value SCOPED IN `δ.length` over a CLOSED environment yields a CLOSED value: the fold
substitutes each free index with a closed filler, dropping the scope by 1 each step to `ScopedIn 0` =
`Closed`. The `ret`/`case`/`split`/`vthunk` closedness obligations of the fundamental theorem. -/
theorem closeV_closed_scoped : ∀ {δ : List Val} {v : Val},
    (∀ u ∈ δ, Val.Closed u) → Val.ScopedIn δ.length v →
      Val.Closed (closeV δ v)
  | [],     v, _,  hv => fun k => hv k (Nat.zero_le k)
  | u :: δ, v, hδ, hv => by
      have hu : Val.Closed u := hδ u List.mem_cons_self
      have hδ' : ∀ w ∈ δ, Val.Closed w := fun w hw => hδ w (List.mem_cons_of_mem u hw)
      rw [closeV]
      exact closeV_closed_scoped hδ' (Val.ScopedIn.subst_closed hu (by
        simpa only [List.length_cons] using hv))


/-- Closing `vvar i` over a CLOSED environment picks out the `i`-th filler (innermost = index 0). The
fold substitutes `δ[0]` at 0 (hitting `vvar 0`), else decrements and recurses — and once a closed filler
is substituted in, the remaining fold leaves it fixed (`closeV_closed`). In range (`i < δ.length`). -/
theorem closeV_vvar {δ : List Val} (hδ : ∀ u ∈ δ, Val.Closed u) :
    ∀ {i : Nat}, i < δ.length → ∀ (d : Val), closeV δ (Val.vvar i) = δ[i]?.getD d := by
  induction δ with
  | nil => intro i hi; exact absurd hi (by simp)
  | cons u δ ih =>
      intro i hi d
      have hu : Val.Closed u := hδ u List.mem_cons_self
      have hδ' : ∀ w ∈ δ, Val.Closed w := fun w hw => hδ w (List.mem_cons_of_mem u hw)
      cases i with
      | zero =>
          -- closeV (u::δ) (vvar 0) = closeV δ (subst u (vvar 0)) = closeV δ u = u (u closed).
          rw [closeV, show Val.subst u (Val.vvar 0) = u from by rw [Val.subst, Val.substFrom, if_pos rfl]]
          rw [closeV_closed hu δ]; rfl
      | succ k =>
          -- closeV (u::δ) (vvar (k+1)) = closeV δ (vvar k) = δ[k] = (u::δ)[k+1].
          rw [closeV, show Val.subst u (Val.vvar (k + 1)) = Val.vvar k from by
            rw [Val.subst, Val.substFrom, if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel]]
          rw [ih hδ' (by simp only [List.length_cons] at hi; omega) d]; rfl

@[simp] theorem closeV_vthunk (δ : List Val) (c : Comp) :
    closeV δ (Val.vthunk c) = Val.vthunk (closeC δ c) := by
  induction δ generalizing c with
  | nil => rfl
  | cons v δ ih => simp only [closeV, closeC, Val.subst, Val.substFrom, Comp.subst]; exact ih _

@[simp] theorem closeV_inl (δ : List Val) (w : Val) :
    closeV δ (Val.inl w) = Val.inl (closeV δ w) := by
  induction δ generalizing w with
  | nil => rfl
  | cons v δ ih => simp only [closeV, Val.subst, Val.substFrom]; exact ih _

@[simp] theorem closeV_inr (δ : List Val) (w : Val) :
    closeV δ (Val.inr w) = Val.inr (closeV δ w) := by
  induction δ generalizing w with
  | nil => rfl
  | cons v δ ih => simp only [closeV, Val.subst, Val.substFrom]; exact ih _

@[simp] theorem closeV_pair (δ : List Val) (a b : Val) :
    closeV δ (Val.pair a b) = Val.pair (closeV δ a) (closeV δ b) := by
  induction δ generalizing a b with
  | nil => rfl
  | cons v δ ih => simp only [closeV, Val.subst, Val.substFrom]; exact ih _ _

@[simp] theorem closeV_fold (δ : List Val) (w : Val) :
    closeV δ (Val.fold w) = Val.fold (closeV δ w) := by
  induction δ generalizing w with
  | nil => rfl
  | cons v δ ih => simp only [closeV, Val.subst, Val.substFrom]; exact ih _

/-! ### B.1b BINDING-former `closeC` distribution (`closeCUnderBinders`)

`closeC` pushes under a binder by re-indexing the environment: the sub-term under `d` fresh binders is
closed by `closeCUnderBinders d` (level-`d` subst with `shiftN d`-weakened fillers). These are STRUCTURAL
(induction on δ, the single `Comp.substFrom 0` step unfolds to the binding former's `substFrom` clause);
NO closedness is consumed — they just name the binder-side fold. `shiftN 1 v = Val.shift v` /
`shiftN 2 v = Val.shift (Val.shift v)` make the level-1/level-2 steps line up with the kernel's
`Comp.substFrom` clauses for `letC`/`lam`/`case` (d=1) and `split` (d=2) definitionally. -/

theorem closeC_letC (δ : List Val) (M N : Comp) :
    closeC δ (Comp.letC M N) = Comp.letC (closeC δ M) (closeCUnderBinders 1 δ N) := by
  induction δ generalizing M N with
  | nil => rfl
  | cons v δ ih =>
    simp only [closeC, closeCUnderBinders, Comp.subst, Comp.substFrom, shiftN]
    exact ih _ _

theorem closeC_lam (δ : List Val) (M : Comp) :
    closeC δ (Comp.lam M) = Comp.lam (closeCUnderBinders 1 δ M) := by
  induction δ generalizing M with
  | nil => rfl
  | cons v δ ih =>
    simp only [closeC, closeCUnderBinders, Comp.subst, Comp.substFrom, shiftN]
    exact ih _

theorem closeC_case (δ : List Val) (w : Val) (N₁ N₂ : Comp) :
    closeC δ (Comp.case w N₁ N₂)
      = Comp.case (closeV δ w) (closeCUnderBinders 1 δ N₁) (closeCUnderBinders 1 δ N₂) := by
  induction δ generalizing w N₁ N₂ with
  | nil => rfl
  | cons v δ ih =>
    simp only [closeC, closeV, closeCUnderBinders, Comp.subst, Val.subst, Comp.substFrom, shiftN]
    exact ih _ _ _

theorem closeC_split (δ : List Val) (w : Val) (N : Comp) :
    closeC δ (Comp.split w N) = Comp.split (closeV δ w) (closeCUnderBinders 2 δ N) := by
  induction δ generalizing w N with
  | nil => rfl
  | cons v δ ih =>
    simp only [closeC, closeV, closeCUnderBinders, Comp.subst, Val.subst, Comp.substFrom, shiftN]
    exact ih _ _


/-! ### B.1c The single-binder substitution-commutation core

`closeC_subst_comm` reduces (by induction on δ) to a single de Bruijn fact: filling a level-1 binder
with a CLOSED `v` then a level-0 binder with a CLOSED `w` is the same as filling level-0 with `w` then
level-0 with `v`. Both fillers must be closed: the second substitution traverses INTO the first's
filler, so each must be shift-invariant (closed) to survive the other's renumbering. This is faithful —
the values flowing through the CK machine's binders (a returned value, an env filler) are always closed
(ADR-0025/0030, the carrier now enforced in `Krel`/`Srel`/`EnvRel`).

  de Bruijn substitution lemma (Pierce TAPL §6.2 / autosubst `subst_comp`), specialized to two closed
  fillers so neither shift survives. Proved by mutual structural induction, cutoff `k` generalized. -/

-- For CLOSED `v,w`: `substFrom k w (substFrom (k+1) v M) = substFrom k v (substFrom k w M)`. The
-- cutoff `k` is generalized so the binder cases (which step to `k+1` with `shift v`/`shift w` = `v`/`w`)
-- reuse the IH at the SAME fillers. Mutual with the `Val`/`Handler` analogues.
-- ADR-0054: `handle` BINDS the capability at index 0, so the `handle` arm descends the body under one
-- binder (`k+1`) with the shifted fillers — but the fillers are CLOSED (`hv.shift`/`hw.shift`), so the IH
-- recurses at `v`/`w` unchanged, exactly like `lam`/`letC`. No cap-shift (that machinery is gone).
mutual
theorem Val.substFrom_swap_closed :
    ∀ {v w : Val}, Val.Closed v → Val.Closed w → ∀ (k : Nat) (t : Val),
      Val.substFrom k w (Val.substFrom (k + 1) v t) = Val.substFrom k v (Val.substFrom k w t)
  | _, _, _, _, _, .vunit => rfl
  | _, _, _, _, _, .vint _ => rfl
  | _, _, _, _, _, .vcap _ _ => rfl
  | v, w, hv, hw, k, .vvar i => by
      -- both substs on a variable reduce to nested `if`s over `i vs k`/`k+1`; `split_ifs` + `omega`
      -- discharges the index arithmetic. In the two FILLED-SLOT branches the outer subst lands on a
      -- closed filler, fixed by `Closed.subst_at`; elsewhere it lands on another `vvar` (reduce again).
      rcases Nat.lt_trichotomy i k with hlt | heq | hgt
      · -- i < k < k+1: every `if` takes its `else`; both sides are `vvar i`.
        simp only [Val.substFrom, if_neg (show ¬ i = k + 1 by omega), if_neg (show ¬ i > k + 1 by omega),
          if_neg (show ¬ i = k by omega), if_neg (show ¬ i > k by omega)]
      · -- i = k: LHS → w; RHS → `substFrom k v w` = w (w closed).
        subst heq
        simp only [Val.substFrom, if_neg (show ¬ i = i + 1 by omega), if_neg (show ¬ i > i + 1 by omega),
          if_true, hw.subst_at i v]
      · rcases Nat.lt_trichotomy i (k + 1) with hk1 | heq1 | hgt1
        · omega
        · -- i = k+1: LHS → `substFrom k w v` = v (v closed); RHS → vvar k → v.
          subst heq1
          simp only [Val.substFrom, if_true, hv.subst_at k w,
            if_neg (show ¬ k + 1 = k by omega), if_pos (show k + 1 > k by omega), Nat.add_sub_cancel]
        · -- i > k+1: both substs decrement; both sides reach `vvar (i-2)`.
          simp only [Val.substFrom, if_neg (show ¬ i = k + 1 by omega), if_pos (show i > k + 1 by omega),
            if_neg (show ¬ i = k by omega), if_pos (show i > k by omega),
            if_neg (show ¬ i - 1 = k by omega), if_pos (show i - 1 > k by omega)]
  | v, w, hv, hw, k, .vthunk M => by
      simp only [Val.substFrom]; rw [Comp.substFrom_swap_closed hv hw k M]
  | v, w, hv, hw, k, .inl u => by simp only [Val.substFrom]; rw [Val.substFrom_swap_closed hv hw k u]
  | v, w, hv, hw, k, .inr u => by simp only [Val.substFrom]; rw [Val.substFrom_swap_closed hv hw k u]
  | v, w, hv, hw, k, .pair u₁ u₂ => by
      simp only [Val.substFrom]
      rw [Val.substFrom_swap_closed hv hw k u₁, Val.substFrom_swap_closed hv hw k u₂]
  | v, w, hv, hw, k, .fold u => by simp only [Val.substFrom]; rw [Val.substFrom_swap_closed hv hw k u]

theorem Comp.substFrom_swap_closed :
    ∀ {v w : Val}, Val.Closed v → Val.Closed w → ∀ (k : Nat) (t : Comp),
      Comp.substFrom k w (Comp.substFrom (k + 1) v t) = Comp.substFrom k v (Comp.substFrom k w t)
  | v, w, hv, hw, k, .ret u => by simp only [Comp.substFrom]; rw [Val.substFrom_swap_closed hv hw k u]
  | v, w, hv, hw, k, .binop op a b => by
      simp only [Comp.substFrom]; rw [Val.substFrom_swap_closed hv hw k a, Val.substFrom_swap_closed hv hw k b]
  | v, w, hv, hw, k, .letC M N => by
      simp only [Comp.substFrom, hv.shift, hw.shift]
      rw [Comp.substFrom_swap_closed hv hw k M, Comp.substFrom_swap_closed hv hw (k + 1) N]
  | v, w, hv, hw, k, .force u => by simp only [Comp.substFrom]; rw [Val.substFrom_swap_closed hv hw k u]
  | v, w, hv, hw, k, .lam M => by
      simp only [Comp.substFrom, hv.shift, hw.shift]
      rw [Comp.substFrom_swap_closed hv hw (k + 1) M]
  | v, w, hv, hw, k, .app M u => by
      simp only [Comp.substFrom]
      rw [Comp.substFrom_swap_closed hv hw k M, Val.substFrom_swap_closed hv hw k u]
  | v, w, hv, hw, k, .perform cp op u => by
      simp only [Comp.substFrom]
      rw [Val.substFrom_swap_closed hv hw k cp, Val.substFrom_swap_closed hv hw k u]
  | v, w, hv, hw, k, .handle h M => by
      -- ADR-0054: `handle` BINDS the cap at 0, so the body descends to `k+1` with shifted fillers; the
      -- fillers are CLOSED (`hv.shift`/`hw.shift`), so the IH recurses at `v`/`w` directly (mirror `lam`).
      simp only [Comp.substFrom, hv.shift, hw.shift]
      rw [Handler.substFrom_swap_closed hv hw k h, Comp.substFrom_swap_closed hv hw (k + 1) M]
  | v, w, hv, hw, k, .case u N₁ N₂ => by
      simp only [Comp.substFrom, hv.shift, hw.shift]
      rw [Val.substFrom_swap_closed hv hw k u,
        Comp.substFrom_swap_closed hv hw (k + 1) N₁, Comp.substFrom_swap_closed hv hw (k + 1) N₂]
  | v, w, hv, hw, k, .split u N => by
      simp only [Comp.substFrom, hv.shift, hw.shift]
      rw [Val.substFrom_swap_closed hv hw k u, Comp.substFrom_swap_closed hv hw (k + 2) N]
  | v, w, hv, hw, k, .unfold u => by simp only [Comp.substFrom]; rw [Val.substFrom_swap_closed hv hw k u]
  | _, _, _, _, _, .oom => rfl
  | _, _, _, _, _, .wrong _ => rfl

theorem Handler.substFrom_swap_closed :
    ∀ {v w : Val}, Val.Closed v → Val.Closed w → ∀ (k : Nat) (h : Handler),
      Handler.substFrom k w (Handler.substFrom (k + 1) v h) = Handler.substFrom k v (Handler.substFrom k w h)
  | v, w, hv, hw, k, .state ℓ s => by simp only [Handler.substFrom]; rw [Val.substFrom_swap_closed hv hw k s]
  | _, _, _, _, _, .throws _ => rfl
  | _, _, _, _, _, .transaction _ _ => rfl
  | _, _, _, _, _, .custom _ _ _ => rfl   -- subst identity on custom (ADR-0085 stage 1)
  | _, _, _, _, _, .customUpd _ _ _ => rfl   -- customUpd (ADR-0107 D5): identity like `custom`
end

/-! ### B.1c′ NON-ADJACENT substitution-swap (for the d=2 `split` descent)

`closeC_subst2_comm` (the `split` case) fills two level-0 binders through `closeCUnderBinders 2`, which
after the first descent leaves the two substitutions at NON-adjacent levels (0 and `d+1`). The adjacent
swap above (`i, i+1`) doesn't reach it, so here is the general `i ≤ j` form, both fillers CLOSED:
  `substFrom i w (substFrom (j+1) u t) = substFrom j u (substFrom i w t)`.
The adjacent lemma is the `i = j` instance; this generalizes the cutoff gap. Mutual structural
induction; the binder cases step BOTH cutoffs (`i+1 ≤ j+1`). -/
-- ADR-0054: `handle` BINDS the cap at 0, so the `handle` arm descends both bodies to `i+1`/`j+1`; the
-- fillers are CLOSED, so the IH recurses at `u`/`w` unchanged (mirror `lam`/`letC`). No cap-shift.
mutual
theorem Val.substFrom_swap_closed_ge :
    ∀ {u w : Val}, Val.Closed u → Val.Closed w → ∀ (i j : Nat), i ≤ j → ∀ (t : Val),
      Val.substFrom i w (Val.substFrom (j + 1) u t) = Val.substFrom j u (Val.substFrom i w t)
  | _, _, _, _, _, _, _,   .vunit => rfl
  | _, _, _, _, _, _, _,   .vint _ => rfl
  | _, _, _, _, _, _, _,   .vcap _ _ => rfl
  | u, w, hu, hw, i, j, hij, .vvar m => by
      -- the two substs remove levels i and j+1 (i ≤ j), renumbering disjointly; at the removed slots
      -- the closed fillers w (at i) / u (at j+1) are subst-fixed.
      rcases Nat.lt_trichotomy m i with hmi | hmi | hmi
      · -- m < i ≤ j: untouched by all four `if`s.
        simp only [Val.substFrom, if_neg (show ¬ m = j + 1 by omega), if_neg (show ¬ m > j + 1 by omega),
          if_neg (show ¬ m = i by omega), if_neg (show ¬ m > i by omega),
          if_neg (show ¬ m = j by omega), if_neg (show ¬ m > j by omega)]
      · -- m = i: LHS subst(j+1) keeps vvar i, subst i → w. RHS subst i → w, subst j fixes w (closed).
        subst hmi
        simp only [Val.substFrom, if_neg (show ¬ m = j + 1 by omega),
          if_neg (show ¬ m > j + 1 by omega), if_true]
        rw [hw.subst_at j u]
      · rcases Nat.lt_trichotomy m (j + 1) with hmj | hmj | hmj
        · -- i < m ≤ j: subst(j+1) keeps vvar m; subst i → vvar (m-1); RHS → vvar (m-1) (m-1<j? m≤j so m-1<j or =).
          simp only [Val.substFrom, if_neg (show ¬ m = j + 1 by omega), if_neg (show ¬ m > j + 1 by omega),
            if_neg (show ¬ m = i by omega), if_pos (show m > i by omega),
            if_neg (show ¬ m - 1 = j by omega), if_neg (show ¬ m - 1 > j by omega)]
        · -- m = j+1: LHS subst(j+1) → u, subst i fixes u (closed). RHS subst i → vvar j, subst j → u.
          subst hmj
          simp only [Val.substFrom, if_true,
            if_neg (show ¬ j + 1 = i by omega), if_pos (show j + 1 > i by omega), Nat.add_sub_cancel]
          rw [hu.subst_at i w]
        · -- m > j+1: both decrement; vvar (m-2) each side.
          simp only [Val.substFrom, if_neg (show ¬ m = j + 1 by omega), if_pos (show m > j + 1 by omega),
            if_neg (show ¬ m - 1 = i by omega), if_pos (show m - 1 > i by omega),
            if_neg (show ¬ m = i by omega), if_pos (show m > i by omega),
            if_neg (show ¬ m - 1 = j by omega), if_pos (show m - 1 > j by omega)]
  | u, w, hu, hw, i, j, hij, .vthunk M => by
      simp only [Val.substFrom]; rw [Comp.substFrom_swap_closed_ge hu hw i j hij M]
  | u, w, hu, hw, i, j, hij, .inl t => by simp only [Val.substFrom]; rw [Val.substFrom_swap_closed_ge hu hw i j hij t]
  | u, w, hu, hw, i, j, hij, .inr t => by simp only [Val.substFrom]; rw [Val.substFrom_swap_closed_ge hu hw i j hij t]
  | u, w, hu, hw, i, j, hij, .pair a b => by
      simp only [Val.substFrom]
      rw [Val.substFrom_swap_closed_ge hu hw i j hij a, Val.substFrom_swap_closed_ge hu hw i j hij b]
  | u, w, hu, hw, i, j, hij, .fold t => by simp only [Val.substFrom]; rw [Val.substFrom_swap_closed_ge hu hw i j hij t]

theorem Comp.substFrom_swap_closed_ge :
    ∀ {u w : Val}, Val.Closed u → Val.Closed w → ∀ (i j : Nat), i ≤ j → ∀ (t : Comp),
      Comp.substFrom i w (Comp.substFrom (j + 1) u t) = Comp.substFrom j u (Comp.substFrom i w t)
  | u, w, hu, hw, i, j, hij, .ret t => by simp only [Comp.substFrom]; rw [Val.substFrom_swap_closed_ge hu hw i j hij t]
  | u, w, hu, hw, i, j, hij, .binop op a b => by
      simp only [Comp.substFrom]
      rw [Val.substFrom_swap_closed_ge hu hw i j hij a, Val.substFrom_swap_closed_ge hu hw i j hij b]
  | u, w, hu, hw, i, j, hij, .letC M N => by
      simp only [Comp.substFrom, hu.shift, hw.shift]
      rw [Comp.substFrom_swap_closed_ge hu hw i j hij M,
        Comp.substFrom_swap_closed_ge hu hw (i + 1) (j + 1) (by omega) N]
  | u, w, hu, hw, i, j, hij, .force t => by simp only [Comp.substFrom]; rw [Val.substFrom_swap_closed_ge hu hw i j hij t]
  | u, w, hu, hw, i, j, hij, .lam M => by
      simp only [Comp.substFrom, hu.shift, hw.shift]
      rw [Comp.substFrom_swap_closed_ge hu hw (i + 1) (j + 1) (by omega) M]
  | u, w, hu, hw, i, j, hij, .app M t => by
      simp only [Comp.substFrom]
      rw [Comp.substFrom_swap_closed_ge hu hw i j hij M, Val.substFrom_swap_closed_ge hu hw i j hij t]
  | u, w, hu, hw, i, j, hij, .perform cp op t => by
      simp only [Comp.substFrom]
      rw [Val.substFrom_swap_closed_ge hu hw i j hij cp, Val.substFrom_swap_closed_ge hu hw i j hij t]
  | u, w, hu, hw, i, j, hij, .handle h M => by
      -- ADR-0054: `handle` BINDS the cap at 0, so the body descends to `i+1`/`j+1` with shifted fillers;
      -- the fillers are CLOSED (`hu.shift`/`hw.shift`), so the IH recurses at `u`/`w` directly (mirror `lam`).
      simp only [Comp.substFrom, hu.shift, hw.shift]
      rw [Handler.substFrom_swap_closed_ge hu hw i j hij h,
        Comp.substFrom_swap_closed_ge hu hw (i + 1) (j + 1) (by omega) M]
  | u, w, hu, hw, i, j, hij, .case t N₁ N₂ => by
      simp only [Comp.substFrom, hu.shift, hw.shift]
      rw [Val.substFrom_swap_closed_ge hu hw i j hij t,
        Comp.substFrom_swap_closed_ge hu hw (i + 1) (j + 1) (by omega) N₁,
        Comp.substFrom_swap_closed_ge hu hw (i + 1) (j + 1) (by omega) N₂]
  | u, w, hu, hw, i, j, hij, .split t N => by
      simp only [Comp.substFrom, hu.shift, hw.shift]
      rw [Val.substFrom_swap_closed_ge hu hw i j hij t,
        Comp.substFrom_swap_closed_ge hu hw (i + 2) (j + 2) (by omega) N]
  | u, w, hu, hw, i, j, hij, .unfold t => by simp only [Comp.substFrom]; rw [Val.substFrom_swap_closed_ge hu hw i j hij t]
  | _, _, _, _, _, _, _, .oom => rfl
  | _, _, _, _, _, _, _, .wrong _ => rfl

theorem Handler.substFrom_swap_closed_ge :
    ∀ {u w : Val}, Val.Closed u → Val.Closed w → ∀ (i j : Nat), i ≤ j → ∀ (h : Handler),
      Handler.substFrom i w (Handler.substFrom (j + 1) u h)
        = Handler.substFrom j u (Handler.substFrom i w h)
  | u, w, hu, hw, i, j, hij, .state ℓ s => by
      simp only [Handler.substFrom]; rw [Val.substFrom_swap_closed_ge hu hw i j hij s]
  | _, _, _, _, _, _, _, .throws _ => rfl
  | _, _, _, _, _, _, _, .transaction _ _ => rfl
  | _, _, _, _, _, _, _, .custom _ _ _ => rfl   -- subst identity on custom (ADR-0085 stage 1)
  | _, _, _, _, _, _, _, .customUpd _ _ _ => rfl   -- customUpd (ADR-0107 D5): identity like `custom`
end

/-! ### B.1d The substitution-descent crux (`closeC_subst_comm`)

The lemma every BINDER case of `lr_fundamental` consumes: closing a body UNDER one binder and then
filling the binder with `w` equals substituting `w` first and then closing. For a CLOSED environment the
binder-side weakening `shiftN 1` vanishes (`shiftN_closed`), so `closeCUnderBinders 1 δ` substitutes the
SAME fillers as `closeC δ` but at level 1; the level-0 `Comp.subst w` then commutes past each via
`Comp.substFrom_swap_closed` (both fillers closed).

  shape: biernacki-popl18 §5.2 fundamental theorem — closing substitution `G⟦Γ⟧` commutes with the
         single binder-substitution introduced by `letC`/`lam`/`case`/`split` β-reduction. -/
theorem closeC_subst_comm {δ : List Val} (hδ : ∀ v ∈ δ, Val.Closed v)
    {w : Val} (hw : Val.Closed w)
    (N : Comp) :
    (closeCUnderBinders 1 δ N).subst w = closeC δ (Comp.subst w N) := by
  induction δ generalizing N with
  | nil => rfl
  | cons v δ ih =>
    have hv : Val.Closed v := hδ v List.mem_cons_self
    have hδ' : ∀ u ∈ δ, Val.Closed u := fun u hu => hδ u (List.mem_cons_of_mem v hu)
    -- LHS: closeCUnderBinders 1 (v::δ) N = closeCUnderBinders 1 δ (substFrom 1 v N)  [shiftN 1 v = v].
    -- RHS: closeC (v::δ) (subst w N) = closeC δ (subst v (subst w N)).
    simp only [closeCUnderBinders, closeC, shiftN, hv.shift]
    rw [ih hδ' (Comp.substFrom 1 v N)]
    -- goal: closeC δ (subst w (substFrom 1 v N)) = closeC δ (subst v (subst w N))
    congr 1
    -- subst w (substFrom 1 v N) = subst v (subst w N), i.e. the k=0 swap (closed v, w; route-B).
    exact Comp.substFrom_swap_closed hv hw 0 N

/-- General level-0 descent through `closeCUnderBinders (d+1)`: filling the outermost (level-0) binder
with a CLOSED `w` commutes past the `d+1`-level fillers (closed), dropping the binder-depth by one. The
engine behind `closeC_subst_comm` (d=0) and the d=2 `split` descent. Uses the NON-adjacent swap
(`Comp.substFrom_swap_closed_ge` at `i=0, j=d`). -/
theorem closeCUnderBinders_subst0 (d : Nat) {δ : List Val} (hδ : ∀ v ∈ δ, Val.Closed v)
    {w : Val} (hw : Val.Closed w)
    (N : Comp) :
    Comp.substFrom 0 w (closeCUnderBinders (d + 1) δ N)
      = closeCUnderBinders d δ (Comp.substFrom 0 w N) := by
  induction δ generalizing N with
  | nil => rfl
  | cons v δ ih =>
    have hv : Val.Closed v := hδ v List.mem_cons_self
    have hδ' : ∀ u ∈ δ, Val.Closed u := fun u hu => hδ u (List.mem_cons_of_mem v hu)
    -- closeCUnderBinders (d+1) (v::δ) N = closeCUnderBinders (d+1) δ (substFrom (d+1) v N)  [shiftN=v].
    -- closeCUnderBinders d (v::δ) (subst₀ w N) = closeCUnderBinders d δ (substFrom d v (subst₀ w N)).
    simp only [closeCUnderBinders, shiftN_closed hv]
    rw [ih hδ' (Comp.substFrom (d + 1) v N)]
    congr 1
    -- substFrom 0 w (substFrom (d+1) v N) = substFrom d v (substFrom 0 w N)  (non-adjacent swap, 0 ≤ d).
    exact Comp.substFrom_swap_closed_ge hv hw 0 d (Nat.zero_le d) N

/-- The d=2 substitution-descent for `split`: filling the TWO binders of `closeCUnderBinders 2 δ N`
(the inner with `Val.shift w`, the outer with `v`, matching the `split (pair v w) N ↦ subst v (subst
(shift w) N)` reduct) equals closing `subst v (subst w N)`. The two closed fillers and the closedness
of `w` (which collapses `Val.shift w = w`) make it go through via two `closeCUnderBinders_subst0`
descents. -/
theorem closeC_subst2_comm {δ : List Val} (hδ : ∀ u ∈ δ, Val.Closed u)
    {v w : Val} (hv : Val.Closed v) (hw : Val.Closed w) (N : Comp) :
    Comp.subst v (Comp.subst (Val.shift w) (closeCUnderBinders 2 δ N))
      = closeC δ (Comp.subst v (Comp.subst w N)) := by
  -- subst (shift w) = subst w (w closed); both `Comp.subst` are `substFrom 0`.
  rw [show Val.shift w = w from hw.shift]
  show Comp.substFrom 0 v (Comp.substFrom 0 w (closeCUnderBinders (1 + 1) δ N))
    = closeC δ (Comp.substFrom 0 v (Comp.substFrom 0 w N))
  -- inner descent (d=1): substFrom 0 w through closeCUnderBinders 2 = closeCUnderBinders 1 of the body.
  rw [closeCUnderBinders_subst0 1 hδ hw N]
  -- outer descent (d=0): substFrom 0 v through closeCUnderBinders 1 = closeCUnderBinders 0 = closeC.
  rw [closeCUnderBinders_subst0 0 hδ hv (Comp.substFrom 0 w N), closeCUnderBinders_zero]

end -- public section

end Bang
