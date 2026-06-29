/-
  Compat.lean — the Phase-B target list.
  `lr_fundamental` (Spec.lean) = induction over the typing derivation, one case
  per rule, each discharged by the matching lemma below. Proving all of these
  (in PROOF_ORDER) IS proving the fundamental theorem.

-/
-- Compat is a proof module UPSTREAM of Spec (sibling to Metatheory): Spec wires its frozen
-- `lr_fundamental`/`lr_sound` statements to the proofs assembled here (`:= lr_fundamental_proof`,
-- exactly as `preservation := preservation_proof`). So we import the DEFINITION layers, not Spec
-- (importing Spec would cycle once Spec imports Compat). Verified no cycle: Metatheory imports only
-- Core/Syntax/Operational; LR adds the relations; neither imports Spec.
module

public import Bang.Core.IR
public import Bang.Core.Typing
public import Bang.Core.Semantics
public import Bang.Meta.LR
public import Bang.Core.Soundness

namespace Bang

open Bang.EffectRow (Label)

-- Module reveal (Phase 1a). `@[expose] public section`: Compat's compatibility lemmas
-- (the STD compat block, KrelS/CrelK machinery) are unfolded by downstream Spec, so
-- bodies cross the boundary. Zero-external-ref proof-term lemmas → `private` (deferred).
@[expose] public section

variable {Eff  : Type} [Lattice Eff] [OrderBot Eff]
variable {Mult : Type} [CommSemiring Mult] [DecidableEq Mult]
variable [EffSig Eff Mult]


/-! ## B.0 Convergence anti-reduction infrastructure (the workhorse)

The fundamental theorem proves `Crel n B e c c` — a computation relates to ITSELF, but observed
through `Krel`-RELATED (not equal) stacks `K₁,K₂`. So each compat lemma is a CONGRUENCE: relatedness
of stacks lifts through the same head former. The biorthogonal relations are phrased over
fuel-bounded convergence (`CoApprox`/`Converges`), so the workhorse is a CONFIG-LEVEL anti-reduction:

  shape: pitts-step-indexed-biorthogonality / benton-hur-icfp09 — head-expansion closure.

A *context-independent head step* `c ↦ c'` (one that fires `step (K, c) = some (K, c')` for EVERY
stack `K`, e.g. `force (vthunk M) ↦ M`, `case (inl v) … ↦ N₁[v]`) makes `(K, c)` and `(K, c')`
co-converge with a ±1 fuel offset. The PUSH steps (`letC`/`app`/`handle`) are the other shape: they
move a frame onto the stack (`step (K, letC M N) = (letF N :: K, M)`), so `(K, plug-form)` reduces to
the focused subterm under an extended stack — handled by `Stack.plug` unfolding directly. -/

/-- A returned config converges iff its tail does, after one bind step — but the universal workhorse
is: a config that takes a fixed first step `(K,c) ↦ cfg'` converges iff `cfg'` does. -/
theorem converges_cfg_step (cfg cfg' : Config)
    (hstep : Source.step cfg = some cfg')
    (hne : ∀ g v, cfg ≠ (g, [], Comp.ret v)) :
    (∃ n w, Config.run n cfg = Result.done w) ↔ (∃ n w, Config.run n cfg' = Result.done w) := by
  constructor
  · rintro ⟨n, w, hn⟩
    cases n with
    | zero => simp [Config.run] at hn
    | succ m =>
        rw [Config.run_step m cfg hne, hstep] at hn
        exact ⟨m, w, hn⟩
  · rintro ⟨n, w, hn⟩
    refine ⟨n + 1, w, ?_⟩
    rw [Config.run_step n cfg hne, hstep]
    exact hn

/-- A *context-independent head step*: `c ↦ c'` fires under EVERY stack, and `c` is never a bare
returned focus (`ret v` would be terminal, not a redex). The non-PUSH reductions
(`force (vthunk M) ↦ M`, the ADT eliminators) have this shape: they rewrite the focus in place
without consulting the stack. -/
def CIStep (c c' : Comp) : Prop :=
  (∀ (g : Nat) (K : Stack), Source.step (g, K, c) = some (g, K, c')) ∧ (∀ v, c ≠ Comp.ret v)

-- NOTE (inc-5): the `converges_plug_step`/`converges_letF_ret`/`converges_appF_lam`/
-- `converges_handleF_ret` frame-reduce bridges were DELETED. They bridged through the old
-- `converges_plug_iff` (RHS = the raw `(K, c)` config), which LR rekeyed to the machine-shaped
-- reshape config (`handlerCount K, canonStack K c, capSubstInto K c`, ADR-0054/0055); the bridges had
-- zero consumers (the fundamental theorem now goes through the machine-shaped `KrelS`, not these
-- convergence bridges). `converges_cfg_step` (the general config-level head-step anti-reduction) and
-- `CIStep` (the context-independent head-step predicate, used by `CrelK_head_step`) are retained.

/-! ## B.1 The environment relation `EnvRel` / closing substitutions

`EnvRel`, `closeC`, `closeV` are defined in `Bang/LR.lean` (§5.2b) — they are LR machinery the FROZEN
`lr_fundamental` statement (`Spec.lean`, ADR-0034 env-closed form) references, so they must live in a
module `Spec.lean` imports. The fundamental theorem closes an OPEN sub-term over a pair of
`Vrel`-RELATED substitution environments δ₁,δ₂ (Biernacki/Ahmed `G⟦Γ⟧`): the bare `c c` self-relation
is unprovable for open `c` (a `vvar i` is not `Vrel`-related to itself), so the induction invariant is
`EnvRel n Γ δ₁ δ₂ → Crel n B e (closeC δ₁ c) (closeC δ₂ c)`. -/

/-! ### B.1a `closeC`/`closeV` commutation (the substitution-descent lemmas)

`closeC` is a fold of single `Comp.subst`s (innermost binder first), so it commutes with every
NON-binding former structurally (each `Comp.subst` pushes through, and the fold follows). These are
proved by induction on the environment `δ`, threading the single-step commutation
(`Comp.subst v (ret w) = ret (Val.subst v w)`, definitional) through the fold.

The BINDING formers (`letC`/`lam`/`case`/`split`) push `closeC` UNDER a binder: `Comp.subst v` becomes
`Comp.substFrom (0+d) (shiftN d v)` for a sub-term under `d` fresh binders (`d=1` for letC/lam/case,
`d=2` for split). We name that binder-side fold `closeCUnderBinders d` and prove the distribution
lemmas STRUCTURALLY (no closedness needed — they merely re-associate the fold under the binder). The
closedness carrier enters only in `closeC_subst_comm` (below), where it collapses the `shiftN d` so the
bound value can be filled. -/

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


/-! ### B.1a′ `EnvRel` accessors (closedness carrier, length, index)

The fundamental induction consumes the `EnvRel` carrier three ways: the fillers' CLOSEDNESS (feeds
`closeC_subst_comm` under binders), the LENGTH match with `Γ` (feeds `closeV_vvar`'s in-range
requirement), and the per-position `Vrel` (feeds the `vvar` leaf). All by induction on `Γ`/the lists. -/

/-- `EnvRel`'s left fillers are all closed (the `Val.Closed v₁` conjunct, harvested). -/
theorem EnvRel.closed_left {n : Nat} : ∀ {Γ : TyCtx Eff Mult} {δ₁ δ₂ : List Val},
    EnvRel n Γ δ₁ δ₂ → ∀ v ∈ δ₁, Val.Closed v
  | [],      [],        [],        _, v, hv => absurd hv (by simp)
  | _ :: Γ', v₁ :: δ₁', v₂ :: δ₂', h, v, hv => by
      rw [EnvRel] at h
      obtain ⟨hc₁, _, _, hrest⟩ := h
      rcases List.mem_cons.mp hv with rfl | hmem
      · exact hc₁
      · exact EnvRel.closed_left hrest v hmem

/-- `EnvRel`'s right fillers are all closed. -/
theorem EnvRel.closed_right {n : Nat} : ∀ {Γ : TyCtx Eff Mult} {δ₁ δ₂ : List Val},
    EnvRel n Γ δ₁ δ₂ → ∀ v ∈ δ₂, Val.Closed v
  | [],      [],        [],        _, v, hv => absurd hv (by simp)
  | _ :: Γ', v₁ :: δ₁', v₂ :: δ₂', h, v, hv => by
      rw [EnvRel] at h
      obtain ⟨_, hc₂, _, hrest⟩ := h
      rcases List.mem_cons.mp hv with rfl | hmem
      · exact hc₂
      · exact EnvRel.closed_right hrest v hmem

/-- `EnvRel` matches lengths: `δ₁.length = Γ.length` (and `δ₂`). -/
theorem EnvRel.length_left {n : Nat} : ∀ {Γ : TyCtx Eff Mult} {δ₁ δ₂ : List Val},
    EnvRel n Γ δ₁ δ₂ → δ₁.length = Γ.length
  | [],      [],        [],        _ => rfl
  | _ :: Γ', v₁ :: δ₁', v₂ :: δ₂', h => by
      rw [EnvRel] at h; simp only [List.length_cons]; rw [EnvRel.length_left h.2.2.2]
theorem EnvRel.length_right {n : Nat} : ∀ {Γ : TyCtx Eff Mult} {δ₁ δ₂ : List Val},
    EnvRel n Γ δ₁ δ₂ → δ₂.length = Γ.length
  | [],      [],        [],        _ => rfl
  | _ :: Γ', v₁ :: δ₁', v₂ :: δ₂', h => by
      rw [EnvRel] at h; simp only [List.length_cons]; rw [EnvRel.length_right h.2.2.2]

/-- The per-position `Vrel`: if `Γ[i]? = some A`, the `i`-th fillers are `Vrel n A`-related. -/
theorem EnvRel.vrel_at {n : Nat} : ∀ {Γ : TyCtx Eff Mult} {δ₁ δ₂ : List Val},
    EnvRel n Γ δ₁ δ₂ → ∀ {i : Nat} {A : VTy Eff Mult}, Γ[i]? = some A →
      ∀ (d₁ d₂ : Val), Vrel n A (δ₁[i]?.getD d₁) (δ₂[i]?.getD d₂)
  | [],      [],        [],        _, i, A, hΓ, _, _ => by simp at hΓ
  | A' :: Γ', v₁ :: δ₁', v₂ :: δ₂', h, i, A, hΓ, d₁, d₂ => by
      rw [EnvRel] at h
      obtain ⟨_, _, hv, hrest⟩ := h
      cases i with
      | zero => simp only [List.getElem?_cons_zero, Option.getD_some]
                simp only [List.getElem?_cons_zero, Option.some.injEq] at hΓ; subst hΓ; exact hv
      | succ k =>
          simp only [List.getElem?_cons_succ]
          simp only [List.getElem?_cons_succ] at hΓ
          exact EnvRel.vrel_at hrest hΓ d₁ d₂

/-! ◊4.5b `EnvRelK` helpers (mirror the `EnvRel` ones; the closed/length proofs are relation-agnostic,
`vrel_at` returns a `VrelK`). For the migrated `crelK_fund`/`vrelK_fund`. -/
theorem EnvRelK.closed_left {n : Nat} : ∀ {Γ : TyCtx Eff Mult} {δ₁ δ₂ : List Val},
    EnvRelK n Γ δ₁ δ₂ → ∀ v ∈ δ₁, Val.Closed v
  | [],      [],        [],        _, v, hv => absurd hv (by simp)
  | _ :: Γ', v₁ :: δ₁', v₂ :: δ₂', h, v, hv => by
      rw [EnvRelK] at h
      obtain ⟨hc₁, _, _, hrest⟩ := h
      rcases List.mem_cons.mp hv with rfl | hmem
      · exact hc₁
      · exact EnvRelK.closed_left hrest v hmem

theorem EnvRelK.closed_right {n : Nat} : ∀ {Γ : TyCtx Eff Mult} {δ₁ δ₂ : List Val},
    EnvRelK n Γ δ₁ δ₂ → ∀ v ∈ δ₂, Val.Closed v
  | [],      [],        [],        _, v, hv => absurd hv (by simp)
  | _ :: Γ', v₁ :: δ₁', v₂ :: δ₂', h, v, hv => by
      rw [EnvRelK] at h
      obtain ⟨_, hc₂, _, hrest⟩ := h
      rcases List.mem_cons.mp hv with rfl | hmem
      · exact hc₂
      · exact EnvRelK.closed_right hrest v hmem

theorem EnvRelK.length_left {n : Nat} : ∀ {Γ : TyCtx Eff Mult} {δ₁ δ₂ : List Val},
    EnvRelK n Γ δ₁ δ₂ → δ₁.length = Γ.length
  | [],      [],        [],        _ => rfl
  | _ :: Γ', v₁ :: δ₁', v₂ :: δ₂', h => by
      rw [EnvRelK] at h; simp only [List.length_cons]; rw [EnvRelK.length_left h.2.2.2]
theorem EnvRelK.length_right {n : Nat} : ∀ {Γ : TyCtx Eff Mult} {δ₁ δ₂ : List Val},
    EnvRelK n Γ δ₁ δ₂ → δ₂.length = Γ.length
  | [],      [],        [],        _ => rfl
  | _ :: Γ', v₁ :: δ₁', v₂ :: δ₂', h => by
      rw [EnvRelK] at h; simp only [List.length_cons]; rw [EnvRelK.length_right h.2.2.2]

theorem EnvRelK.vrel_at {n : Nat} : ∀ {Γ : TyCtx Eff Mult} {δ₁ δ₂ : List Val},
    EnvRelK n Γ δ₁ δ₂ → ∀ {i : Nat} {A : VTy Eff Mult}, Γ[i]? = some A →
      ∀ (d₁ d₂ : Val), VrelK n A (δ₁[i]?.getD d₁) (δ₂[i]?.getD d₂)
  | [],      [],        [],        _, i, A, hΓ, _, _ => by simp at hΓ
  | A' :: Γ', v₁ :: δ₁', v₂ :: δ₂', h, i, A, hΓ, d₁, d₂ => by
      rw [EnvRelK] at h
      obtain ⟨_, _, hv, hrest⟩ := h
      cases i with
      | zero => simp only [List.getElem?_cons_zero, Option.getD_some]
                simp only [List.getElem?_cons_zero, Option.some.injEq] at hΓ; subst hΓ; exact hv
      | succ k =>
          simp only [List.getElem?_cons_succ]
          simp only [List.getElem?_cons_succ] at hΓ
          exact EnvRelK.vrel_at hrest hΓ d₁ d₂


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

/-! ## B.3′ ◊4.5b sub-block (c) — `CrelK` head-step + value lemmas (the answer-typed migration)

The `CrelK` analogues of `Crel_head_step`/`crel_force`/`crel_unfold`, over the answer-typed `KrelS`.
`CrelK_head_step` is the generic `▷`-anti-reduction: a context-independent `CIStep` on both sides
reduces `CrelK n` to the reducts related at every `m < n` (the metered `▷`). Uses `KrelS_mono` (the
sub-block b downward-closure) where the old one used `Krel_mono`. -/

/-- ◊4.5b `▷`-guarded head-expansion of `CrelK` over the metered observation (the `KrelS` analogue of
`Crel_head_step`). A context-independent head-step on both sides reduces `CrelK n` to the reducts
related at every `m < n`. -/
theorem CrelK_head_step {n : Nat} {B : CTy Eff Mult} {e : Eff} {c₁ c₁' c₂ c₂' : Comp}
    (h₁ : CIStep c₁ c₁') (h₂ : CIStep c₂ c₂')
    (hlater : ∀ m, m < n → CrelK m B e c₁' c₂') : CrelK n B e c₁ c₂ := by
  rw [CrelK]; intro g D K₁ K₂ hK hconv
  have hstep₁ : Source.step (g, K₁, c₁) = some (g, K₁, c₁') :=
    h₁.1 g K₁
  have hne₁ : ∀ g' v, (g, K₁, c₁) ≠ (g', [], Comp.ret v) := by intro g' v; simp [h₁.2 v]
  cases n with
  | zero => exact absurd hconv (not_convergesC_le_zero _)
  | succ k =>
      rw [convergesC_le_step hstep₁ hne₁] at hconv
      have hCk : CrelK k B e c₁' c₂' := hlater k (Nat.lt_succ_self k)
      rw [CrelK] at hCk
      have hKk : KrelS k B D e g K₁ K₂ := KrelS_mono (Nat.le_succ k) hK
      have hstep₂ : Source.step (g, K₂, c₂) = some (g, K₂, c₂') :=
        h₂.1 g K₂
      have hne₂ : ∀ g' v, (g, K₂, c₂) ≠ (g', [], Comp.ret v) := by intro g' v; simp [h₂.2 v]
      exact converges_anti_step hstep₂ hne₂ (hCk g D K₁ K₂ hKk hconv)

/-- ◊4.5b `force` of `VrelK`-related thunks. The U-clause is `∀ j < n, CrelK j` — exactly the `m < n`
reducts `CrelK_head_step` consumes (cleaner than the old `∀ j ≤ n` + `le_of_lt`). -/
theorem crelK_force {n : Nat} {φ : Eff} {B : CTy Eff Mult} {w₁ w₂ : Val}
    (hv : VrelK n (VTy.U φ B) w₁ w₂) : CrelK n B φ (Comp.force w₁) (Comp.force w₂) := by
  rw [VrelK] at hv
  obtain ⟨c₁, c₂, rfl, rfl, hc⟩ := hv
  refine CrelK_head_step (c₁' := c₁) (c₂' := c₂) ?_ ?_ (fun m hm => hc m hm)
  · exact ⟨fun _ _ => rfl, by intro v; simp⟩
  · exact ⟨fun _ _ => rfl, by intro v; simp⟩

/-- ◊4.5b `unfold` of `VrelK`-related μ-values. `unfold (fold u) ↦ ret u` (CIStep); the ▷-head-step
needs `CrelK m (ret u₁) (ret u₂)` at each `m < n`, from `crelK_ret` on the μ-payload. -/
theorem crelK_unfold {n : Nat} {A : VTy Eff Mult} {e : Eff} {w₁ w₂ : Val}
    (hcw₁ : Val.Closed w₁) (hcw₂ : Val.Closed w₂) (hv : VrelK n (VTy.mu A) w₁ w₂) :
    CrelK n (CTy.F 1 (VTy.unrollMu A)) e (Comp.unfold w₁) (Comp.unfold w₂) := by
  rw [VrelK] at hv
  obtain ⟨u₁, u₂, rfl, rfl, hu⟩ := hv
  refine CrelK_head_step (c₁' := Comp.ret u₁) (c₂' := Comp.ret u₂) ?_ ?_ ?_
  · exact ⟨fun _ _ => rfl, by intro v; simp⟩
  · exact ⟨fun _ _ => rfl, by intro v; simp⟩
  · -- ROUTE-1: `crelK_ret` gives the unfolded `CrelK` body at a specific `g`/observation context, so
    -- unfold `CrelK m` and discharge per-config. Hole type `F 1 (unrollMu A)` (q = 1).
    intro m hm
    rw [CrelK]; intro g D K₁ K₂ hK
    exact crelK_ret g D K₁ K₂ hK hcw₁.fold_inv hcw₂.fold_inv (hu m hm)


/-! ### B.3′b `CrelK` frame extensions + `compat` cores (`letC`/`app`)

The answer-typed frame lemmas. `krelS_letF_intro` builds a `KrelS (F q A)` from a `▷`-guarded
continuation relation + a tail `KrelS B` — directly packing the def's letF clause (the tail weakens
from the ambient `ε` to the continuation row `φ` via `KrelS_eff_anti`, `φ ≤ ε`). `compatK_letC`/`_app`
refocus the source redex (`letC`/`app` PUSH) and run the bound computation through the extended stack. -/

/-- ◊4.5b build a letF-extended `KrelS` from a continuation relation (`▷`-guarded, `∀ m < n`) + the
ambient tail. The continuation row `φ ≤ ε`; the tail weakens `ε → φ` via `KrelS_eff_anti`. -/
theorem krelS_letF_intro {n : Nat} {q : Mult} {A : VTy Eff Mult} {B D : CTy Eff Mult} {ε φ : Eff}
    {g : Nat} {N₁ N₂ : Comp} {K₁ K₂ : Stack} (hφε : φ ≤ ε)
    (hN : ∀ m, m < n → ∀ v₁ v₂, Val.Closed v₁ → Val.Closed v₂ →
      VrelK m A v₁ v₂ →
      CrelK m B φ (Comp.subst v₁ N₁) (Comp.subst v₂ N₂))
    (hK : KrelS n B D ε g K₁ K₂) :
    KrelS n (CTy.F q A) D ε g (Frame.letF N₁ :: K₁) (Frame.letF N₂ :: K₂) := by
  rw [krelS_letF]
  exact ⟨q, A, B, φ, rfl, hN, KrelS_eff_anti hφε hK⟩

/-- ◊4.5b the `letC` compat core at `CrelK` (the answer-typed `compat_letC`). REFOCUS
`(K, letC M N) ↦ (letF N::K, M)` (one PUSH step), then run `M` (related at `F q1 A`, row φ₁) through the
letF-extended stack, shown `KrelS`-related by `krelS_letF_intro`. The continuation `hN` is `▷`-guarded
(`∀ m < n`) at row φ₂; the block is at `φ₁ ⊔ φ₂`. -/
theorem compatK_letC {n : Nat} {q1 : Mult} {A : VTy Eff Mult} {B : CTy Eff Mult} {φ₁ φ₂ : Eff}
    {M₁ M₂ N₁' N₂' : Comp}
    (hM : CrelK n (CTy.F q1 A) φ₁ M₁ M₂)
    (hN : ∀ m, m < n → ∀ v₁ v₂, Val.Closed v₁ → Val.Closed v₂ →
      VrelK m A v₁ v₂ →
      CrelK m B φ₂ (Comp.subst v₁ N₁') (Comp.subst v₂ N₂')) :
    CrelK n B (φ₁ ⊔ φ₂) (Comp.letC M₁ N₁') (Comp.letC M₂ N₂') := by
  rw [CrelK]
  intro g D K₁ K₂ hK
  refine coApproxC_le_reduce
    (cfg₁' := (g, Frame.letF N₁' :: K₁, M₁))
    (cfg₂' := (g, Frame.letF N₂' :: K₂, M₂))
    rfl (by intro g' u; simp) rfl (by intro g' u; simp) ?_
  -- the letF-extended stack is `KrelS`-related at `(F q1 A, φ₁)`: tail at the block row φ₁⊔φ₂ weakens
  -- to the continuation row φ₂ (≤ φ₁⊔φ₂); `hM` (related at F q1 A, row φ₁) discharges the reduct.
  have hKletF : KrelS n (CTy.F q1 A) D (φ₁ ⊔ φ₂) g (Frame.letF N₁' :: K₁) (Frame.letF N₂' :: K₂) :=
    krelS_letF_intro le_sup_right hN hK
  rw [CrelK] at hM
  -- `hM` is at row φ₁; the letF-extended stack is at φ₁⊔φ₂. Weaken the stack φ₁⊔φ₂ → φ₁ (antitone).
  exact hM g D (Frame.letF N₁' :: K₁) (Frame.letF N₂' :: K₂) (KrelS_eff_anti le_sup_left hKletF)

/-- ◊4.5b build an appF-extended `KrelS` from a `VrelK`-related closed argument + the codomain tail.
The appF frame doesn't bind a continuation row, so the tail stays at the ambient `ε` (no weakening). -/
theorem krelS_appF_intro {n : Nat} {q : Mult} {A : VTy Eff Mult} {B D : CTy Eff Mult} {ε : Eff}
    {g : Nat} {v₁ v₂ : Val} {K₁ K₂ : Stack} (hcv₁ : Val.Closed v₁) (hcv₂ : Val.Closed v₂)
    (hv : VrelK n A v₁ v₂) (hK : KrelS n B D ε g K₁ K₂) :
    KrelS n (CTy.arr q A B) D ε g (Frame.appF v₁ :: K₁) (Frame.appF v₂ :: K₂) := by
  rw [krelS_appF]
  exact ⟨q, A, B, rfl, hcv₁, hcv₂, hv, hK⟩

/-- ◊4.5b the `app` compat core at `CrelK` (the answer-typed `compat_app`). REFOCUS
`(K, app M v) ↦ (appF v::K, M)`, then run `M` (related at `arr q A B`) through the appF-extended
stack, shown `KrelS`-related by `krelS_appF_intro`. -/
theorem compatK_app {n : Nat} {q : Mult} {A : VTy Eff Mult} {B : CTy Eff Mult} {φ : Eff}
    {M₁ M₂ : Comp} {v₁ v₂ : Val}
    (hM : CrelK n (CTy.arr q A B) φ M₁ M₂)
    (hcv₁ : Val.Closed v₁) (hcv₂ : Val.Closed v₂)
    (hv : VrelK n A v₁ v₂) :
    CrelK n B φ (Comp.app M₁ v₁) (Comp.app M₂ v₂) := by
  rw [CrelK]
  intro g D K₁ K₂ hK
  refine coApproxC_le_reduce
    (cfg₁' := (g, Frame.appF v₁ :: K₁, M₁))
    (cfg₂' := (g, Frame.appF v₂ :: K₂, M₂))
    rfl (by intro g' u; simp) rfl (by intro g' u; simp) ?_
  rw [CrelK] at hM
  exact hM g D (Frame.appF v₁ :: K₁) (Frame.appF v₂ :: K₂) (krelS_appF_intro hcv₁ hcv₂ hv hK)

/-- ◊4.5b the `lam` compat core at `CrelK` (the answer-typed `compat_lam`). A `lam` only β-reduces under
an `appF` frame; other stacks are STUCK on a `lam` (observation vacuous). Stack induction: appF-headed
β-reduces `(appF w::K', lam M') ↦ (K', M'.subst w)`, the body IH discharges; nil/letF are stuck on a
`lam`; handleF passes the lam through (`handleF h::K, lam M` is STUCK too — handleF only reduces a
`ret`). So only the appF case is non-vacuous. -/
theorem compatK_lam {n : Nat} {q : Mult} {A : VTy Eff Mult} {B : CTy Eff Mult} {φ : Eff}
    {M₁' M₂' : Comp}
    (hbody : ∀ w₁ w₂, Val.Closed w₁ → Val.Closed w₂ →
      VrelK n A w₁ w₂ → CrelK n B φ (Comp.subst w₁ M₁') (Comp.subst w₂ M₂')) :
    CrelK n (CTy.arr q A B) φ (Comp.lam M₁') (Comp.lam M₂') := by
  rw [CrelK]
  intro g D K₁ K₂ hK
  cases K₁ with
  | nil =>
      -- nil arrow: `([], lam M)` is STUCK (lam reduces only under appF). Vacuous.
      intro hconv; exact absurd hconv (not_convergesC_le_of_stuck rfl (by intro g' u; simp))
  | cons fr K₁' =>
      cases fr with
      | appF w₁ =>
          cases K₂ with
          | cons fr₂ K₂' =>
              cases fr₂ with
              | appF w₂ =>
                  rw [krelS_appF] at hK
                  obtain ⟨q', A', B', hC, hcw₁, hcw₂, hw, htail⟩ := hK
                  rw [CTy.arr.injEq] at hC; obtain ⟨rfl, rfl, rfl⟩ := hC
                  -- β `(appF w::K', lam M') ↦ (K', M'.subst w)`; body IH at the SAME index, non-dropping.
                  refine coApproxC_le_reduce
                    (cfg₁' := (g, K₁', Comp.subst w₁ M₁'))
                    (cfg₂' := (g, K₂', Comp.subst w₂ M₂'))
                    rfl (by intro g' u; simp) rfl (by intro g' u; simp) ?_
                  have hb := hbody w₁ w₂ hcw₁ hcw₂ hw
                  rw [CrelK] at hb
                  exact hb g D K₁' K₂' htail
              | _ => simp only [KrelS] at hK
          | nil => simp only [KrelS] at hK
      | letF N₁ =>
          -- letF arrow: the clause requires `C = F q A`, but `C = arr q A B` (arr ≠ F) ⇒ False.
          cases K₂ with
          | cons fr₂ K₂' =>
              cases fr₂ with
              | letF N₂ => rw [krelS_letF] at hK; obtain ⟨_, _, _, _, hC, _⟩ := hK; exact absurd hC (by simp)
              | _ => simp only [KrelS] at hK
          | nil => simp only [KrelS] at hK
      | handleF h₁ =>
          -- handleF on a `lam`: `(handleF h::K, lam M)` is STUCK (handleF reduces only a `ret`). Vacuous.
          intro hconv; exact absurd hconv (not_convergesC_le_of_stuck rfl (by intro g' u; simp))

/-- ◊4.5b the `case` (sum elim) compat core at `CrelK`. `case (inl u) ↦ N₁[u]` / `case (inr u) ↦ N₂[u]`
are CISteps; the ▷-head-step needs the chosen branch related at every `m < n`, from the matching branch
IH on the `VrelK m`-related payload (the sum scrutinee gives the tag + payload). -/
theorem compatK_case {n : Nat} {A B : VTy Eff Mult} {C : CTy Eff Mult} {φ : Eff}
    {w₁ w₂ : Val} {N₁₁ N₂₁ N₁₂ N₂₂ : Comp}
    (hw : VrelK n (VTy.sum A B) w₁ w₂) (hcw₁ : Val.Closed w₁) (hcw₂ : Val.Closed w₂)
    (hN₁ : ∀ m, m < n → ∀ v₁ v₂, Val.Closed v₁ → Val.Closed v₂ →
      VrelK m A v₁ v₂ →
      CrelK m C φ (Comp.subst v₁ N₁₁) (Comp.subst v₂ N₁₂))
    (hN₂ : ∀ m, m < n → ∀ v₁ v₂, Val.Closed v₁ → Val.Closed v₂ →
      VrelK m B v₁ v₂ →
      CrelK m C φ (Comp.subst v₁ N₂₁) (Comp.subst v₂ N₂₂)) :
    CrelK n C φ (Comp.case w₁ N₁₁ N₂₁) (Comp.case w₂ N₁₂ N₂₂) := by
  rw [VrelK] at hw
  rcases hw with ⟨u₁, u₂, rfl, rfl, hu⟩ | ⟨u₁, u₂, rfl, rfl, hu⟩
  · refine CrelK_head_step (c₁' := Comp.subst u₁ N₁₁) (c₂' := Comp.subst u₂ N₁₂) ?_ ?_
      (fun m hm => hN₁ m hm u₁ u₂ hcw₁.inl_inv hcw₂.inl_inv (VrelK_mono (le_of_lt hm) hu))
    · exact ⟨fun _ _ => rfl, by intro v; simp⟩
    · exact ⟨fun _ _ => rfl, by intro v; simp⟩
  · refine CrelK_head_step (c₁' := Comp.subst u₁ N₂₁) (c₂' := Comp.subst u₂ N₂₂) ?_ ?_
      (fun m hm => hN₂ m hm u₁ u₂ hcw₁.inr_inv hcw₂.inr_inv (VrelK_mono (le_of_lt hm) hu))
    · exact ⟨fun _ _ => rfl, by intro v; simp⟩
    · exact ⟨fun _ _ => rfl, by intro v; simp⟩

/-- ◊4.5b the `split` (product elim) compat core at `CrelK`. `split (pair a b) N ↦ N[a][shift b]` is a
CIStep; the ▷-head-step needs the two-binder body related at every `m < n`. -/
theorem compatK_split {n : Nat} {A B : VTy Eff Mult} {C : CTy Eff Mult} {φ : Eff}
    {w₁ w₂ : Val} {N₁' N₂' : Comp}
    (hw : VrelK n (VTy.prod A B) w₁ w₂) (hcw₁ : Val.Closed w₁) (hcw₂ : Val.Closed w₂)
    (hN : ∀ m, m < n → ∀ a₁ a₂ b₁ b₂, Val.Closed a₁ → Val.Closed a₂ → Val.Closed b₁ → Val.Closed b₂ →
      VrelK m A a₁ a₂ → VrelK m B b₁ b₂ →
      CrelK m C φ (Comp.subst a₁ (Comp.subst (Val.shift b₁) N₁'))
                  (Comp.subst a₂ (Comp.subst (Val.shift b₂) N₂'))) :
    CrelK n C φ (Comp.split w₁ N₁') (Comp.split w₂ N₂') := by
  rw [VrelK] at hw
  obtain ⟨a₁, a₂, b₁, b₂, rfl, rfl, ha, hb⟩ := hw
  obtain ⟨hca₁, hcb₁⟩ := hcw₁.pair_inv
  obtain ⟨hca₂, hcb₂⟩ := hcw₂.pair_inv
  refine CrelK_head_step
    (c₁' := Comp.subst a₁ (Comp.subst (Val.shift b₁) N₁'))
    (c₂' := Comp.subst a₂ (Comp.subst (Val.shift b₂) N₂')) ?_ ?_
    (fun m hm => hN m hm a₁ a₂ b₁ b₂ hca₁ hca₂ hcb₁ hcb₂
      (VrelK_mono (le_of_lt hm) ha) (VrelK_mono (le_of_lt hm) hb))
  · exact ⟨fun _ _ => rfl, by intro v; simp⟩
  · exact ⟨fun _ _ => rfl, by intro v; simp⟩


/-! ### B.3′c ◊4.5b sub-block (f) — handler-frame `KrelS` intro + `compatK_handle*` cores

The answer-typed analogues of the old `krel_handleF*`/`compat_handle*`. The new `KrelS` has NO stuck-half
(`Srel` is gone — the op-stuck behaviour lives in `CrelK`'s biorthogonality, not the stack relation), so
the handler-frame intro is TRIVIAL: `krelS_handleF` says `KrelS …ε (handleF h::K) ↔ KrelS …ε K`, and the
ROW-DISCHARGE (body row `e` ⊋ discharged row `φ`) is `KrelS_eff_cast` (ε is inert in `KrelS`). This is the
SINGLE-ROW close of the original ◊4.5b wall — no two-row Biernacki `C⟦τ₁/ε₁{τ₂/ε₂⟧` needed (the row only
gated the dropped `Srel`). shape: biernacki-popl18 §5.4 set-row ρ-free collapse. -/

/-- ◊4.5b-append build a handleF-extended `KrelS` from a SELF-`HandlerRel` witness + the discharged-row
tail + the Kᵢ-threading RESUME CONJUNCT. The body row `e` is arbitrary w.r.t. `φ` (`KrelS_eff_cast`).
The conjunct (dispatched-config co-convergence at `m < n`, threading the captured continuation `Kᵢ~Kᵢ'`)
is SUPPLIED by the caller — throws via `crelK_ret` on the tail (zero-shot); state/txn via the resume
relation through `Kᵢ`. -/
theorem krelS_handleF_intro {n : Nat} {nh : Nat} {C D : CTy Eff Mult} {e φ : Eff} {g : Nat} {h₁ h₂ : Handler}
    {K₁ K₂ : Stack} (hHR : HandlerRel Eff Mult n h₁ h₂) (hK : KrelS n C D φ g K₁ K₂)
    (hres : ∀ m, m < n → ∀ (op : OpId) (w₁ w₂ : Val) (Cᵢ : CTy Eff Mult) (εᵢ : Eff)
              (Kᵢ Kᵢ' : Stack) (cfg₁ cfg₂ : EvalCtx × Comp),
        Bang.handlesOp h₁ h₁.label op = true →
        Val.Closed w₁ → Val.Closed w₂ →
        (∀ Aop, EffSig.opArg (Eff := Eff) (Mult := Mult) h₁.label op = some Aop → VrelK m Aop w₁ w₂) →
        KrelS m Cᵢ C εᵢ g Kᵢ Kᵢ' →
        (∀ Aᵣ, EffSig.opRes (Eff := Eff) (Mult := Mult) h₁.label op = some Aᵣ →
          ∃ qᵣ, Cᵢ = CTy.F qᵣ Aᵣ) →
        Bang.dispatchOn nh op w₁ (Kᵢ, h₁, K₁) = some cfg₁ →
        Bang.dispatchOn nh op w₂ (Kᵢ', h₂, K₂) = some cfg₂ →
        (∃ (qᵣ : Mult) (Aᵣ : VTy Eff Mult) (r₁ r₂ : Val) (Sᵢ Sᵢ' : Stack) (eₛ : Eff),
            cfg₁ = (Sᵢ, Comp.ret r₁) ∧ cfg₂ = (Sᵢ', Comp.ret r₂) ∧
            Val.Closed r₁ ∧ Val.Closed r₂ ∧ VrelK m Aᵣ r₁ r₂ ∧
            KrelS m (CTy.F qᵣ Aᵣ) D eₛ g Sᵢ Sᵢ')) :
    KrelS n C D e g (Frame.handleF nh h₁ :: K₁) (Frame.handleF nh h₂ :: K₂) := by
  rw [krelS_handleF]; exact ⟨rfl, hHR, KrelS_eff_cast hK, hres⟩

/-- ◊4.5b-append DISPATCH-APPEND structural fact. `dispatchOn` over an outer stack `Kₒ ++ T` produces
the SAME config as over `Kₒ`, with `T` appended to the result's outer stack. Uniform across all handler
kinds: throws returns `(Kₒ, ret v)` ⇒ `(Kₒ ++ T, ret v)`; state/txn reinstall over `Kᵢ ++ reinstall :: Kₒ`
⇒ `Kᵢ ++ reinstall :: (Kₒ ++ T) = (Kᵢ ++ reinstall :: Kₒ) ++ T`. Proven by `cases` on the handler then
`cases` on the op-string decisions. (Note: this is the structural half; it does NOT make the OPAQUE
`CoApproxC_le` resume conjunct compose under append — see the wall comment at `krelS_append`'s handleF
case.) -/
theorem dispatchOn_append_outer (n : Nat) (op : OpId) (v : Val) (Kᵢ : Stack) (hh : Handler) (Kₒ T : Stack)
    {cfg : EvalCtx × Comp} (hd : Bang.dispatchOn n op v (Kᵢ, hh, Kₒ) = some cfg) :
    Bang.dispatchOn n op v (Kᵢ, hh, Kₒ ++ T) = some (cfg.1 ++ T, cfg.2) := by
  cases hh with
  | throws _ =>
      simp only [dispatchOn] at hd ⊢
      obtain rfl := (Option.some.injEq _ _).mp hd.symm; rfl
  | state ℓ' s =>
      simp only [dispatchOn] at hd ⊢
      by_cases hop : op == "get" <;> simp only [hop, if_true, if_false, Bool.false_eq_true] at hd ⊢ <;>
        (obtain rfl := (Option.some.injEq _ _).mp hd.symm; simp [List.append_assoc])
  | transaction ℓ' Θ =>
      simp only [dispatchOn] at hd ⊢
      by_cases h1 : op == "newTVar"
      · simp only [h1, if_true] at hd ⊢
        obtain rfl := (Option.some.injEq _ _).mp hd.symm; simp [List.append_assoc]
      · by_cases h2 : op == "readTVar"
        · simp only [h1, h2, if_true, if_false, Bool.false_eq_true] at hd ⊢
          obtain rfl := (Option.some.injEq _ _).mp hd.symm; simp [List.append_assoc]
        · simp only [h1, h2, if_false, Bool.false_eq_true] at hd ⊢
          cases v <;>
            (simp only [] at hd ⊢; obtain rfl := (Option.some.injEq _ _).mp hd.symm;
             simp [List.append_assoc])

/-- ◊4.5b-strengthen the krel-carrying resume CONCLUSION → `CoApproxC_le`. The strengthened handleF
resume conjunct concludes a DECOMPOSITION `cfgⱼ = (Sᵢ, ret rⱼ)` with `r₁~r₂` (VrelK) + `Sᵢ~Sᵢ'` (KrelS
at a returner hole). `crelK_ret` on the returned values, instantiated at the related stacks, recovers the
plain `CoApproxC_le m cfg₁ cfg₂`. This is the T=[] consumer; the nested case appends a tail to `Sᵢ` first
(via `krelS_append`) then runs the SAME `crelK_ret`. -/
-- ADR-0058 ROUTE-1: the `crelK_ret` consumer, now at the THREADED counter `g`. NO density premises —
-- both resume-decomposition configs observe at the SAME `g` (dispatch/reinstall preserves the counter),
-- so `crelK_ret` (route-1 form) bridges the decomposition directly, no `Canonical`/`CapsBelow`/`run_bump`.
theorem coApproxC_le_of_resumeDecomp {m : Nat} {qᵣ : Mult} {Aᵣ : VTy Eff Mult} {D : CTy Eff Mult}
    {g : Nat} {r₁ r₂ : Val} {Sᵢ Sᵢ' : Stack} {eₛ : Eff}
    (hcr₁ : Val.Closed r₁) (hcr₂ : Val.Closed r₂) (hr : VrelK m Aᵣ r₁ r₂)
    (hS : KrelS m (CTy.F qᵣ Aᵣ) D eₛ g Sᵢ Sᵢ') :
    CoApproxC_le m (g, Sᵢ, Comp.ret r₁) (g, Sᵢ', Comp.ret r₂) :=
  crelK_ret g D Sᵢ Sᵢ' hS hcr₁ hcr₂ hr

/-- ◊4.5b-strengthen `HandlerRel` DOWNWARD-CLOSURE — the relational handler condition is monotone in its
`VrelK`-stored state (state: one cell; transaction: pointwise heap; throws: index-independent label). The
inlined form lives in `KrelS_mono`'s handleF case; extracted here for the `krelS_append` index-drop. -/
theorem HandlerRel_mono {n m : Nat} {h₁ h₂ : Handler} (hmn : m ≤ n)
    (hh : HandlerRel Eff Mult n h₁ h₂) : HandlerRel Eff Mult m h₁ h₂ := by
  cases h₁ <;> cases h₂ <;> simp only [HandlerRel] at hh ⊢
  · exact ⟨hh.1, hh.2.imp fun _ hv => VrelK_mono hmn hv⟩
  · exact hh
  · exact ⟨hh.1, hh.2.1, fun i hi => VrelK_mono hmn (hh.2.2 i hi)⟩

/-- ◊4.5b-append `krelS_append` — the config-level Biernacki Lemma-2 analogue. Compose a related captured
continuation `Kᵢ ~ Kᵢ'` (answer type `Dᵢ`) with a related handleF-extended tail (`handleF h :: K`, hole
`Dᵢ`) into the appended stack `Kᵢ ++ handleF h :: K`. The inner `Kᵢ`'s answer type MUST equal the
reinstalled-handler frame's hole type `Dᵢ` (the resume value flows out of `Kᵢ` into the handler frame).
Proven by induction on `Kᵢ` (structural, like `crelK_ret`/`KrelS_mono`): nil = `krelS_handleF_intro`;
letF/appF peel + reconstruct over the appended tail. The handleF-in-`Kᵢ` sub-case (a handler NESTED in
the captured continuation) needs the resume-conjunct RELOCATED to the appended tail — same as the
decomp-miss-wrap; one documented sorry. shape: biernacki-popl18 §5.4 Lemma 2 (config-level append). -/
theorem krelS_append {m : Nat} {nh : Nat} {Cᵢ Dᵢ D' : CTy Eff Mult} {εᵢ e' : Eff} {g : Nat} {h₁ h₂ : Handler}
    {Kᵢ Kᵢ' K₁ K₂ : Stack}
    (hin : KrelS m Cᵢ Dᵢ εᵢ g Kᵢ Kᵢ')
    (hHR : HandlerRel Eff Mult m h₁ h₂)
    (htail : KrelS m Dᵢ D' e' g K₁ K₂)
    (hres : ∀ k, k < m → ∀ (op : OpId) (w₁ w₂ : Val) (Cⱼ : CTy Eff Mult) (εⱼ : Eff)
              (Kⱼ Kⱼ' : Stack) (cfg₁ cfg₂ : EvalCtx × Comp),
        Bang.handlesOp h₁ h₁.label op = true →
        Val.Closed w₁ → Val.Closed w₂ →
        (∀ Aop, EffSig.opArg (Eff := Eff) (Mult := Mult) h₁.label op = some Aop → VrelK k Aop w₁ w₂) →
        KrelS k Cⱼ Dᵢ εⱼ g Kⱼ Kⱼ' →
        (∀ Aᵣ, EffSig.opRes (Eff := Eff) (Mult := Mult) h₁.label op = some Aᵣ →
          ∃ qᵣ, Cⱼ = CTy.F qᵣ Aᵣ) →
        Bang.dispatchOn nh op w₁ (Kⱼ, h₁, K₁) = some cfg₁ →
        Bang.dispatchOn nh op w₂ (Kⱼ', h₂, K₂) = some cfg₂ →
        (∃ (qᵣ : Mult) (Aᵣ : VTy Eff Mult) (r₁ r₂ : Val) (Sᵢ Sᵢ' : Stack) (eₛ : Eff),
            cfg₁ = (Sᵢ, Comp.ret r₁) ∧ cfg₂ = (Sᵢ', Comp.ret r₂) ∧
            Val.Closed r₁ ∧ Val.Closed r₂ ∧ VrelK k Aᵣ r₁ r₂ ∧
            KrelS k (CTy.F qᵣ Aᵣ) D' eₛ g Sᵢ Sᵢ')) :
    KrelS m Cᵢ D' εᵢ g (Kᵢ ++ Frame.handleF nh h₁ :: K₁) (Kᵢ' ++ Frame.handleF nh h₂ :: K₂) := by
  -- ◊4.5b-strengthen: WELL-FOUNDED recursion on `(m, Kᵢ.length)`. letF/appF recurse on the shorter
  -- `Kᵢ` (second component drops); the NESTED handleF case recurses at the DROPPED index `k < m` (first
  -- component drops) on the dispatched stack `Sᵢ` — which may be LONGER, but the step-index pays for it.
  match Kᵢ, Kᵢ' with
  | [], [] =>
      -- Cᵢ = Dᵢ (nil); the append is `handleF h :: K` — `krelS_handleF_intro`.
      rw [krelS_nil] at hin
      obtain ⟨rfl, _⟩ := hin
      simpa using krelS_handleF_intro (e := εᵢ) hHR htail hres
  | (Frame.letF N₁ :: Kᵢrest), (Frame.letF N₂ :: Kᵢ'rest) =>
      rw [krelS_letF] at hin
      obtain ⟨q, A, B, φ, hC, hbody, htin⟩ := hin
      rw [List.cons_append, List.cons_append, krelS_letF]
      exact ⟨q, A, B, φ, hC, hbody, krelS_append htin hHR htail hres⟩
  | (Frame.appF u₁ :: Kᵢrest), (Frame.appF u₂ :: Kᵢ'rest) =>
      rw [krelS_appF] at hin
      obtain ⟨q, A, B, hC, hcu₁, hcu₂, hu, htin⟩ := hin
      rw [List.cons_append, List.cons_append, krelS_appF]
      exact ⟨q, A, B, hC, hcu₁, hcu₂, hu, krelS_append htin hHR htail hres⟩
  | (Frame.handleF mh₁ hh₁ :: Kᵢrest), (Frame.handleF mh₂ hh₂ :: Kᵢ'rest) =>
      -- ◊4.5b-strengthen CLOSE: a handler NESTED in the captured continuation. The structural shape
      -- closes HandlerRel + the recursive-append tail; the resume conjunct over the APPENDED tail is now
      -- reconstructible. From the inner conjunct `_hres_inner` (krel-carrying): the inner dispatch over
      -- `Kᵢrest` yields a RETURN config `(Sᵢ, ret rⱼ)` with `Sᵢ~Sᵢ'` (KrelS at hole `F qᵣ Aᵣ`, answer `Dᵢ`)
      -- and `r₁~r₂`. `dispatchOn_append_outer` lifts this dispatch over `Kᵢrest ++ handleF nh h₁::K₁` to
      -- `(Sᵢ ++ handleF nh h₁::K₁, ret rⱼ)`. Then `krelS_append` (at the DROPPED index `k`, on the inner `Sᵢ`)
      -- composes `Sᵢ` with `handleF nh h₁::K₁` ⇒ `KrelS k (F qᵣ Aᵣ) D' (Sᵢ++handleF nh h₁::K₁)(Sᵢ'++…)`,
      -- exactly the appended decomposition the goal demands. ADR-0055: the nested frame carries its OWN
      -- identity `mh₁` (= `mh₂` by `krelS_handleF`'s id equality), routed through `dispatchOn mh₁`.
      -- shape: biernacki-popl18 §5.4 Lemma 2 (config append).
      rw [krelS_handleF] at hin
      obtain ⟨hmid, hHRtop, htin, hres_inner⟩ := hin
      subst hmid
      rw [List.cons_append, List.cons_append, krelS_handleF]
      refine ⟨rfl, hHRtop, krelS_append htin hHR htail hres, ?_⟩
      intro k hk op w₁ w₂ Cⱼ εⱼ Kⱼ Kⱼ' cfg₁ cfg₂ hcatch hcw₁ hcw₂ hVrel hKj hCⱼ hd₁ hd₂
      -- recover the INNER dispatch (over `Kᵢrest`) by computing it, then lift via `dispatchOn_append_outer`.
      obtain ⟨cfgᵢ₁, hdi₁⟩ : ∃ c, Bang.dispatchOn mh₁ op w₁ (Kⱼ, hh₁, Kᵢrest) = some c := by
        cases hh₁ with
        | throws _ => exact ⟨_, rfl⟩
        | state _ _ => rw [dispatchOn]; split <;> exact ⟨_, rfl⟩
        | transaction _ _ => unfold dispatchOn; split_ifs <;> first | exact ⟨_, rfl⟩ | (cases w₁ <;> exact ⟨_, rfl⟩)
      obtain ⟨cfgᵢ₂, hdi₂⟩ : ∃ c, Bang.dispatchOn mh₁ op w₂ (Kⱼ', hh₂, Kᵢ'rest) = some c := by
        cases hh₂ with
        | throws _ => exact ⟨_, rfl⟩
        | state _ _ => rw [dispatchOn]; split <;> exact ⟨_, rfl⟩
        | transaction _ _ => unfold dispatchOn; split_ifs <;> first | exact ⟨_, rfl⟩ | (cases w₂ <;> exact ⟨_, rfl⟩)
      have hlift₁ := dispatchOn_append_outer mh₁ op w₁ Kⱼ hh₁ Kᵢrest (Frame.handleF nh h₁ :: K₁) hdi₁
      have hlift₂ := dispatchOn_append_outer mh₁ op w₂ Kⱼ' hh₂ Kᵢ'rest (Frame.handleF nh h₂ :: K₂) hdi₂
      rw [hd₁] at hlift₁; rw [hd₂] at hlift₂
      obtain rfl := (Option.some.injEq _ _).mp hlift₁.symm
      obtain rfl := (Option.some.injEq _ _).mp hlift₂.symm
      -- apply the inner conjunct to the inner dispatch → the decomposition `cfgᵢⱼ = (Sᵢ, ret rⱼ)`.
      obtain ⟨qᵣ, Aᵣ, r₁, r₂, Sᵢ, Sᵢ', eₛ, hcf₁, hcf₂, hcr₁, hcr₂, hr, hSrel⟩ :=
        hres_inner k hk op w₁ w₂ Cⱼ εⱼ Kⱼ Kⱼ' cfgᵢ₁ cfgᵢ₂ hcatch hcw₁ hcw₂ hVrel hKj hCⱼ hdi₁ hdi₂
      subst hcf₁; subst hcf₂
      -- the appended config is `(Sᵢ ++ handleF nh h₁::K₁, ret rⱼ)`; rebuild the decomposition over the
      -- append by `krelS_append` at the dropped index `k` (the step-index pays for the longer `Sᵢ`).
      refine ⟨qᵣ, Aᵣ, r₁, r₂, Sᵢ ++ Frame.handleF nh h₁ :: K₁, Sᵢ' ++ Frame.handleF nh h₂ :: K₂, eₛ,
        by simp, by simp, hcr₁, hcr₂, hr, ?_⟩
      exact krelS_append (εᵢ := eₛ) hSrel (HandlerRel_mono (le_of_lt hk) hHR)
        (KrelS_mono (le_of_lt hk) htail) (fun k' hk' => hres k' (lt_trans hk' hk))
  | [], (_ :: _) => simp only [KrelS] at hin
  | (fr :: _), [] => exact absurd hin (by simp only [KrelS]; cases fr <;> exact not_false)
  | (Frame.letF _ :: _), (Frame.appF _ :: _) => simp only [KrelS] at hin
  | (Frame.letF _ :: _), (Frame.handleF _ _ :: _) => simp only [KrelS] at hin
  | (Frame.appF _ :: _), (Frame.letF _ :: _) => simp only [KrelS] at hin
  | (Frame.appF _ :: _), (Frame.handleF _ _ :: _) => simp only [KrelS] at hin
  | (Frame.handleF _ _ :: _), (Frame.letF _ :: _) => simp only [KrelS] at hin
  | (Frame.handleF _ _ :: _), (Frame.appF _ :: _) => simp only [KrelS] at hin
termination_by (m, Kᵢ.length)
decreasing_by
  -- letF/appF/handleF structural recursions drop `Kᵢ.length` (m fixed); the nested handleF resume
  -- recursion drops the step-index `m` (to `k`).
  all_goals first
    | exact Prod.Lex.right _ (by simp)
    | exact Prod.Lex.left _ _ hk

/-- ◊4.5b-append the STATE-reinstall lemma — the resumptive heart. A `state ℓ s` handler frame over a
related tail self-relates at every index, with the resume conjunct supplied by GUARDED RECURSION on the
index: the get/put dispatch reinstalls `state ℓ s` and resumes `ret r` (r = s for get, unit for put)
through the captured continuation `Kᵢ`, which `krelS_append`s onto the reinstalled frame + tail at the
DROPPED index `m' < m` (the IH). The stored state `s` self-relates at `S` (hsv, from the caller's typing
via `vrelK_fund`). shape: biernacki-popl18 §5.4 resumptive clause + the ▷-guarded reinstall. -/
theorem krelS_state_reinstall {q : Mult} {A S : VTy Eff Mult} {D : CTy Eff Mult} {φ : Eff} {ℓ : Label}
    {g : Nat}
    (hgr : EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "get" = some S)
    (hp : EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "put" = some S)
    (hpr : EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "put" = some VTy.unit)
    (hrestrict : ∀ op s, Bang.handlesOp (Handler.state ℓ s) ℓ op = true → op = "get" ∨ op = "put") :
    ∀ (nh : Nat) m (s₁ s₂ : Val), Val.Closed s₁ → Val.Closed s₂ →
      VrelK m S s₁ s₂ →
      ∀ (K₁ K₂ : Stack), KrelS m (CTy.F q A) D φ g K₁ K₂ →
      KrelS m (CTy.F q A) D φ g (Frame.handleF nh (Handler.state ℓ s₁) :: K₁)
                              (Frame.handleF nh (Handler.state ℓ s₂) :: K₂) := by
  -- GUARDED RECURSION on the index: the reinstalled handler (over the SAME tail, at the put-updated state
  -- pair) relates at the DROPPED index m' < m (the IH), supplying `krelS_append`'s resume conjunct.
  -- ADR-0055: the frame carries its generative id `nh`; the resume dispatch reinstalls `handleF nh` (same id).
  intro nh m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro s₁ s₂ hcs₁ hcs₂ hsv K₁ K₂ hK
    refine krelS_handleF_intro
      (show HandlerRel Eff Mult m (Handler.state ℓ s₁) (Handler.state ℓ s₂) from ⟨rfl, S, hsv⟩) hK ?_
    intro m' hm' op w₁ w₂ Cᵢ εᵢ Kᵢ Kᵢ' cfg₁ cfg₂ hcatch hcw₁ hcw₂ hVrel hKi hCᵢ hd₁ hd₂
    rcases hrestrict op s₁ hcatch with rfl | rfl
    · -- GET: cfg = (Kᵢ ++ handleF nh (state ℓ sⱼ)::Kⱼ, ret sⱼ); resume value = the stored state (related).
      obtain ⟨qᵣ, rfl⟩ := hCᵢ S (by rw [Handler.label]; exact hgr)
      simp only [Handler.label, dispatchOn] at hd₁ hd₂
      obtain rfl := (Option.some.injEq _ _).mp hd₁.symm
      obtain rfl := (Option.some.injEq _ _).mp hd₂.symm
      -- the reinstalled `state ℓ s₁/s₂` over the tail relates at m' (IH at the SAME state pair, downward).
      have hreinst := ih m' hm' s₁ s₂ hcs₁ hcs₂ (VrelK_mono (le_of_lt hm') hsv) K₁ K₂
        (KrelS_mono (le_of_lt hm') hK)
      rw [krelS_handleF] at hreinst
      have happ := krelS_append (Dᵢ := CTy.F q A) hKi
        (show HandlerRel Eff Mult m' (Handler.state ℓ s₁) (Handler.state ℓ s₂) from
          ⟨rfl, S, VrelK_mono (le_of_lt hm') hsv⟩)
        (KrelS_mono (le_of_lt hm') hK) hreinst.2.2.2
      -- ◊4.5b-strengthen: SUPPLY the decomposition — the dispatched config is `(Kᵢ++reinstall::K, ret sⱼ)`,
      -- the resume value `s₁~s₂` at `S`, the appended stack `KrelS`-related at the returner hole `F qᵣ S`.
      exact ⟨qᵣ, S, s₁, s₂, _, _, εᵢ, rfl, rfl, hcs₁, hcs₂, VrelK_mono (le_of_lt hm') hsv, happ⟩
    · -- PUT: cfg = (Kᵢ ++ handleF nh (state ℓ wⱼ)::Kⱼ, ret unit); reinstalled state = the payload (related at
      -- S via hVrel), resume value = unit (trivially related). The IH at the NEW state pair (w₁,w₂).
      have hwS : VrelK m' S w₁ w₂ := hVrel S (by rw [Handler.label]; exact hp)
      obtain ⟨qᵣ, rfl⟩ := hCᵢ VTy.unit (by rw [Handler.label]; exact hpr)
      simp only [Handler.label, dispatchOn] at hd₁ hd₂
      obtain rfl := (Option.some.injEq _ _).mp hd₁.symm
      obtain rfl := (Option.some.injEq _ _).mp hd₂.symm
      have hreinst := ih m' hm' w₁ w₂ hcw₁ hcw₂ hwS K₁ K₂ (KrelS_mono (le_of_lt hm') hK)
      rw [krelS_handleF] at hreinst
      have happ := krelS_append (Dᵢ := CTy.F q A) hKi
        (show HandlerRel Eff Mult m' (Handler.state ℓ w₁) (Handler.state ℓ w₂) from ⟨rfl, S, hwS⟩)
        (KrelS_mono (le_of_lt hm') hK) hreinst.2.2.2
      -- ◊4.5b-strengthen: PUT resumes `unit` (unit~unit); the appended stack relates at hole `F qᵣ unit`.
      exact ⟨qᵣ, VTy.unit, Val.vunit, Val.vunit, _, _, εᵢ, rfl, rfl, (fun k => rfl), (fun k => rfl),
        (by show VrelK m' VTy.unit Val.vunit Val.vunit; rw [VrelK, BaseRel]; exact ⟨rfl, rfl⟩), happ⟩

/-! ### ◊4.5b-append — heap `getD` facts, proved GetD-IMPORT-FREE (from `List.Basic`'s `getElem?`).
`Mathlib.Data.List.GetD` is deliberately NOT imported (it tips the `crelK_fund` mutual block's
structural-recursion inference past the heartbeat budget). All heap `getD` reasoning routes through
`List.getD_eq_getElem?_getD` (transitively available) + `getElem?` lemmas from `List.Basic`. -/

theorem heap_getD_append_left (l l' : List Val) (d : Val) (n : Nat) (h : n < l.length) :
    (l ++ l').getD n d = l.getD n d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem heap_getD_append_mid (l : List Val) (w : Val) (d : Val) :
    (l ++ [w]).getD l.length d = w := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]; simp

theorem heap_getD_default (l : List Val) (d : Val) (n : Nat) (h : l.length ≤ n) :
    l.getD n d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

theorem heap_getD_get (l : List Val) (d : Val) (n : Nat) (h : n < l.length) :
    l.getD n d = l[n] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

/-- ◊4.5b-append the heap-relation for `transaction` (length-eq + pointwise int). Explicit `Eff Mult`
(Store monomorphic). int cells ⇒ related = equal int. -/
def HeapRel (Eff Mult : Type) [Lattice Eff] [OrderBot Eff] [CommSemiring Mult] [DecidableEq Mult]
    [EffSig Eff Mult] (n : Nat) (Θ₁ Θ₂ : Store) : Prop :=
  Θ₁.length = Θ₂.length ∧
    ∀ i : Nat, i < Θ₁.length →
      VrelK (Eff := Eff) (Mult := Mult) n (VTy.int : VTy Eff Mult)
        (Θ₁.getD i (Val.vint 0)) (Θ₂.getD i (Val.vint 0))

/-- ◊4.5b-append `HeapRel n Θ Θ` from all-cells-`int`, WITHOUT `vrelK_fund` — int is a base type, so each
cell self-relates by `BaseRel` (`HasVTy.vint` is the SOLE `int` constructor ⇒ `cell = vint a`). This MUST
avoid `vrelK_fund`: the `crelK_fund` handleTransaction arm would otherwise call it on `hcells` (a SIDE-
condition, NOT a sub-derivation of the handle node) — breaking the mutual block's structural recursion. -/
theorem heapRel_self_of_cells_int (n : Nat) (Θ : Store)
    (hcells : ∀ cell ∈ Θ, HasVTy (Eff := Eff) (Mult := Mult) [] [] cell VTy.int) :
    HeapRel Eff Mult n Θ Θ := by
  -- canonical form at `int` (its SOLE producer is `HasVTy.vint`): case on the typing with a GENERAL type
  -- `A` (the working codebase pattern) + the `A = int` equation, discharging non-`vint` constructors.
  have hcanon : ∀ {γ : GradeVec Mult} {cell : Val} {A : VTy Eff Mult},
      HasVTy γ ([] : TyCtx Eff Mult) cell A → A = VTy.int → ∃ a : Int, cell = Val.vint a := by
    intro γ cell A ht hA
    cases ht with
    | vint => exact ⟨_, rfl⟩
    | vvar hget => simp at hget
    | _ => exact absurd hA (by simp)
  refine ⟨rfl, fun i hi => ?_⟩
  have hmem : Θ.getD i (Val.vint 0) ∈ Θ := by
    rw [heap_getD_get _ _ _ hi]; exact List.getElem_mem hi
  obtain ⟨a, ha⟩ := hcanon (hcells _ hmem) rfl
  rw [ha, VrelK, BaseRel]; exact ⟨a, rfl, rfl⟩

/-- `dispatchOn (state _)` is total (factored OUT of the mutual block — keeps the producer arms cheap). -/
theorem dispatchOn_state_isSome (n : Nat) (op : OpId) (v : Val) (Kᵢ Kₒ : Stack) (ℓ : Label) (s : Val) :
    ∃ c, Bang.dispatchOn n op v (Kᵢ, Handler.state ℓ s, Kₒ) = some c := by
  rw [dispatchOn]; split <;> exact ⟨_, rfl⟩

/-- `dispatchOn (transaction _)` is total. -/
theorem dispatchOn_transaction_isSome (n : Nat) (op : OpId) (v : Val) (Kᵢ Kₒ : Stack) (ℓ : Label) (Θ : Store) :
    ∃ c, Bang.dispatchOn n op v (Kᵢ, Handler.transaction ℓ Θ, Kₒ) = some c := by
  unfold dispatchOn; split_ifs <;> first | exact ⟨_, rfl⟩ | (cases v <;> exact ⟨_, rfl⟩)

/-- ◊4.5b-append the TRANSACTION-reinstall lemma — the multi-cell resumptive heart (the `state` analogue
with a heap). GUARDED RECURSION on the index; newTVar/readTVar/writeTVar reinstall + resume,
`krelS_append`ed onto the reinstalled frame at the dropped index. Each op preserves `HeapRel` (int cells
related = equal). All heap `getD` via the GetD-free `heap_getD_*`. -/
theorem krelS_transaction_reinstall {q : Mult} {A : VTy Eff Mult} {D : CTy Eff Mult} {φ : Eff}
    {ℓ : Label} {g : Nat}
    (hnewA : EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "newTVar" = some VTy.int)
    (hnewR : EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "newTVar" = some VTy.int)
    (hreadA : EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "readTVar" = some VTy.int)
    (hreadR : EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "readTVar" = some VTy.int)
    (hwriteA : EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "writeTVar"
      = some (VTy.prod (VTy.int : VTy Eff Mult) VTy.int))
    (hwriteR : EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "writeTVar" = some VTy.unit)
    (hrestrict : ∀ op Θ', Bang.handlesOp (Handler.transaction ℓ Θ') ℓ op = true →
      op = "newTVar" ∨ op = "readTVar" ∨ op = "writeTVar") :
    ∀ (nh : Nat) m (Θ₁ Θ₂ : Store), HeapRel Eff Mult m Θ₁ Θ₂ →
      ∀ (K₁ K₂ : Stack), KrelS m (CTy.F q A) D φ g K₁ K₂ →
      KrelS m (CTy.F q A) D φ g (Frame.handleF nh (Handler.transaction ℓ Θ₁) :: K₁)
                              (Frame.handleF nh (Handler.transaction ℓ Θ₂) :: K₂) := by
  intro nh m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro Θ₁ Θ₂ hheap K₁ K₂ hK
    refine krelS_handleF_intro
      (show HandlerRel Eff Mult m (Handler.transaction ℓ Θ₁) (Handler.transaction ℓ Θ₂) from
        ⟨rfl, hheap.1, hheap.2⟩) hK ?_
    intro m' hm' op w₁ w₂ Cᵢ εᵢ Kᵢ Kᵢ' cfg₁ cfg₂ hcatch hcw₁ hcw₂ hVrel hKi hCᵢ hd₁ hd₂
    have hheap' : HeapRel Eff Mult m' Θ₁ Θ₂ := ⟨hheap.1, fun i hi => VrelK_mono (le_of_lt hm') (hheap.2 i hi)⟩
    rcases hrestrict op Θ₁ hcatch with rfl | rfl | rfl
    · -- newTVar: reinstall Θⱼ ++ [wⱼ], resume `vint Θⱼ.length` (same length ⇒ equal int).
      obtain ⟨qᵣ, rfl⟩ := hCᵢ VTy.int (by rw [Handler.label]; exact hnewR)
      have hwint : VrelK m' VTy.int w₁ w₂ := hVrel VTy.int (by rw [Handler.label]; exact hnewA)
      simp only [Handler.label, dispatchOn] at hd₁ hd₂
      obtain rfl := (Option.some.injEq _ _).mp hd₁.symm
      obtain rfl := (Option.some.injEq _ _).mp hd₂.symm
      have happend : HeapRel Eff Mult m' (Θ₁ ++ [w₁]) (Θ₂ ++ [w₂]) := by
        refine ⟨by simp [hheap'.1], fun i hi => ?_⟩
        simp only [List.length_append, List.length_cons, List.length_nil] at hi
        by_cases hlt : i < Θ₁.length
        · rw [heap_getD_append_left _ _ _ _ hlt, heap_getD_append_left _ _ _ _ (hheap'.1 ▸ hlt)]
          exact hheap'.2 i hlt
        · have hi1 : i = Θ₁.length := by omega
          subst hi1
          rw [heap_getD_append_mid, hheap'.1, heap_getD_append_mid]; exact hwint
      have hreinst := ih m' hm' (Θ₁ ++ [w₁]) (Θ₂ ++ [w₂]) happend K₁ K₂ (KrelS_mono (le_of_lt hm') hK)
      rw [krelS_handleF] at hreinst
      have happ := krelS_append (Dᵢ := CTy.F q A) hKi
        (show HandlerRel Eff Mult m' (Handler.transaction ℓ (Θ₁ ++ [w₁])) (Handler.transaction ℓ (Θ₂ ++ [w₂]))
          from ⟨rfl, happend.1, happend.2⟩) (KrelS_mono (le_of_lt hm') hK) hreinst.2.2.2
      -- ◊4.5b-strengthen: SUPPLY the decomposition — resume `vint Θⱼ.length` (related; same length).
      exact ⟨qᵣ, VTy.int, Val.vint Θ₁.length, Val.vint Θ₂.length, _, _, εᵢ, rfl, rfl,
        (fun k => rfl), (fun k => rfl),
        (by show VrelK m' VTy.int (Val.vint Θ₁.length) (Val.vint Θ₂.length)
            rw [VrelK, BaseRel]; exact ⟨Θ₁.length, rfl, by rw [hheap'.1]⟩), happ⟩
    · -- readTVar: heap UNCHANGED, resume the cell (related via hheap', or default both sides).
      obtain ⟨qᵣ, rfl⟩ := hCᵢ VTy.int (by rw [Handler.label]; exact hreadR)
      have hweq : w₁ = w₂ := by
        have := hVrel VTy.int (by rw [Handler.label]; exact hreadA)
        rw [VrelK, BaseRel] at this; obtain ⟨a, rfl, rfl⟩ := this; rfl
      subst hweq
      simp only [Handler.label, dispatchOn] at hd₁ hd₂
      obtain rfl := (Option.some.injEq _ _).mp hd₁.symm
      obtain rfl := (Option.some.injEq _ _).mp hd₂.symm
      set idx := (Bang.tvarIdx w₁).getD 0 with hidx
      have hcellrel : VrelK (Eff := Eff) (Mult := Mult) m' VTy.int
          (Θ₁.getD idx (Val.vint 0)) (Θ₂.getD idx (Val.vint 0)) := by
        by_cases hlt : idx < Θ₁.length
        · exact hheap'.2 idx hlt
        · rw [heap_getD_default _ _ _ (by omega), heap_getD_default _ _ _ (by rw [← hheap'.1]; omega)]
          rw [VrelK, BaseRel]; exact ⟨0, rfl, rfl⟩
      obtain ⟨a, hca₁, hca₂⟩ : ∃ a : Int, Θ₁.getD idx (Val.vint 0) = Val.vint a ∧
          Θ₂.getD idx (Val.vint 0) = Val.vint a := by
        have := hcellrel; rw [VrelK, BaseRel] at this; exact this
      have hreinst := ih m' hm' Θ₁ Θ₂ hheap' K₁ K₂ (KrelS_mono (le_of_lt hm') hK)
      rw [krelS_handleF] at hreinst
      have happ := krelS_append (Dᵢ := CTy.F q A) hKi
        (show HandlerRel Eff Mult m' (Handler.transaction ℓ Θ₁) (Handler.transaction ℓ Θ₂)
          from ⟨rfl, hheap'.1, hheap'.2⟩) (KrelS_mono (le_of_lt hm') hK) hreinst.2.2.2
      -- ◊4.5b-strengthen: SUPPLY the decomposition — resume the read cell (related via `hcellrel`).
      exact ⟨qᵣ, VTy.int, Θ₁.getD idx (Val.vint 0), Θ₂.getD idx (Val.vint 0), _, _, εᵢ, rfl, rfl,
        (by rw [hca₁]; intro k; rfl), (by rw [hca₂]; intro k; rfl), hcellrel, happ⟩
    · -- writeTVar: payload `pair (vint i) (vint b)`; reinstall `storeSet Θⱼ i (vint b)`, resume unit.
      obtain ⟨qᵣ, rfl⟩ := hCᵢ VTy.unit (by rw [Handler.label]; exact hwriteR)
      have hpair := hVrel (VTy.prod VTy.int VTy.int) (by rw [Handler.label]; exact hwriteA)
      rw [VrelK] at hpair
      obtain ⟨a₁, a₂, b₁, b₂, rfl, rfl, hia, hib⟩ := hpair
      rw [VrelK, BaseRel] at hia hib
      obtain ⟨i, rfl, rfl⟩ := hia
      obtain ⟨b, rfl, rfl⟩ := hib
      simp only [Handler.label, dispatchOn] at hd₁ hd₂
      obtain rfl := (Option.some.injEq _ _).mp hd₁.symm
      obtain rfl := (Option.some.injEq _ _).mp hd₂.symm
      set j := (Bang.tvarIdx (Val.vint i)).getD 0 with hj
      have hset : HeapRel Eff Mult m' (Bang.storeSet Θ₁ j (Val.vint b)) (Bang.storeSet Θ₂ j (Val.vint b)) := by
        refine ⟨by simp [Bang.storeSet, hheap'.1], fun kk hk => ?_⟩
        simp only [Bang.storeSet, List.length_set] at hk ⊢
        rw [heap_getD_get _ _ _ (by rw [List.length_set]; exact hk),
            heap_getD_get _ _ _ (by rw [List.length_set, ← hheap'.1]; exact hk)]
        by_cases hkj : kk = j
        · subst hkj
          rw [List.getElem_set_self, List.getElem_set_self]
          rw [VrelK, BaseRel]; exact ⟨b, rfl, rfl⟩
        · rw [List.getElem_set_ne (Ne.symm hkj), List.getElem_set_ne (Ne.symm hkj)]
          have := hheap'.2 kk hk
          rwa [heap_getD_get _ _ _ hk, heap_getD_get _ _ _ (by rw [← hheap'.1]; exact hk)] at this
      have hreinst := ih m' hm' _ _ hset K₁ K₂ (KrelS_mono (le_of_lt hm') hK)
      rw [krelS_handleF] at hreinst
      have happ := krelS_append (Dᵢ := CTy.F q A) hKi
        (show HandlerRel Eff Mult m' (Handler.transaction ℓ (Bang.storeSet Θ₁ j (Val.vint b)))
            (Handler.transaction ℓ (Bang.storeSet Θ₂ j (Val.vint b)))
          from ⟨rfl, hset.1, hset.2⟩) (KrelS_mono (le_of_lt hm') hK) hreinst.2.2.2
      -- ◊4.5b-strengthen: SUPPLY the decomposition — writeTVar resumes `unit`.
      exact ⟨qᵣ, VTy.unit, Val.vunit, Val.vunit, _, _, εᵢ, rfl, rfl, (fun k => rfl), (fun k => rfl),
        (by show VrelK m' VTy.unit Val.vunit Val.vunit; rw [VrelK, BaseRel]; exact ⟨rfl, rfl⟩), happ⟩

/-! ◊4.5b sub-block (f) — `splitAt`-DECOMPOSITION over `KrelS` (the producer-`up` enabler). With the
`h₁ = h₂` handleF clause, `splitAt` fires IDENTICALLY on the two related stacks: the SAME catching
handler `h` at the SAME position, and the OUTER tails `K₁ₒ, K₂ₒ` stay `KrelS`-related. The
`krelS_splitAtId_decomp` (ADR-0054/0055) form below supersedes the legacy `splitAt`-decomp — the
handleF-MISS arm dissolves under IDENTITY dispatch (`splitAtId` matches the cap's generative id, no
`handlesOp` walk-past). -/

/-- ADR-0053: `KrelS`-related stacks have the SAME handler count. `KrelS` forces matching frame KINDS
(`letF::letF`/`appF::appF`/`handleF::handleF`), so the handler skeletons coincide. This is what lets the
ABSOLUTE level→index conversion `handlerCount K - 1 - cap` agree on `K₁` and `K₂` at the dispatch seam. -/
theorem krelS_handlerCount_eq {n : Nat} :
    ∀ {K₁ K₂ : Stack} {C D : CTy Eff Mult} {e : Eff} {g : Nat},
      KrelS n C D e g K₁ K₂ → Bang.handlerCount K₁ = Bang.handlerCount K₂ := by
  intro K₁
  induction K₁ with
  | nil =>
      intro K₂ C D e g hK
      rcases K₂ with _ | ⟨fr, K⟩
      · rfl
      · simp only [KrelS] at hK
  | cons fr K₁' ih =>
      intro K₂ C D e g hK
      rcases K₂ with _ | ⟨fr₂, K₂'⟩
      · cases fr <;> simp only [KrelS] at hK
      · cases fr <;> cases fr₂ <;>
          first
          | (simp only [KrelS] at hK; done)
          | (rw [KrelS] at hK
             obtain ⟨_, _, _, _, _, _, htail⟩ := hK
             simp only [Bang.handlerCount]; exact ih htail)
          | (rw [KrelS] at hK
             obtain ⟨_, _, _, _, _, _, _, htail⟩ := hK
             simp only [Bang.handlerCount]; exact ih htail)
          | (have htail := (krelS_handleF.mp hK).2.2.1
             simp only [Bang.handlerCount]
             have := ih htail; omega)

theorem krelS_splitAtId_decomp {n : Nat} {C D : CTy Eff Mult} {e : Eff} {g : Nat}
    {K₁ K₂ : Stack} {nid : Nat} {K₁ᵢ K₁ₒ : Stack} {h : Handler}
    (hK : KrelS n C D e g K₁ K₂)
    (hsp : Bang.splitAtId K₁ nid = some (K₁ᵢ, h, K₁ₒ)) :
    -- ADR-0055: `splitAtId K₂ nid` fires at the SAME identity `nid` (the stacks share frame KINDS and,
    -- under canonical ids, the matching `handleF` ids — `krelS_handleF` forces `nh₁ = nh₂`) with a
    -- RELATED handler `h'` (`HandlerRel n h h'`). The handleF arm is a PURE ID TEST (`nh = nid` HIT /
    -- `nh ≠ nid` SKIP): the old `splitAt`-decomp's answer-type-determinism MISS wall DISSOLVES because
    -- `splitAtId` never tests `handlesOp` — it locates the catcher by identity, not by walking past
    -- non-catching handlers. (SKIP arm carries ONE documented relocation residual; see the sorry.)
    ∃ (K₂ᵢ K₂ₒ : Stack) (h' : Handler) (Dᵢ : CTy Eff Mult) (C' : CTy Eff Mult) (e' : Eff),
      Bang.splitAtId K₂ nid = some (K₂ᵢ, h', K₂ₒ) ∧ HandlerRel Eff Mult n h h' ∧
      KrelS n C Dᵢ e g K₁ᵢ K₂ᵢ ∧ KrelS n C' D e' g K₁ₒ K₂ₒ
      ∧ (∀ m, m < n → ∀ (op' : OpId) (w₁ w₂ : Val) (Cᵢ' : CTy Eff Mult) (εᵢ' : Eff)
            (Kᵢ Kᵢ' : Stack) (cfg₁ cfg₂ : EvalCtx × Comp),
          Bang.handlesOp h h.label op' = true →
          Val.Closed w₁ → Val.Closed w₂ →
          (∀ Aop, EffSig.opArg (Eff := Eff) (Mult := Mult) h.label op' = some Aop → VrelK m Aop w₁ w₂) →
          KrelS m Cᵢ' Dᵢ εᵢ' g Kᵢ Kᵢ' →
          (∀ Aᵣ, EffSig.opRes (Eff := Eff) (Mult := Mult) h.label op' = some Aᵣ →
            ∃ qᵣ, Cᵢ' = CTy.F qᵣ Aᵣ) →
          Bang.dispatchOn nid op' w₁ (Kᵢ, h, K₁ₒ) = some cfg₁ →
          Bang.dispatchOn nid op' w₂ (Kᵢ', h', K₂ₒ) = some cfg₂ →
          (∃ (qᵣ : Mult) (Aᵣ : VTy Eff Mult) (r₁ r₂ : Val) (Sᵢ Sᵢ' : Stack) (eₛ : Eff),
              cfg₁ = (Sᵢ, Comp.ret r₁) ∧ cfg₂ = (Sᵢ', Comp.ret r₂) ∧
              Val.Closed r₁ ∧ Val.Closed r₂ ∧ VrelK m Aᵣ r₁ r₂ ∧
              KrelS m (CTy.F qᵣ Aᵣ) D eₛ g Sᵢ Sᵢ')) := by
  induction K₁ generalizing K₂ K₁ᵢ K₁ₒ C e with
  | nil => simp [Bang.splitAtId] at hsp
  | cons fr K₁' ih =>
      match K₂ with
      | [] => exact absurd hK (by simp only [KrelS]; cases fr <;> exact not_false)
      | fr₂ :: K₂' =>
          cases fr with
          | letF N₁ =>
              cases fr₂ with
              | letF N₂ =>
                  rw [krelS_letF] at hK
                  obtain ⟨q, A, B, φ, hC, hbody, htail⟩ := hK
                  simp only [splitAtId, Option.map_eq_some_iff] at hsp
                  obtain ⟨⟨Ki', hh, Ko'⟩, hsp', heq⟩ := hsp
                  simp only [Prod.mk.injEq] at heq
                  obtain ⟨rfl, rfl, rfl⟩ := heq
                  obtain ⟨K₂ᵢ, K₂ₒ, h', Dᵢ, C', e', hsp2, hHR, hin, htail2, hres2⟩ := ih htail hsp'
                  refine ⟨Frame.letF N₂ :: K₂ᵢ, K₂ₒ, h', Dᵢ, C', e',
                    by simp only [splitAtId]; rw [hsp2]; rfl, hHR, ?_, htail2, hres2⟩
                  rw [krelS_letF]; exact ⟨q, A, B, φ, hC, hbody, hin⟩
              | _ => simp only [KrelS] at hK
          | appF w₁ =>
              cases fr₂ with
              | appF w₂ =>
                  rw [krelS_appF] at hK
                  obtain ⟨q, A, B, hC, hcw₁, hcw₂, hw, htail⟩ := hK
                  simp only [splitAtId, Option.map_eq_some_iff] at hsp
                  obtain ⟨⟨Ki', hh, Ko'⟩, hsp', heq⟩ := hsp
                  simp only [Prod.mk.injEq] at heq
                  obtain ⟨rfl, rfl, rfl⟩ := heq
                  obtain ⟨K₂ᵢ, K₂ₒ, h', Dᵢ, C', e', hsp2, hHR, hin, htail2, hres2⟩ := ih htail hsp'
                  refine ⟨Frame.appF w₂ :: K₂ᵢ, K₂ₒ, h', Dᵢ, C', e',
                    by simp only [splitAtId]; rw [hsp2]; rfl, hHR, ?_, htail2, hres2⟩
                  rw [krelS_appF]; exact ⟨q, A, B, hC, hcw₁, hcw₂, hw, hin⟩
              | _ => simp only [KrelS] at hK
          | handleF mh₁ hh₁ =>
              cases fr₂ with
              | handleF mh₂ hh₂ =>
                  rw [krelS_handleF] at hK
                  obtain ⟨hmid, hHRtop, htail, hres⟩ := hK
                  subst hmid
                  simp only [splitAtId] at hsp
                  by_cases hmn : mh₁ = nid
                  · -- HIT (`mh₁ = nid`): the split point. Inner prefix `[]` (nil at hole C), outer tail
                    -- K₁'/K₂' (related via `htail`), resume conjunct `hres` is the catching frame's
                    -- Kᵢ-threading one directly (its dispatch id IS `nid` after the `subst`).
                    subst hmn
                    rw [if_pos rfl, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hsp
                    obtain ⟨rfl, rfl, rfl⟩ := hsp
                    refine ⟨[], K₂', hh₂, C, C, e,
                      by simp [splitAtId], hHRtop, ?_, htail, hres⟩
                    rw [krelS_nil]; exact ⟨rfl, fun q A hC v₁ v₂ _ _ _ _ => ⟨1, v₂, rfl⟩⟩
                  · -- SKIP (`mh₁ ≠ nid`): the id test fails — recurse with the SAME `nid` on the tail.
                    -- The skipped handleF wraps the inner prefix. The MISS edge is GONE (identity dispatch
                    -- located the catcher by `nid`, NOT by walking past hh₁ — no answer-type-determinism wall).
                    rw [if_neg hmn, Option.map_eq_some_iff] at hsp
                    obtain ⟨⟨Ki', hh, Ko'⟩, hsp', heq⟩ := hsp
                    simp only [Prod.mk.injEq] at heq
                    obtain ⟨rfl, rfl, rfl⟩ := heq
                    obtain ⟨K₂ᵢ, K₂ₒ, h', Dᵢ, C', e', hsp2, hHR, hin, htail2, hres2⟩ := ih htail hsp'
                    refine ⟨Frame.handleF mh₁ hh₂ :: K₂ᵢ, K₂ₒ, h', Dᵢ, C', e',
                      by simp only [splitAtId]; rw [if_neg hmn, hsp2]; rfl, hHR, ?_, htail2, hres2⟩
                    -- the skipped handleF wraps the inner prefix: `KrelS n C Dᵢ e (handleF mh₁ hh₁::K₁ᵢ)(…)`.
                    -- `krelS_handleF_intro` rebuilds it from `hHRtop` + `hin` (inner relation, hole C,
                    -- answer Dᵢ) + a resume conjunct.
                    refine krelS_handleF_intro (nh := mh₁) hHRtop hin ?_
                    -- ADR-0055 SKIP RESIDUAL (the old 1628 relocation sorry, identity-keyed): `hres` (hh₁'s
                    -- resume over the ORIGINAL tail `K₁'`) must RELOCATE to the recursed inner prefix `Ki'`
                    -- (where `splitAtId` placed the deeper catcher). `K₁' = Ki' ++ handleF nid h' :: Ko'`
                    -- (`splitAtId_decomp hsp'`), so `dispatchOn` over `Ki'` lifts to `K₁'` via
                    -- `dispatchOn_append_outer` — but the conjunct demands the INVERSE (strip the appended
                    -- tail off a decomposition over the longer stack), which `hres` over `K₁'` does not
                    -- factor through in general. The dissolution is REAL (no `handlesOp` wall); the residual
                    -- is this one clean relocation. Scoped here for the SKIP arm. shape: biernacki-popl18 §5.4.
                    sorry
              | _ => simp only [KrelS] at hK

-- ◊inc-5 the op-PRODUCER, re-keyed to ADR-0054/0055 IDENTITY dispatch. The capability is now a VALUE
-- `vcap m ℓ` (VrelK at cap type forces the SAME id `m` both sides, LR:1427); `Source.step` resolves it via
-- `idDispatch K m ℓ op v = (splitAtId K m).bind (handlesOp-guard ∘ dispatchOn m)`. STANDALONE ⇒ a
-- `set_option maxHeartbeats` is safe (no mutual structural-recursion inference).
set_option maxHeartbeats 1000000 in
theorem crelK_fund_up {n : Nat} {m : Nat} {ℓ : Label} {op : OpId} {q : Mult} {A B : VTy Eff Mult} {φ : Eff}
    {v₁ v₂ : Val}
    (hArg : EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ op = some A)
    (hRes : EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ op = some B)
    (hcv₁ : Val.Closed v₁) (hcv₂ : Val.Closed v₂) (hvk : VrelK n A v₁ v₂) :
    CrelK n (CTy.F q B) φ (Comp.perform (Val.vcap m ℓ) op v₁) (Comp.perform (Val.vcap m ℓ) op v₂) := by
  -- ◊inc-5 STOP-AND-SHOW (the FROZEN-lr_sound guard, the value-carried mirror of the old ADR-0043 `:1707`
  -- seam). `Source.step (g, K₁, perform (vcap m ℓ) op v₁) = (idDispatch K₁ m ℓ op v₁).map (g, ·)`. To run
  -- the decomp (`krelS_splitAtId_decomp hK`) we first need `splitAtId K₁ m = some (Kᵢ, h, Kₒ)` AND the
  -- fail-loud guard `handlesOp h ℓ op = true` — i.e. `CapResolves K₁ m ℓ op` (the cap NON-ESCAPES in K₁).
  -- `KrelS` is purely structural + resume; it does NOT carry cap-resolution. And the resume values feed
  -- the guarded `crelK_ret`'s `CapsBelow 0` premise + a counter-bridge (the dispatched `g` vs the canonical
  -- `handlerCount Sᵢ`, `run_bump`). BOTH obligations are NonEscape/cap-scopedness facts about the OBSERVATION
  -- context K₁ — which the FROZEN `lr_sound`/`lr_fundamental` statements (Spec.lean) do not provide. So this
  -- arm PROPAGATES UP to the frozen statement: it is the ADR-0056/0057 escape-discipline question (B-occ,
  -- task #23), not internally dischargeable from `KrelS` alone. Held as a named sorry pending ADR-0057
  -- (the dissolution lemma `HasConfigTy ⟹ NonEscape` + the `CapsBelow` discharge it licenses).
  sorry

/-- ADR-0058 route 1: `KrelS` is INDEPENDENT of the threaded fresh-id counter `g`. The counter only
pins the nil return-half (discharged at ANY `g` by `⟨1,v₂,rfl⟩`, a `ret` converges regardless) and
threads through the resume conjunct (recursively re-cast at `m < n`). MINT advances `g → g+1`, so
running a handle body through the freshly pushed `handleF g` frame needs the ambient observation tail
re-cast from the pre-MINT `g` to the post-MINT `g+1`. Well-founded on `(n, K₁.length)`: tail recursion
drops the length at fixed `n`; the conjunct recursion drops `n` (`m < n`) at an arbitrary `Kᵢ`. -/
theorem KrelS_g_cast : ∀ (n : Nat) {C D : CTy Eff Mult} {ε : Eff} (g g' : Nat) (K₁ K₂ : Stack),
    KrelS n C D ε g K₁ K₂ → KrelS n C D ε g' K₁ K₂
  | _, _, _, _, _, _, [], [], hK => by
      rw [krelS_nil] at hK ⊢
      exact ⟨hK.1, fun q A hC v₁ v₂ _ _ _ _ => ⟨1, v₂, rfl⟩⟩
  | n, _, _, _, g, g', (Frame.letF N₁ :: K₁'), (Frame.letF N₂ :: K₂'), hK => by
      rw [krelS_letF] at hK ⊢
      obtain ⟨q, A, B, φ, hC, hbody, htail⟩ := hK
      exact ⟨q, A, B, φ, hC, hbody, KrelS_g_cast n g g' K₁' K₂' htail⟩
  | n, _, _, _, g, g', (Frame.appF w₁ :: K₁'), (Frame.appF w₂ :: K₂'), hK => by
      rw [krelS_appF] at hK ⊢
      obtain ⟨q, A, B, hC, hcw₁, hcw₂, hw, htail⟩ := hK
      exact ⟨q, A, B, hC, hcw₁, hcw₂, hw, KrelS_g_cast n g g' K₁' K₂' htail⟩
  | n, _, _, _, g, g', (Frame.handleF nh h :: K₁'), (Frame.handleF nh' h' :: K₂'), hK => by
      rw [krelS_handleF] at hK ⊢
      obtain ⟨hid, hh, htail, hres⟩ := hK
      refine ⟨hid, hh, KrelS_g_cast n g g' K₁' K₂' htail, ?_⟩
      intro m hm op w₁ w₂ Cᵢ εᵢ Kᵢ Kᵢ' cfg₁ cfg₂ hcatch hcw₁ hcw₂ hVrel hKi hCᵢ hd₁ hd₂
      obtain ⟨qᵣ, Aᵣ, r₁, r₂, Sᵢ, Sᵢ', eₛ, hcfg1, hcfg2, hcr1, hcr2, hvr, hSk⟩ :=
        hres m hm op w₁ w₂ Cᵢ εᵢ Kᵢ Kᵢ' cfg₁ cfg₂ hcatch hcw₁ hcw₂ hVrel
          (KrelS_g_cast m g' g Kᵢ Kᵢ' hKi) hCᵢ hd₁ hd₂
      exact ⟨qᵣ, Aᵣ, r₁, r₂, Sᵢ, Sᵢ', eₛ, hcfg1, hcfg2, hcr1, hcr2, hvr,
        KrelS_g_cast m g g' Sᵢ Sᵢ' hSk⟩
  | _, _, _, _, _, _, [], (_ :: _), hK => by simp only [KrelS] at hK
  | _, _, _, _, _, _, (_ :: _), [], hK => by simp only [KrelS] at hK
  | _, _, _, _, _, _, (Frame.letF _ :: _), (Frame.appF _ :: _), hK => by simp only [KrelS] at hK
  | _, _, _, _, _, _, (Frame.letF _ :: _), (Frame.handleF _ _ :: _), hK => by simp only [KrelS] at hK
  | _, _, _, _, _, _, (Frame.appF _ :: _), (Frame.letF _ :: _), hK => by simp only [KrelS] at hK
  | _, _, _, _, _, _, (Frame.appF _ :: _), (Frame.handleF _ _ :: _), hK => by simp only [KrelS] at hK
  | _, _, _, _, _, _, (Frame.handleF _ _ :: _), (Frame.letF _ :: _), hK => by simp only [KrelS] at hK
  | _, _, _, _, _, _, (Frame.handleF _ _ :: _), (Frame.appF _ :: _), hK => by simp only [KrelS] at hK
termination_by n _ _ _ _ _ K₁ _ _ => (n, K₁.length)
decreasing_by
  all_goals simp_wf
  · exact Prod.Lex.right _ (by simp)
  · exact Prod.Lex.right _ (by simp)
  · exact Prod.Lex.right _ (by simp)
  · exact Prod.Lex.left _ _ hm
  · exact Prod.Lex.left _ _ hm

/-- ◊4.5b the `handleThrows` compat core at `CrelK`, ADR-0054/0055 cap-binding. MINT
`(g, K, handle (throws ℓ) M) ↦ (g+1, handleF g (throws ℓ)::K, subst (vcap g ℓ) M)` — the handle BINDS
the capability `vcap g ℓ` at body var 0 (the SAME fresh `g` it pushes). So the premise is CAP-QUANTIFIED
`∀ gid, CrelK … (subst (vcap gid ℓ) M₁) (subst (vcap gid ℓ) M₂)` (the body related under the cap binder,
parallel `compatK_lam`); instantiated at the minted `gid := g`. The observation counter advances to
`g+1`, so the ambient tail `hK` is re-cast `g → g+1` via `KrelS_g_cast`. The block discharges `ℓ` from
`e` to `φ`. shape: biernacki-popl18 §5.4 (throws zero-shot arm). -/
theorem compatK_handleThrows {n : Nat} {q : Mult} {A : VTy Eff Mult} {e φ : Eff} {ℓ : Label}
    {M₁ M₂ : Comp}
    (hArg : EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "raise" = some A)
    (hbody : ∀ gid, CrelK n (CTy.F q A) e
      (Comp.subst (Val.vcap gid ℓ) M₁) (Comp.subst (Val.vcap gid ℓ) M₂)) :
    CrelK n (CTy.F q A) φ (Comp.handle (Handler.throws ℓ) M₁) (Comp.handle (Handler.throws ℓ) M₂) := by
  rw [CrelK]
  intro g D K₁ K₂ hK
  refine coApproxC_le_reduce
    (cfg₁' := (g + 1, Frame.handleF g (Handler.throws ℓ) :: K₁, Comp.subst (Val.vcap g ℓ) M₁))
    (cfg₂' := (g + 1, Frame.handleF g (Handler.throws ℓ) :: K₂, Comp.subst (Val.vcap g ℓ) M₂))
    rfl (by intro g' u; simp) rfl (by intro g' u; simp) ?_
  have hb := hbody g
  rw [CrelK] at hb
  refine hb (g + 1) D (Frame.handleF g (Handler.throws ℓ) :: K₁)
    (Frame.handleF g (Handler.throws ℓ) :: K₂)
    (krelS_handleF_intro (nh := g) (by simp only [HandlerRel])
      (KrelS_g_cast n g (g + 1) K₁ K₂ hK) ?_)
  -- THROWS resume supply: `dispatchOn op w (Kᵢ, throws ℓ, Kⱼ) = (Kⱼ, ret w)` (zero-shot abort — Kᵢ
  -- DISCARDED). `handlesOp` forces `op = "raise"`, so `opArg ℓ "raise" = A` (hArg) gives `VrelK m A w`;
  -- the dispatched config IS the tail's return-half on the re-cast (`g+1`) tail at hole `F q A`.
  intro m hm op w₁ w₂ Cᵢ εᵢ Kᵢ Kᵢ' cfg₁ cfg₂ hcatch hcw₁ hcw₂ hVrel _hKi _hCᵢ hd₁ hd₂
  have hop : op = "raise" := by
    simp only [Handler.label, handlesOp, Bool.and_eq_true, beq_iff_eq] at hcatch; exact hcatch.2
  subst hop
  have hw : VrelK m A w₁ w₂ := hVrel A (by rw [Handler.label]; exact hArg)
  simp only [dispatchOn] at hd₁ hd₂
  obtain rfl := (Option.some.injEq _ _).mp hd₁.symm
  obtain rfl := (Option.some.injEq _ _).mp hd₂.symm
  exact ⟨q, A, w₁, w₂, K₁, K₂, φ, rfl, rfl, hcw₁, hcw₂, hw,
    KrelS_mono (le_of_lt hm) (KrelS_g_cast n g (g + 1) K₁ K₂ hK)⟩

/-- ◊4.5b-append the `handleState` compat core at `CrelK`, ADR-0054/0055 cap-binding. MINT
`(g, K, handle (state ℓ s) M) ↦ (g+1, handleF g (state ℓ s)::K, subst (vcap g ℓ) M)`. CAP-QUANTIFIED
premise `hbody` (cap binds body var 0, parallel `compatK_lam`); the reinstalling stack is shown
`KrelS`-related at the minted frame id `g` and post-MINT counter `g+1` by `krelS_state_reinstall` (the
resumptive heart), the ambient tail re-cast `g → g+1` via `KrelS_g_cast`. The interface (get/put sig) +
the stored state's self-relation `hsv` are threaded from the caller's `HasCTy.handleState` typing. -/
theorem compatK_handleState {n : Nat} {q : Mult} {A S : VTy Eff Mult} {e φ : Eff} {ℓ : Label} {s : Val}
    {M₁ M₂ : Comp}
    (hgr : EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "get" = some S)
    (hp : EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "put" = some S)
    (hpr : EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "put" = some VTy.unit)
    (hrestrict : ∀ op s', Bang.handlesOp (Handler.state ℓ s') ℓ op = true → op = "get" ∨ op = "put")
    (hcs : Val.Closed s) (hsv : ∀ k, VrelK k S s s)
    (hbody : ∀ gid, CrelK n (CTy.F q A) e
      (Comp.subst (Val.vcap gid ℓ) M₁) (Comp.subst (Val.vcap gid ℓ) M₂)) :
    CrelK n (CTy.F q A) φ (Comp.handle (Handler.state ℓ s) M₁) (Comp.handle (Handler.state ℓ s) M₂) := by
  rw [CrelK]
  intro g D K₁ K₂ hK
  refine coApproxC_le_reduce
    (cfg₁' := (g + 1, Frame.handleF g (Handler.state ℓ s) :: K₁, Comp.subst (Val.vcap g ℓ) M₁))
    (cfg₂' := (g + 1, Frame.handleF g (Handler.state ℓ s) :: K₂, Comp.subst (Val.vcap g ℓ) M₂))
    rfl (by intro g' u; simp) rfl (by intro g' u; simp) ?_
  have hb := hbody g
  rw [CrelK] at hb
  -- discharge the row `φ → e` (`KrelS_eff_cast`) + counter `g → g+1` (`KrelS_g_cast`) on the tail.
  exact hb (g + 1) D (Frame.handleF g (Handler.state ℓ s) :: K₁)
    (Frame.handleF g (Handler.state ℓ s) :: K₂)
    (krelS_state_reinstall hgr hp hpr hrestrict g n s s hcs hcs (hsv n) K₁ K₂
      (KrelS_g_cast n g (g + 1) K₁ K₂ (KrelS_eff_cast hK)))

/-- ◊4.5b the `handleTransaction` compat core at `CrelK`, ADR-0054/0055 cap-binding. The multi-cell
resumptive analogue — same MINT shape (`handleF g (transaction ℓ Θ)::K`, `subst (vcap g ℓ)`, counter
`g+1`); the cap-QUANTIFIED body runs through the reinstalling stack via `krelS_transaction_reinstall`,
tail re-cast `g → g+1`. The heap `Θ` is arbitrary. -/
theorem compatK_handleTransaction {n : Nat} {q : Mult} {A : VTy Eff Mult} {e φ : Eff} {ℓ : Label}
    {Θ : Store} {M₁ M₂ : Comp}
    (hnewA : EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "newTVar" = some VTy.int)
    (hnewR : EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "newTVar" = some VTy.int)
    (hreadA : EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "readTVar" = some VTy.int)
    (hreadR : EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "readTVar" = some VTy.int)
    (hwriteA : EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "writeTVar"
      = some (VTy.prod (VTy.int : VTy Eff Mult) VTy.int))
    (hwriteR : EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "writeTVar" = some VTy.unit)
    (hrestrict : ∀ op Θ', Bang.handlesOp (Handler.transaction ℓ Θ') ℓ op = true →
      op = "newTVar" ∨ op = "readTVar" ∨ op = "writeTVar")
    (hheap : HeapRel Eff Mult n Θ Θ)
    (hbody : ∀ gid, CrelK n (CTy.F q A) e
      (Comp.subst (Val.vcap gid ℓ) M₁) (Comp.subst (Val.vcap gid ℓ) M₂)) :
    CrelK n (CTy.F q A) φ (Comp.handle (Handler.transaction ℓ Θ) M₁)
                          (Comp.handle (Handler.transaction ℓ Θ) M₂) := by
  rw [CrelK]
  intro g D K₁ K₂ hK
  refine coApproxC_le_reduce
    (cfg₁' := (g + 1, Frame.handleF g (Handler.transaction ℓ Θ) :: K₁, Comp.subst (Val.vcap g ℓ) M₁))
    (cfg₂' := (g + 1, Frame.handleF g (Handler.transaction ℓ Θ) :: K₂, Comp.subst (Val.vcap g ℓ) M₂))
    rfl (by intro g' u; simp) rfl (by intro g' u; simp) ?_
  have hb := hbody g
  rw [CrelK] at hb
  exact hb (g + 1) D (Frame.handleF g (Handler.transaction ℓ Θ) :: K₁)
    (Frame.handleF g (Handler.transaction ℓ Θ) :: K₂)
    (krelS_transaction_reinstall hnewA hnewR hreadA hreadR hwriteA hwriteR hrestrict g n Θ Θ hheap
      K₁ K₂ (KrelS_g_cast n g (g + 1) K₁ K₂ (KrelS_eff_cast hK)))


/-- A well-typed value is `ScopedIn Γ.length` (`HasVTy.shift_closed`: shifting at a cutoff `≥ Γ.length`
is the identity). The bridge from the typing derivation to the syntactic scope bound that
`closeV_closed_scoped` consumes. -/
theorem HasVTy.scopedIn {γ : GradeVec Mult} {Γ : TyCtx Eff Mult} {v : Val} {A : VTy Eff Mult}
    (h : HasVTy γ Γ v A) : Val.ScopedIn Γ.length v := fun k hk => h.shift_closed k hk



/-! ### B.5′ ◊4.5b — the migrated fundamental theorem (`vrelK_fund` / `crelK_fund`) over `CrelK`/`KrelS`

The answer-typed migration of `vrel_fund`/`crel_fund`, wiring the `compatK_*` cores (sub-block c) over
`EnvRelK`. The non-handler cases and the 3 handler cases all CLOSE — the absolute-cap representation
dissolved the shift wall (`closeC_handle*` rewrite unshifted), so the arms close on their
`compatK_handle*` cores. The remaining obligations: `crelK_fund_up` holds ONE propagated `sorry` (the
ADR-0056/0057 cap-escape / B-occ question, task #23), plus the `krelS_splitAtId_decomp` SKIP relocation
residual. The Kripke continuation indices use `∀ m < n` at the letC/case/split seams (the `compatK_*`
cores' ▷-guarded shape) and `∀ j ≤ n` would over-supply. -/
mutual
theorem vrelK_fund {γ : GradeVec Mult} {Γ : TyCtx Eff Mult} {v : Val} {A : VTy Eff Mult}
    (h : HasVTy γ Γ v A) :
    ∀ (n : Nat) (δ₁ δ₂ : List Val), EnvRelK n Γ δ₁ δ₂ →
      VrelK n A (closeV δ₁ v) (closeV δ₂ v) := by
  cases h with
  | vunit => intro n δ₁ δ₂ _; rw [closeV_vunit, closeV_vunit, VrelK]; exact ⟨rfl, rfl⟩
  | vint  => intro n δ₁ δ₂ _; rw [closeV_vint, closeV_vint, VrelK]; exact ⟨_, rfl, rfl⟩
  | @vcap _ nid ℓ =>
      -- ADR-0054: a capability is a CLOSED absolute value `vcap nid ℓ` (no de-Bruijn var), so `closeV`
      -- leaves it fixed. `VrelK` at `cap ℓ` forces the SAME id + label both sides — `⟨nid, rfl, rfl⟩`.
      intro n δ₁ δ₂ _
      have hcap : Val.Closed (Val.vcap nid ℓ) := fun k => rfl
      rw [closeV_closed hcap, closeV_closed hcap, VrelK]
      exact ⟨nid, rfl, rfl⟩
  | @vvar _ i _ hget =>
      intro n δ₁ δ₂ hδ
      have hlen₁ := hδ.length_left
      have hlen₂ := hδ.length_right
      have hi : i < Γ.length := by rw [List.getElem?_eq_some_iff] at hget; exact hget.1
      rw [closeV_vvar (hδ.closed_left) (by omega) Val.vunit,
          closeV_vvar (hδ.closed_right) (by omega) Val.vunit]
      exact hδ.vrel_at hget Val.vunit Val.vunit
  | @vthunk _ _ M φ B hM =>
      intro n δ₁ δ₂ hδ
      rw [closeV_vthunk, closeV_vthunk, VrelK]
      -- ◊4.5b the U-clause is `∀ j < n`: supply `CrelK j` for each `j < n` via the IH at `j` on the
      -- `EnvRelK_mono`-weakened env (`j < n ⇒ j ≤ n`). The ▷-guarded thunk.
      exact ⟨closeC δ₁ M, closeC δ₂ M, rfl, rfl,
        fun j hjn => crelK_fund hM j δ₁ δ₂ (EnvRelK_mono (Nat.le_of_lt hjn) hδ)⟩
  | @inl _ _ w A B hw =>
      intro n δ₁ δ₂ hδ
      rw [closeV_inl, closeV_inl, VrelK]
      exact Or.inl ⟨_, _, rfl, rfl, vrelK_fund hw n δ₁ δ₂ hδ⟩
  | @inr _ _ w A B hw =>
      intro n δ₁ δ₂ hδ
      rw [closeV_inr, closeV_inr, VrelK]
      exact Or.inr ⟨_, _, rfl, rfl, vrelK_fund hw n δ₁ δ₂ hδ⟩
  | @pair _ _ _ _ a b A B ha hb _ =>
      intro n δ₁ δ₂ hδ
      rw [closeV_pair, closeV_pair, VrelK]
      exact ⟨_, _, _, _, rfl, rfl, vrelK_fund ha n δ₁ δ₂ hδ, vrelK_fund hb n δ₁ δ₂ hδ⟩
  | @fold _ _ w A hw =>
      intro n δ₁ δ₂ hδ
      rw [closeV_fold, closeV_fold, VrelK]
      exact ⟨_, _, rfl, rfl,
        fun j hjn => vrelK_fund hw j δ₁ δ₂ (EnvRelK_mono (Nat.le_of_lt hjn) hδ)⟩

theorem crelK_fund {γ : GradeVec Mult} {Γ : TyCtx Eff Mult} {c : Comp} {e : Eff} {B : CTy Eff Mult}
    (h : HasCTy γ Γ c e B) :
    ∀ (n : Nat) (δ₁ δ₂ : List Val), EnvRelK n Γ δ₁ δ₂ →
      CrelK n B e (closeC δ₁ c) (closeC δ₂ c) := by
  cases h with
  | @ret _ _ _ v A q hv _ =>
      intro n δ₁ δ₂ hδ
      rw [closeC_ret, closeC_ret]
      have hsc₁ : Val.Closed (closeV δ₁ v) :=
        closeV_closed_scoped hδ.closed_left (by have := hv.scopedIn; rwa [hδ.length_left])
      have hsc₂ : Val.Closed (closeV δ₂ v) :=
        closeV_closed_scoped hδ.closed_right (by have := hv.scopedIn; rwa [hδ.length_right])
      -- ROUTE-1: `crelK_ret` gives the unfolded `CrelK` body per observation context; unfold + apply.
      rw [CrelK]; intro g D K₁ K₂ hK
      exact crelK_ret g D K₁ K₂ hK hsc₁ hsc₂ (vrelK_fund hv n δ₁ δ₂ hδ)
  | @letC _ _ _ _ M N φ₁ φ₂ q1 q2 A B hM hN _ =>
      intro n δ₁ δ₂ hδ
      rw [closeC_letC, closeC_letC]
      refine compatK_letC (q1 := q1) (crelK_fund hM n δ₁ δ₂ hδ) ?_
      -- ▷-guarded continuation: at EVERY `m < n`, on the `EnvRelK_mono`-weakened env.
      intro m hmn v₁ v₂ hcv₁ hcv₂ hvrel
      rw [closeC_subst_comm hδ.closed_left hcv₁, closeC_subst_comm hδ.closed_right hcv₂]
      have hδ' : EnvRelK m (A :: Γ) (v₁ :: δ₁) (v₂ :: δ₂) := by
        rw [EnvRelK]; exact ⟨hcv₁, hcv₂, hvrel, EnvRelK_mono (Nat.le_of_lt hmn) hδ⟩
      have := crelK_fund hN m (v₁ :: δ₁) (v₂ :: δ₂) hδ'
      rwa [show closeC (v₁ :: δ₁) N = closeC δ₁ (Comp.subst v₁ N) from rfl,
           show closeC (v₂ :: δ₂) N = closeC δ₂ (Comp.subst v₂ N) from rfl] at this
  | @force _ _ v φ B hv =>
      intro n δ₁ δ₂ hδ
      rw [closeC_force, closeC_force]
      exact crelK_force (vrelK_fund hv n δ₁ δ₂ hδ)
  | @lam _ _ M φ q A B hM =>
      intro n δ₁ δ₂ hδ
      rw [closeC_lam, closeC_lam]
      refine compatK_lam ?_
      intro w₁ w₂ hcw₁ hcw₂ hw
      rw [closeC_subst_comm hδ.closed_left hcw₁, closeC_subst_comm hδ.closed_right hcw₂]
      have hδ' : EnvRelK n (A :: Γ) (w₁ :: δ₁) (w₂ :: δ₂) := by
        rw [EnvRelK]; exact ⟨hcw₁, hcw₂, hw, hδ⟩
      have := crelK_fund hM n (w₁ :: δ₁) (w₂ :: δ₂) hδ'
      rwa [show closeC (w₁ :: δ₁) M = closeC δ₁ (Comp.subst w₁ M) from rfl,
           show closeC (w₂ :: δ₂) M = closeC δ₂ (Comp.subst w₂ M) from rfl] at this
  | @app _ _ _ _ M v φ q A B hM hv _ =>
      intro n δ₁ δ₂ hδ
      rw [closeC_app, closeC_app]
      have hscv₁ : Val.Closed (closeV δ₁ v) :=
        closeV_closed_scoped hδ.closed_left (by have := hv.scopedIn; rwa [hδ.length_left])
      have hscv₂ : Val.Closed (closeV δ₂ v) :=
        closeV_closed_scoped hδ.closed_right (by have := hv.scopedIn; rwa [hδ.length_right])
      exact compatK_app (crelK_fund hM n δ₁ δ₂ hδ) hscv₁ hscv₂ (vrelK_fund hv n δ₁ δ₂ hδ)
  | @case _ _ _ _ v N₁ N₂ φ q A B C hv hN₁ hN₂ _ =>
      intro n δ₁ δ₂ hδ
      rw [closeC_case, closeC_case]
      have hscv₁ : Val.Closed (closeV δ₁ v) :=
        closeV_closed_scoped hδ.closed_left (by have := hv.scopedIn; rwa [hδ.length_left])
      have hscv₂ : Val.Closed (closeV δ₂ v) :=
        closeV_closed_scoped hδ.closed_right (by have := hv.scopedIn; rwa [hδ.length_right])
      refine compatK_case (vrelK_fund hv n δ₁ δ₂ hδ) hscv₁ hscv₂ ?_ ?_
      · intro m hm u₁ u₂ hcu₁ hcu₂ hu
        rw [closeC_subst_comm hδ.closed_left hcu₁, closeC_subst_comm hδ.closed_right hcu₂]
        have hδ' : EnvRelK m (A :: Γ) (u₁ :: δ₁) (u₂ :: δ₂) := by
          rw [EnvRelK]; exact ⟨hcu₁, hcu₂, hu, EnvRelK_mono (Nat.le_of_lt hm) hδ⟩
        exact crelK_fund hN₁ m (u₁ :: δ₁) (u₂ :: δ₂) hδ'
      · intro m hm u₁ u₂ hcu₁ hcu₂ hu
        rw [closeC_subst_comm hδ.closed_left hcu₁, closeC_subst_comm hδ.closed_right hcu₂]
        have hδ' : EnvRelK m (B :: Γ) (u₁ :: δ₁) (u₂ :: δ₂) := by
          rw [EnvRelK]; exact ⟨hcu₁, hcu₂, hu, EnvRelK_mono (Nat.le_of_lt hm) hδ⟩
        exact crelK_fund hN₂ m (u₁ :: δ₁) (u₂ :: δ₂) hδ'
  | @split _ _ _ _ v N φ q A B C hv hN _ =>
      intro n δ₁ δ₂ hδ
      rw [closeC_split, closeC_split]
      have hscv₁ : Val.Closed (closeV δ₁ v) :=
        closeV_closed_scoped hδ.closed_left (by have := hv.scopedIn; rwa [hδ.length_left])
      have hscv₂ : Val.Closed (closeV δ₂ v) :=
        closeV_closed_scoped hδ.closed_right (by have := hv.scopedIn; rwa [hδ.length_right])
      refine compatK_split (vrelK_fund hv n δ₁ δ₂ hδ) hscv₁ hscv₂ ?_
      intro m hm a₁ a₂ b₁ b₂ hca₁ hca₂ hcb₁ hcb₂ ha hb
      rw [closeC_subst2_comm hδ.closed_left hca₁ hcb₁, closeC_subst2_comm hδ.closed_right hca₂ hcb₂]
      have hδ' : EnvRelK m (B :: A :: Γ) (b₁ :: a₁ :: δ₁) (b₂ :: a₂ :: δ₂) := by
        rw [EnvRelK]; refine ⟨hcb₁, hcb₂, hb, ?_⟩; rw [EnvRelK]
        exact ⟨hca₁, hca₂, ha, EnvRelK_mono (Nat.le_of_lt hm) hδ⟩
      have := crelK_fund hN m (b₁ :: a₁ :: δ₁) (b₂ :: a₂ :: δ₂) hδ'
      rwa [show closeC (b₁ :: a₁ :: δ₁) N = closeC δ₁ (Comp.subst a₁ (Comp.subst b₁ N)) from rfl,
           show closeC (b₂ :: a₂ :: δ₂) N = closeC δ₂ (Comp.subst a₂ (Comp.subst b₂ N)) from rfl] at this
  | @unfold _ _ v A hv =>
      intro n δ₁ δ₂ hδ
      rw [closeC_unfold, closeC_unfold]
      cases hv with
      | @fold _ _ a _ ha =>
          rw [closeV_fold, closeV_fold]
          have hsa₁ : Val.Closed (closeV δ₁ a) :=
            closeV_closed_scoped hδ.closed_left (by have := ha.scopedIn; rwa [hδ.length_left])
          have hsa₂ : Val.Closed (closeV δ₂ a) :=
            closeV_closed_scoped hδ.closed_right (by have := ha.scopedIn; rwa [hδ.length_right])
          refine CrelK_head_step (c₁' := Comp.ret (closeV δ₁ a)) (c₂' := Comp.ret (closeV δ₂ a))
            ⟨fun _ _ => rfl, by intro u; simp⟩ ⟨fun _ _ => rfl, by intro u; simp⟩ ?_
          intro m hm
          rw [CrelK]; intro g D K₁ K₂ hK
          exact crelK_ret g D K₁ K₂ hK hsa₁ hsa₂ (vrelK_fund ha m δ₁ δ₂ (EnvRelK_mono (le_of_lt hm) hδ))
      | @vvar _ i _ hget =>
          have hsc₁ : Val.Closed (closeV δ₁ (Val.vvar i)) :=
            closeV_closed_scoped hδ.closed_left (by
              have := (HasVTy.vvar hget).scopedIn; rwa [hδ.length_left])
          have hsc₂ : Val.Closed (closeV δ₂ (Val.vvar i)) :=
            closeV_closed_scoped hδ.closed_right (by
              have := (HasVTy.vvar hget).scopedIn; rwa [hδ.length_right])
          exact crelK_unfold hsc₁ hsc₂ (vrelK_fund (HasVTy.vvar hget) n δ₁ δ₂ hδ)
  | @perform _ _ _ c ℓ op v φ q A B hcap _hℓ hArg hRes hv =>
      -- ◊4.5b-append: the op-PRODUCER, now a THIN call to `crelK_fund_up` (extracted outside the mutual
      -- block so its match stays small enough for structural-recursion inference). `hvk` precomputed via
      -- `vrelK_fund hv` (the only mutual recursion); the rest is self-contained in `crelK_fund_up`.
      -- ADR-0054: the cap argument `c : cap ℓ` closes to a LITERAL `vcap mid ℓ` (VrelK at cap forces the
      -- same id both sides — `vrelK_fund hcap`), so the closed redex is `perform (vcap mid ℓ) op …`, the
      -- exact shape `crelK_fund_up` consumes.
      intro n δ₁ δ₂ hδ
      rw [closeC_perform, closeC_perform]
      have hck : VrelK n (VTy.cap ℓ) (closeV δ₁ c) (closeV δ₂ c) := vrelK_fund hcap n δ₁ δ₂ hδ
      rw [VrelK] at hck
      obtain ⟨mid, hc1, hc2⟩ := hck
      rw [hc1, hc2]
      have hvk : VrelK n A (closeV δ₁ v) (closeV δ₂ v) := vrelK_fund hv n δ₁ δ₂ hδ
      have hcv₁ : Val.Closed (closeV δ₁ v) :=
        closeV_closed_scoped hδ.closed_left (by have := hv.scopedIn; rwa [hδ.length_left])
      have hcv₂ : Val.Closed (closeV δ₂ v) :=
        closeV_closed_scoped hδ.closed_right (by have := hv.scopedIn; rwa [hδ.length_right])
      exact crelK_fund_up hArg hRes hcv₁ hcv₂ hvk
  | @handleThrows _ _ ℓ M e φ q qc A hArg _hIface hM _hsub _hBocc =>
      -- ◊4.5b sub-block (f): handler row-discharge over `CrelK`. throws is ▷-free (zero-shot abort, no
      -- resume). ADR-0054/0055: `handle` BINDS the capability — `closeC_handleThrows` rewrites to
      -- `handle (throws ℓ) (closeCUnderBinders 1 δ M)` (body under ONE binder, var 0 = the cap). So the
      -- `compatK_handleThrows` premise is CAP-QUANTIFIED `∀ gid, CrelK … (subst (vcap gid ℓ) …)`, supplied
      -- by the IH `crelK_fund hM` on the env EXTENDED by `vcap gid ℓ` at the cap binder (PARALLEL `lam`,
      -- bridged by `closeC_subst_comm`). The env-shift wall (ADR-0050) is dissolved: caps are absolute.
      intro n δ₁ δ₂ hδ
      rw [closeC_handleThrows, closeC_handleThrows]
      refine compatK_handleThrows (e := e) hArg (fun gid => ?_)
      have hclosed : Val.Closed (Val.vcap gid ℓ) := fun k => rfl
      rw [closeC_subst_comm hδ.closed_left hclosed, closeC_subst_comm hδ.closed_right hclosed]
      have hδ' : EnvRelK n (VTy.cap ℓ :: Γ) (Val.vcap gid ℓ :: δ₁) (Val.vcap gid ℓ :: δ₂) := by
        rw [EnvRelK]
        exact ⟨hclosed, hclosed,
          (show VrelK n (VTy.cap ℓ) (Val.vcap gid ℓ) (Val.vcap gid ℓ) by
            rw [VrelK]; exact ⟨gid, rfl, rfl⟩), hδ⟩
      have := crelK_fund hM n (Val.vcap gid ℓ :: δ₁) (Val.vcap gid ℓ :: δ₂) hδ'
      rwa [show closeC (Val.vcap gid ℓ :: δ₁) M = closeC δ₁ (Comp.subst (Val.vcap gid ℓ) M) from rfl,
           show closeC (Val.vcap gid ℓ :: δ₂) M = closeC δ₂ (Comp.subst (Val.vcap gid ℓ) M) from rfl]
        at this
  | @handleState _ _ ℓ s₀ M e φ q qc S A _hga hgr hp hpr _hrestrict hs hM _hsub _hBocc =>
      -- ◊4.5b-append: state-resume closes via `compatK_handleState` (→ `krelS_state_reinstall`, the
      -- resumptive heart). The stored state `s₀` is CLOSED (`HasVTy [] []`, so `closeV δᵢ s₀ = s₀`); its
      -- self-relation `VrelK k S s₀ s₀` comes from `vrelK_fund hs`. ADR-0054/0055: cap-binding premise via
      -- the `vcap gid ℓ`-EXTENDED env (parallel `lam`, bridged by `closeC_subst_comm`).
      intro n δ₁ δ₂ hδ
      rw [closeC_handleState, closeC_handleState]
      have hcs₀ : Val.Closed s₀ := fun k => hs.shift_closed k (Nat.zero_le k)
      rw [closeV_closed hcs₀, closeV_closed hcs₀]
      have hsv : ∀ k, VrelK k S s₀ s₀ := fun k => by
        have := vrelK_fund hs k [] [] (EnvRelK_nil_iff k [] [] |>.mpr ⟨rfl, rfl⟩)
        rwa [closeV_closed hcs₀] at this
      have hrestrict' : ∀ op s', Bang.handlesOp (Handler.state ℓ s') ℓ op = true → op = "get" ∨ op = "put" :=
        fun op s' hc => by
          simp only [handlesOp, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc
          rcases hc.2 with rfl | rfl <;> simp
      refine compatK_handleState (e := e) hgr hp hpr hrestrict' hcs₀ hsv (fun gid => ?_)
      have hclosed : Val.Closed (Val.vcap gid ℓ) := fun k => rfl
      rw [closeC_subst_comm hδ.closed_left hclosed, closeC_subst_comm hδ.closed_right hclosed]
      have hδ' : EnvRelK n (VTy.cap ℓ :: Γ) (Val.vcap gid ℓ :: δ₁) (Val.vcap gid ℓ :: δ₂) := by
        rw [EnvRelK]
        exact ⟨hclosed, hclosed,
          (show VrelK n (VTy.cap ℓ) (Val.vcap gid ℓ) (Val.vcap gid ℓ) by
            rw [VrelK]; exact ⟨gid, rfl, rfl⟩), hδ⟩
      have := crelK_fund hM n (Val.vcap gid ℓ :: δ₁) (Val.vcap gid ℓ :: δ₂) hδ'
      rwa [show closeC (Val.vcap gid ℓ :: δ₁) M = closeC δ₁ (Comp.subst (Val.vcap gid ℓ) M) from rfl,
           show closeC (Val.vcap gid ℓ :: δ₂) M = closeC δ₂ (Comp.subst (Val.vcap gid ℓ) M) from rfl]
        at this
  | @handleTransaction _ _ ℓ Θ₀ M e φ q qc A hnewA hnewR hreadA hreadR hwriteA hwriteR _hrestrict hcells hM _hsub _hBocc =>
      -- ◊4.5b-append: transaction-resume via `compatK_handleTransaction` (→ `krelS_transaction_reinstall`).
      -- `HeapRel n Θ₀ Θ₀` from `hcells` via `heapRel_self_of_cells_int` (NO `vrelK_fund` — int is base).
      -- ADR-0054/0055: cap-binding premise via the `vcap gid ℓ`-EXTENDED env (parallel `lam`).
      intro n δ₁ δ₂ hδ
      rw [closeC_handleTransaction, closeC_handleTransaction]
      have hrestrict' : ∀ op Θ', Bang.handlesOp (Handler.transaction ℓ Θ') ℓ op = true →
          op = "newTVar" ∨ op = "readTVar" ∨ op = "writeTVar" := fun op Θ' hc => by
        simp only [handlesOp, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc; tauto
      have hheap : HeapRel Eff Mult n Θ₀ Θ₀ := heapRel_self_of_cells_int n Θ₀ hcells
      refine compatK_handleTransaction (e := e) hnewA hnewR hreadA hreadR hwriteA hwriteR hrestrict' hheap
        (fun gid => ?_)
      have hclosed : Val.Closed (Val.vcap gid ℓ) := fun k => rfl
      rw [closeC_subst_comm hδ.closed_left hclosed, closeC_subst_comm hδ.closed_right hclosed]
      have hδ' : EnvRelK n (VTy.cap ℓ :: Γ) (Val.vcap gid ℓ :: δ₁) (Val.vcap gid ℓ :: δ₂) := by
        rw [EnvRelK]
        exact ⟨hclosed, hclosed,
          (show VrelK n (VTy.cap ℓ) (Val.vcap gid ℓ) (Val.vcap gid ℓ) by
            rw [VrelK]; exact ⟨gid, rfl, rfl⟩), hδ⟩
      have := crelK_fund hM n (Val.vcap gid ℓ :: δ₁) (Val.vcap gid ℓ :: δ₂) hδ'
      rwa [show closeC (Val.vcap gid ℓ :: δ₁) M = closeC δ₁ (Comp.subst (Val.vcap gid ℓ) M) from rfl,
           show closeC (Val.vcap gid ℓ :: δ₂) M = closeC δ₂ (Comp.subst (Val.vcap gid ℓ) M) from rfl]
        at this
end


/-! ### B.6′ ◊4.5b — `krelS_refl` (the answer-typed `lr_sound` capstone)

A well-typed stack is `KrelS`-self-related at answer type `Co` (the whole-program returner type, the
`D` parameter). Induction over `HasStack`: nil = `krelS_nil_succ`; letF/appF reuse the frame intros +
`crelK_fund`/`vrelK_fund` for the continuation/arg self-relation; the handler arms reuse the closed
`crelK_fund` handler cases (ADR-0053 5→2 — no handler-arm sorry here). -/
theorem krelS_refl {n : Nat} {C : Stack} {e eo : Eff} {B Co : CTy Eff Mult} {qo : Mult}
    {Ao : VTy Eff Mult} {g : Nat} (hCo : Co = CTy.F qo Ao)
    (hC : HasStack C e B eo Co) : KrelS n B Co e g C C := by
  induction hC with
  | @nil e' C' =>
      -- `B = C' = Co = F qo Ao` (`hCo`): the returner empty stack is `krelS_nil_succ`.
      subst hCo; exact krelS_nil_succ n _ _ _ _
  | @letF K N e₁ e₂ eo q qk A B Co hN hK ihK =>
      -- HasStack.letF: tail `K` at the JOINED row `e₁⊔e₂` (ihK), continuation `N` at `e₂`, frame hole
      -- at `e₁`. Build the letF-extended `KrelS` at the joined row `e₁⊔e₂` (continuation row e₂ ≤ e₁⊔e₂),
      -- then WEAKEN the whole frame down to the goal's hole row `e₁` (`e₁ ≤ e₁⊔e₂`, antitone). The frame
      -- body self-relates the continuation `N` via `crelK_fund` (▷-guarded, ∀ m < n).
      have hframe : KrelS n (CTy.F q A) Co (e₁ ⊔ e₂) g (Frame.letF N :: K) (Frame.letF N :: K) := by
        refine krelS_letF_intro (φ := e₂) le_sup_right ?_ (ihK hCo)
        intro m _hm v₁ v₂ hcv₁ hcv₂ hv
        have hδ' : EnvRelK m [A] [v₁] [v₂] := by
          rw [EnvRelK]; exact ⟨hcv₁, hcv₂, hv, EnvRelK_nil_iff m [] [] |>.mpr ⟨rfl, rfl⟩⟩
        have := crelK_fund hN m [v₁] [v₂] hδ'
        rwa [show closeC [v₁] N = Comp.subst v₁ N from rfl,
             show closeC [v₂] N = Comp.subst v₂ N from rfl] at this
      exact KrelS_eff_anti le_sup_left hframe
  | @appF K v e eo q A B Co hv hK ihK =>
      have hcv : Val.Closed v := fun k => hv.shift_closed k (Nat.zero_le k)
      have hvr : VrelK n A v v := by
        have := vrelK_fund hv n [] [] (EnvRelK_nil_iff n [] [] |>.mpr ⟨rfl, rfl⟩)
        rwa [closeV_closed hcv] at this
      exact krelS_appF_intro hcv hcv hvr (ihK hCo)
  | @handleF K nh ℓ e φ eo q A Co hArg hIface hsub _hBocc hK ihK =>
      -- ◊4.5b sub-block f: the handler-frame self-relation = the ROW-DISCHARGE. `krelS_handleF` reduces the
      -- goal `KrelS …e (handleF::K)` to `KrelS …e K`; the IH gives the tail at the DISCHARGED row `φ`
      -- (`HasStack.handleF`: `K` is typed at `φ`, the frame at `e ≤ ℓ⊔φ`). `KrelS_eff_cast` bridges
      -- `φ → e` with no ordering — the SINGLE-ROW `KrelS` expresses the discharge (no two-row needed)
      -- because ε is inert in the answer-typed core (no `Srel` stuck-half gates on it). [decision: single-row]
      -- ◊4.5b sub-block f: the self-relation makes EQUAL handlers (same `h` both sides) ⇒ `h = h` by `rfl`.
      -- THROWS resume supply: dispatch aborts to `(K, ret w)` (ANY op, zero-shot) — `crelK_ret` on the
      -- self-related tail `ihK` closes it (the `hVrel` premise at `C = F q A` gives `VrelK m A w`).
      -- ◊4.5b-append: throws self-relation. HandlerRel n (throws ℓ) (throws ℓ) = (ℓ=ℓ) = rfl. The
      -- Kᵢ-threading resume conjunct: dispatch aborts to (K, ret w) (zero-shot, Kᵢ discarded) — `crelK_ret`
      -- on the self-related tail `ihK` closes it (the hVrel premise at C = F q A gives VrelK m A w).
      rw [krelS_handleF]
      refine ⟨rfl, by simp only [HandlerRel], KrelS_eff_cast (ihK hCo), ?_⟩
      intro m hm op w₁ w₂ Cᵢ εᵢ Kᵢ Kᵢ' cfg₁ cfg₂ hcatch hcw₁ hcw₂ hVrel _hKi _hCᵢ hd₁ hd₂
      have hop : op = "raise" := by
        simp only [Handler.label, handlesOp, Bool.and_eq_true, beq_iff_eq] at hcatch; exact hcatch.2
      subst hop
      have hw : VrelK m A w₁ w₂ := hVrel A (by rw [Handler.label]; exact hArg)
      simp only [dispatchOn] at hd₁ hd₂
      obtain rfl := (Option.some.injEq _ _).mp hd₁.symm
      obtain rfl := (Option.some.injEq _ _).mp hd₂.symm
      -- ◊4.5b-strengthen: SUPPLY the decomposition — throws aborts to `(K, ret w)`, `w₁~w₂` at `A`, the
      -- self-related tail `K~K` at returner hole `F q A` (the discharged-row, downward-closed).
      exact ⟨q, A, w₁, w₂, K, K, φ, rfl, rfl, hcw₁, hcw₂, hw,
        KrelS_mono (le_of_lt hm) (KrelS_eff_cast (ihK hCo))⟩
  | @stateF K nh ℓ s e φ eo q A S Co hg hgr hp hpr hIface hcs hsub _hBocc hK ihK =>
      -- ◊4.5b-append: the state-frame self-relation IS `krelS_state_reinstall` at `s = s` (the same stored
      -- state both sides). The tail self-relates via `ihK` (cast `φ → e`); the interface + state typing come
      -- from the `stateF` binder. `hcs : HasVTy [] [] s S` ⇒ closed + `VrelK k S s s` (`vrelK_fund`).
      have hcss : Val.Closed s := fun k => hcs.shift_closed k (Nat.zero_le k)
      have hsv : ∀ k, VrelK k S s s := fun k => by
        have := vrelK_fund hcs k [] [] (EnvRelK_nil_iff k [] [] |>.mpr ⟨rfl, rfl⟩)
        rwa [closeV_closed hcss] at this
      have hrestrict' : ∀ op s', Bang.handlesOp (Handler.state ℓ s') ℓ op = true → op = "get" ∨ op = "put" :=
        fun op s' hc => by
          simp only [handlesOp, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc
          rcases hc.2 with rfl | rfl <;> simp
      exact krelS_state_reinstall hgr hp hpr hrestrict' nh n s s hcss hcss (hsv n) K K
        (KrelS_eff_cast (ihK hCo))
  | @transactionF K nh ℓ Θ e φ eo q A Co hnewA hnewR hreadA hreadR hwriteA hwriteR _ hcells hsub _hBocc hK ihK =>
      -- ◊4.5b-append: transaction-frame self-relation IS `krelS_transaction_reinstall` at Θ=Θ; tail via
      -- `ihK` (cast φ→e); heap self-relation `HeapRel n Θ Θ` from `hcells` (all cells closed int).
      have hrestrict' : ∀ op Θ', Bang.handlesOp (Handler.transaction ℓ Θ') ℓ op = true →
          op = "newTVar" ∨ op = "readTVar" ∨ op = "writeTVar" := fun op Θ' hc => by
        simp only [handlesOp, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc; tauto
      exact krelS_transaction_reinstall hnewA hnewR hreadA hreadR hwriteA hwriteR hrestrict' nh n Θ Θ
        (heapRel_self_of_cells_int n Θ hcells) K K (KrelS_eff_cast (ihK hCo))

end -- public section
end Bang
