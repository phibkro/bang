/-
  Compat.lean — the Phase-B target list.
  `lr_fundamental` (Spec.lean) = induction over the typing derivation, one case
  per rule, each discharged by the matching lemma below. Proving all of these
  (in PROOF_ORDER) IS proving the fundamental theorem.

  STATUS (Phase A part 1, 2026-06-21):
    Stubbed — the previous content used Ctx/VTy/CTy as 0-arg types, but Phase A
    part 1 made them (Eff Mult)-parametrized. The compat lemmas need:
      (a) explicit Eff/Mult threading in every signature
      (b) the ADR-0019 two-context shape: GradeVec γ (Finsupp +/•) + TyCtx Γ
      (c) `U`, `F`, `ret`, etc. accessed as constructors (e.g. VTy.U, CTy.F, Comp.ret)
      (d) helpers like `var`, `unit`, `lamC`, `forceC`, `bindC`, `opC`, `handleC`,
          `HandlerRelated` to be either dropped (subsumed by Spec.lean's concrete
          Comp constructors) or restated as helpers atop the concrete syntax.
    Phase A part 2 will repopulate this file once Ctx arithmetic + the typing
    judgments are concrete in Spec.lean.

  Source map (preserved for the rewrite):
    - 10 standard CBPV lemmas: compat_var, compat_unit, compat_thunk,
      compat_force, compat_ret, compat_bind, compat_lam, compat_app
    - 3 effect lemmas (Biernacki Lemmas 5–7, with `lift`/ρ DROPPED for set-rows):
      compat_op, (NO compat_lift — deliberate), compat_handle [KEY]
    - 3 graded structural lemmas: compat_sub_eff, compat_weaken, compat_split

  Risk: all [STD]/recipe EXCEPT `compat_handle`, which is [KEY] — it is the heart
  of the effect side and where `Srel` (the 𝒮 half of `Krel`) is actually used.
  Prove `compat_handle` LAST per PROOF_ORDER.
-/
-- Compat is a proof module UPSTREAM of Spec (sibling to Metatheory): Spec wires its frozen
-- `lr_fundamental`/`lr_sound` statements to the proofs assembled here (`:= lr_fundamental_proof`,
-- exactly as `preservation := preservation_proof`). So we import the DEFINITION layers, not Spec
-- (importing Spec would cycle once Spec imports Compat). Verified no cycle: Metatheory imports only
-- Core/Syntax/Operational; LR adds the relations; neither imports Spec.
import Bang.Core
import Bang.Syntax
import Bang.Operational
import Bang.LR
import Bang.Metatheory

namespace Bang

open Bang.EffectRow (Label)

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
    (hne : ∀ v, cfg ≠ ([], Comp.ret v)) :
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

/-- `Converges`-level form: if `c` takes a context-independent head step to `c'` under stack `K`
(`step (K, c) = some (K, c')`), and `K ≠ []` OR `c` is not a bare `ret`, then plugging `K` with `c`
converges iff plugging with `c'` does. Bridges through `converges_plug_iff`. -/
theorem converges_plug_step (K : Stack) (c c' : Comp)
    (hstep : Source.step (K, c) = some (K, c'))
    (hne : ∀ v, (K, c) ≠ ([], Comp.ret v)) :
    Converges (Stack.plug K c) ↔ Converges (Stack.plug K c') := by
  rw [Stack.plug, Stack.plug, converges_plug_iff, converges_plug_iff]
  exact converges_cfg_step (K, c) (K, c') hstep hne

/-- A *context-independent head step*: `c ↦ c'` fires under EVERY stack, and `c` is never a bare
returned focus (`ret v` would be terminal, not a redex). The non-PUSH reductions
(`force (vthunk M) ↦ M`, the ADT eliminators) have this shape: they rewrite the focus in place
without consulting the stack. -/
def CIStep (c c' : Comp) : Prop :=
  (∀ K : Stack, Source.step (K, c) = some (K, c')) ∧ (∀ v, c ≠ Comp.ret v)

/-- Head-expansion of `Crel`: a context-independent head step on BOTH sides reduces `Crel` to the
relation on the reducts. The `▷`-free direction (same index `n`), because the step is a machine
β/ι-reduction, not an effect crossing a `▷`. -/
theorem Crel_head_step {n : Nat} {B : CTy Eff Mult} {e : Eff} {c₁ c₁' c₂ c₂' : Comp}
    (h₁ : CIStep c₁ c₁') (h₂ : CIStep c₂ c₂') :
    Crel n B e c₁' c₂' → Crel n B e c₁ c₂ := by
  intro hrel
  unfold Crel at hrel ⊢
  intro K₁ K₂ hK hconv
  -- forward: plug K₁ c₁ converges ⇒ (anti-red) plug K₁ c₁' converges ⇒ (hrel) plug K₂ c₂' ⇒
  -- (anti-red, reverse) plug K₂ c₂ converges.
  have e1 : Converges (Stack.plug K₁ c₁) ↔ Converges (Stack.plug K₁ c₁') :=
    converges_plug_step K₁ c₁ c₁' (h₁.1 K₁) (by intro v; simp [h₁.2 v])
  have e2 : Converges (Stack.plug K₂ c₂) ↔ Converges (Stack.plug K₂ c₂') :=
    converges_plug_step K₂ c₂ c₂' (h₂.1 K₂) (by intro v; simp [h₂.2 v])
  exact e2.mpr (hrel K₁ K₂ hK (e1.mp hconv))


/-- The `letF` REDUCE bridge: plugging `letF N :: K` with `ret v` co-converges with plugging `K` with
`N.subst v`. The step `(letF N :: K, ret v) ↦ (K, N.subst v)` is context-dependent (it consumes the
`letF` frame), so this is NOT a `CIStep` — proven directly through `converges_cfg_step`. The frame
`letF N :: K` is never `([], ret _)` (it has a head frame), so the no-terminal side-condition holds. -/
theorem converges_letF_ret (K : Stack) (N : Comp) (v : Val) :
    Converges (Stack.plug (Frame.letF N :: K) (Comp.ret v)) ↔ Converges (Stack.plug K (Comp.subst v N)) := by
  rw [Stack.plug, Stack.plug, converges_plug_iff, converges_plug_iff]
  exact converges_cfg_step (Frame.letF N :: K, Comp.ret v) (K, Comp.subst v N)
    rfl (by intro u; simp)

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

@[simp] theorem closeC_up (δ : List Val) (ℓ : Label) (op : OpId) (w : Val) :
    closeC δ (Comp.up ℓ op w) = Comp.up ℓ op (closeV δ w) := by
  induction δ generalizing w with
  | nil => rfl
  | cons v δ ih => simp only [closeC, closeV, Comp.subst, Comp.substFrom]; exact ih _

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
mutual
theorem Val.shiftFrom_substFrom_closed {u : Val} (hu : Val.Closed u) :
    ∀ (k i : Nat), i ≤ k → ∀ (t : Val),
      Val.shiftFrom k (Val.substFrom i u t) = Val.substFrom i u (Val.shiftFrom (k + 1) t)
  | _, _, _,    .vunit => rfl
  | _, _, _,    .vint _ => rfl
  | k, i, hik,  .vvar j => by
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
  | k, i, hik,  .vthunk M => by
      simp only [Val.shiftFrom, Val.substFrom]
      rw [Comp.shiftFrom_substFrom_closed hu k i hik M]
  | k, i, hik,  .inl w => by
      simp only [Val.shiftFrom, Val.substFrom]; rw [Val.shiftFrom_substFrom_closed hu k i hik w]
  | k, i, hik,  .inr w => by
      simp only [Val.shiftFrom, Val.substFrom]; rw [Val.shiftFrom_substFrom_closed hu k i hik w]
  | k, i, hik,  .pair a b => by
      simp only [Val.shiftFrom, Val.substFrom]
      rw [Val.shiftFrom_substFrom_closed hu k i hik a, Val.shiftFrom_substFrom_closed hu k i hik b]
  | k, i, hik,  .fold w => by
      simp only [Val.shiftFrom, Val.substFrom]; rw [Val.shiftFrom_substFrom_closed hu k i hik w]

theorem Comp.shiftFrom_substFrom_closed {u : Val} (hu : Val.Closed u) :
    ∀ (k i : Nat), i ≤ k → ∀ (t : Comp),
      Comp.shiftFrom k (Comp.substFrom i u t) = Comp.substFrom i u (Comp.shiftFrom (k + 1) t)
  | k, i, hik, .ret w => by
      simp only [Comp.shiftFrom, Comp.substFrom]; rw [Val.shiftFrom_substFrom_closed hu k i hik w]
  | k, i, hik, .letC M N => by
      simp only [Comp.shiftFrom, Comp.substFrom, hu.shift]
      rw [Comp.shiftFrom_substFrom_closed hu k i hik M,
        Comp.shiftFrom_substFrom_closed hu (k + 1) (i + 1) (by omega) N]
  | k, i, hik, .force w => by
      simp only [Comp.shiftFrom, Comp.substFrom]; rw [Val.shiftFrom_substFrom_closed hu k i hik w]
  | k, i, hik, .lam M => by
      simp only [Comp.shiftFrom, Comp.substFrom, hu.shift]
      rw [Comp.shiftFrom_substFrom_closed hu (k + 1) (i + 1) (by omega) M]
  | k, i, hik, .app M w => by
      simp only [Comp.shiftFrom, Comp.substFrom]
      rw [Comp.shiftFrom_substFrom_closed hu k i hik M, Val.shiftFrom_substFrom_closed hu k i hik w]
  | k, i, hik, .up ℓ op w => by
      simp only [Comp.shiftFrom, Comp.substFrom]; rw [Val.shiftFrom_substFrom_closed hu k i hik w]
  | k, i, hik, .handle h M => by
      simp only [Comp.shiftFrom, Comp.substFrom]
      rw [Handler.shiftFrom_substFrom_closed hu k i hik h, Comp.shiftFrom_substFrom_closed hu k i hik M]
  | k, i, hik, .case w N₁ N₂ => by
      simp only [Comp.shiftFrom, Comp.substFrom, hu.shift]
      rw [Val.shiftFrom_substFrom_closed hu k i hik w,
        Comp.shiftFrom_substFrom_closed hu (k + 1) (i + 1) (by omega) N₁,
        Comp.shiftFrom_substFrom_closed hu (k + 1) (i + 1) (by omega) N₂]
  | k, i, hik, .split w N => by
      simp only [Comp.shiftFrom, Comp.substFrom, hu.shift]
      rw [Val.shiftFrom_substFrom_closed hu k i hik w,
        Comp.shiftFrom_substFrom_closed hu (k + 2) (i + 2) (by omega) N]
  | k, i, hik, .unfold w => by
      simp only [Comp.shiftFrom, Comp.substFrom]; rw [Val.shiftFrom_substFrom_closed hu k i hik w]
  | _, _, _, .oom => rfl
  | _, _, _, .wrong _ => rfl

theorem Handler.shiftFrom_substFrom_closed {u : Val} (hu : Val.Closed u) :
    ∀ (k i : Nat), i ≤ k → ∀ (h : Handler),
      Handler.shiftFrom k (Handler.substFrom i u h) = Handler.substFrom i u (Handler.shiftFrom (k + 1) h)
  | k, i, hik, .state ℓ s => by
      simp only [Handler.shiftFrom, Handler.substFrom]; rw [Val.shiftFrom_substFrom_closed hu k i hik s]
  | _, _, _, .throws _ => rfl
  | _, _, _, .transaction _ _ => rfl
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

/-- Closing a value SCOPED IN `δ.length` over a CLOSED environment yields a CLOSED value: the fold
substitutes each free index with a closed filler, dropping the scope by 1 each step to `ScopedIn 0` =
`Closed`. The `ret`/`case`/`split`/`vthunk` closedness obligations of the fundamental theorem. -/
theorem closeV_closed_scoped : ∀ {δ : List Val} {v : Val},
    (∀ u ∈ δ, Val.Closed u) → Val.ScopedIn δ.length v → Val.Closed (closeV δ v)
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
mutual
theorem Val.substFrom_swap_closed {v w : Val} (hv : Val.Closed v) (hw : Val.Closed w) :
    ∀ (k : Nat) (t : Val),
      Val.substFrom k w (Val.substFrom (k + 1) v t) = Val.substFrom k v (Val.substFrom k w t)
  | _, .vunit => rfl
  | _, .vint _ => rfl
  | k, .vvar i => by
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
  | k, .vthunk M => by
      simp only [Val.substFrom]; rw [Comp.substFrom_swap_closed hv hw k M]
  | k, .inl u => by simp only [Val.substFrom]; rw [Val.substFrom_swap_closed hv hw k u]
  | k, .inr u => by simp only [Val.substFrom]; rw [Val.substFrom_swap_closed hv hw k u]
  | k, .pair u₁ u₂ => by
      simp only [Val.substFrom]
      rw [Val.substFrom_swap_closed hv hw k u₁, Val.substFrom_swap_closed hv hw k u₂]
  | k, .fold u => by simp only [Val.substFrom]; rw [Val.substFrom_swap_closed hv hw k u]

theorem Comp.substFrom_swap_closed {v w : Val} (hv : Val.Closed v) (hw : Val.Closed w) :
    ∀ (k : Nat) (t : Comp),
      Comp.substFrom k w (Comp.substFrom (k + 1) v t) = Comp.substFrom k v (Comp.substFrom k w t)
  | k, .ret u => by simp only [Comp.substFrom]; rw [Val.substFrom_swap_closed hv hw k u]
  | k, .letC M N => by
      simp only [Comp.substFrom, hv.shift, hw.shift]
      rw [Comp.substFrom_swap_closed hv hw k M, Comp.substFrom_swap_closed hv hw (k + 1) N]
  | k, .force u => by simp only [Comp.substFrom]; rw [Val.substFrom_swap_closed hv hw k u]
  | k, .lam M => by
      simp only [Comp.substFrom, hv.shift, hw.shift]
      rw [Comp.substFrom_swap_closed hv hw (k + 1) M]
  | k, .app M u => by
      simp only [Comp.substFrom]
      rw [Comp.substFrom_swap_closed hv hw k M, Val.substFrom_swap_closed hv hw k u]
  | k, .up ℓ op u => by simp only [Comp.substFrom]; rw [Val.substFrom_swap_closed hv hw k u]
  | k, .handle h M => by
      simp only [Comp.substFrom]
      rw [Handler.substFrom_swap_closed hv hw k h, Comp.substFrom_swap_closed hv hw k M]
  | k, .case u N₁ N₂ => by
      simp only [Comp.substFrom, hv.shift, hw.shift]
      rw [Val.substFrom_swap_closed hv hw k u,
        Comp.substFrom_swap_closed hv hw (k + 1) N₁, Comp.substFrom_swap_closed hv hw (k + 1) N₂]
  | k, .split u N => by
      simp only [Comp.substFrom, hv.shift, hw.shift]
      rw [Val.substFrom_swap_closed hv hw k u, Comp.substFrom_swap_closed hv hw (k + 2) N]
  | k, .unfold u => by simp only [Comp.substFrom]; rw [Val.substFrom_swap_closed hv hw k u]
  | _, .oom => rfl
  | _, .wrong _ => rfl

theorem Handler.substFrom_swap_closed {v w : Val} (hv : Val.Closed v) (hw : Val.Closed w) :
    ∀ (k : Nat) (h : Handler),
      Handler.substFrom k w (Handler.substFrom (k + 1) v h) = Handler.substFrom k v (Handler.substFrom k w h)
  | k, .state ℓ s => by simp only [Handler.substFrom]; rw [Val.substFrom_swap_closed hv hw k s]
  | _, .throws _ => rfl
  | _, .transaction _ _ => rfl
end

/-! ### B.1d The substitution-descent crux (`closeC_subst_comm`)

The lemma every BINDER case of `lr_fundamental` consumes: closing a body UNDER one binder and then
filling the binder with `w` equals substituting `w` first and then closing. For a CLOSED environment the
binder-side weakening `shiftN 1` vanishes (`shiftN_closed`), so `closeCUnderBinders 1 δ` substitutes the
SAME fillers as `closeC δ` but at level 1; the level-0 `Comp.subst w` then commutes past each via
`Comp.substFrom_swap_closed` (both fillers closed).

  shape: biernacki-popl18 §5.2 fundamental theorem — closing substitution `G⟦Γ⟧` commutes with the
         single binder-substitution introduced by `letC`/`lam`/`case`/`split` β-reduction. -/
theorem closeC_subst_comm {δ : List Val} (hδ : ∀ v ∈ δ, Val.Closed v) {w : Val} (hw : Val.Closed w)
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
    -- subst w (substFrom 1 v N) = subst v (subst w N), i.e. the k=0 swap (closed v, w).
    exact Comp.substFrom_swap_closed hv hw 0 N
/-! ## B.2 The return / value-injection compat core (`crel_ret`)

`Crel`-relatedness of `ret v₁` and `ret v₂` follows from `Vrel`-relatedness of `v₁,v₂`: a
`Krel`-related stack pair, by its RETURN half, co-converges when plugged with `Vrel`-related returns.
This is the biorthogonal "values inject into computations" closure (Biernacki Fig 7, the `F q A`
clause of `Krel`). It is the `compat_ret` core and the engine of every `▷`-free leaf. -/

theorem crel_ret {n : Nat} {q : Mult} {A : VTy Eff Mult} {e : Eff} {v₁ v₂ : Val}
    (hc₁ : Val.Closed v₁) (hc₂ : Val.Closed v₂)
    (hv : Vrel n A v₁ v₂) : Crel n (CTy.F q A) e (Comp.ret v₁) (Comp.ret v₂) := by
  unfold Crel
  intro K₁ K₂ hK
  unfold Krel at hK
  -- the RETURN half of Krel fires on `Vrel n A v₁ v₂` (at closed values) at the returner type `F q A`.
  exact hK.1 q A rfl v₁ v₂ hc₁ hc₂ hv


/-! ## B.3 Head-reduction compat cores (`force` / ADT eliminators)

Each of these formers takes a context-independent head step (the focus rewrites in place without
consulting the stack), so `Crel_head_step` reduces the goal to `Crel` on the reduct. The `Vrel`
hypothesis on the scrutinee value supplies the reduct's shape (a thunk for `force`, a tag for
`case`, a pair for `split`, a `fold` for `unfold`). -/

/-- `force` of `Vrel`-related thunks: `Vrel (U φ B)` unfolds to `Crel B φ` on the forced bodies, and
`force (vthunk c) ↦ c` is a CIStep. -/
theorem crel_force {n : Nat} {φ : Eff} {B : CTy Eff Mult} {w₁ w₂ : Val}
    (hv : Vrel n (VTy.U φ B) w₁ w₂) : Crel n B φ (Comp.force w₁) (Comp.force w₂) := by
  -- Vrel at U φ B: w₁ = vthunk c₁, w₂ = vthunk c₂, Crel n B φ c₁ c₂.
  rw [Vrel] at hv
  obtain ⟨c₁, c₂, rfl, rfl, hc⟩ := hv
  refine Crel_head_step (c₁' := c₁) (c₂' := c₂) ?_ ?_ hc
  · exact ⟨fun K => rfl, by intro v; simp⟩
  · exact ⟨fun K => rfl, by intro v; simp⟩

/-! ## B.3b The `letF` frame-extension `Krel` lemma (the `letC` congruence engine)

`compat_letC` proves `Crel n B (φ₁⊔φ₂) (letC M₁ N₁') (letC M₂ N₂')` by running `M` under the extended
stack `letF N' :: K`: `plug Kᵢ (letC Mᵢ Nᵢ') = plug (letF Nᵢ' :: Kᵢ) Mᵢ` (definitional refocus,
`plug_cons`), so the IH for `M` (`Crel n (F q1 A) φ₁ M₁ M₂`) fires once the extended stacks are shown
`Krel`-related at `(F q1 A, φ₁)`. THAT is `krel_letF`:

  • RETURN half: a returned value `v` triggers the `letF` REDUCE (`converges_letF_ret`) to `Nᵢ'.subst v`,
    related by the continuation hypothesis `hN` (the IH for `N`); the ambient `Krel n B (φ₁⊔φ₂)` weakens
    to `Krel n B φ₂` (`Krel_eff_anti`, φ₂ ≤ φ₁⊔φ₂) to discharge the resulting `Crel n B φ₂`.
  • STUCK half: an `Srel`-pair under `letF Nᵢ' :: Kᵢ` is an UNHANDLED `up` (`splitAt = none` is in the
    `Srel` premise), so `plug (letF Nᵢ' :: K₁) c₁` never converges (`not_converges_up_splitNone`) and
    `CoApprox` is vacuously true. The resume clause of `Srel` is not consumed — the frame never resumes
    an op it does not handle.

  shape: biernacki-popl18 §5 evaluation-context congruence (the `let` frame case of the fundamental
         theorem); benton-hur-icfp09 biorthogonal frame extension. -/
theorem krel_letF {n : Nat} {q1 : Mult} {A : VTy Eff Mult} {B : CTy Eff Mult} {φ₁ φ₂ : Eff}
    {N₁' N₂' : Comp} {K₁ K₂ : Stack}
    (hK : Krel (n + 1) B (φ₁ ⊔ φ₂) K₁ K₂)
    (hN : ∀ v₁ v₂, Val.Closed v₁ → Val.Closed v₂ → Vrel (n + 1) A v₁ v₂ →
      Crel (n + 1) B φ₂ (Comp.subst v₁ N₁') (Comp.subst v₂ N₂')) :
    Krel (n + 1) (CTy.F q1 A) φ₁ (Frame.letF N₁' :: K₁) (Frame.letF N₂' :: K₂) := by
  rw [Krel]
  refine ⟨?_, ?_⟩
  · -- RETURN half: F q1 A = F q A' ⟹ q = q1, A' = A; the letF frame reduces to the continuation.
    intro q A' hEq v₁ v₂ hc₁ hc₂ hv
    rw [CTy.F.injEq] at hEq
    obtain ⟨rfl, rfl⟩ := hEq
    intro hconv₁
    -- plug (letF N₁' :: K₁) (ret v₁) converges ⟹ plug K₁ (N₁'.subst v₁) converges.
    rw [converges_letF_ret] at hconv₁
    rw [converges_letF_ret]
    -- the continuation is Crel (n+1) B φ₂; weaken the ambient Krel to φ₂ and apply.
    have hKφ₂ : Krel (n + 1) B φ₂ K₁ K₂ := Krel_eff_anti (n + 1) B φ₂ (φ₁ ⊔ φ₂) K₁ K₂ le_sup_right hK
    have hCrel := hN v₁ v₂ hc₁ hc₂ hv
    rw [Crel] at hCrel
    exact hCrel K₁ K₂ hKφ₂ hconv₁
  · -- STUCK half: the Srel pair is an unhandled op under letF :: K — never converges, CoApprox vacuous.
    intro c₁ c₂ hS
    rw [Srel] at hS
    obtain ⟨ℓ, op, v₁, v₂, _, _, hc₁, _, _, _, _, _, hsp₁, _, _⟩ := hS
    intro hconv₁
    rw [hc₁] at hconv₁
    exact absurd hconv₁ (not_converges_up_splitNone (Frame.letF N₁' :: K₁) ℓ op v₁ hsp₁)

/-- The `letC` compatibility core (`compat_letC`): a `Crel` for `M` (the bound computation, at its
returner type `F q1 A` and effect `φ₁`) plus a continuation relation `hN` (the IH for `N`: for every
closed `Vrel`-related bound value, the substituted continuations are `Crel`-related at `(B, φ₂)`) give
`Crel` for the whole `letC` at the joined effect `φ₁ ⊔ φ₂`. The engine is the definitional REFOCUS
`plug K (letC M N') = plug (letF N' :: K) M` (`plug_cons`), turning the goal into running `M` under the
`letF`-extended stacks, which `krel_letF` shows `Krel`-related at `(F q1 A, φ₁)`. The fundamental
induction supplies `hN` via `closeC_subst_comm` + `closeC_letC` (`Nᵢ'.subst v = closeC δᵢ (N.subst v)`
= the IH instance `closeC (v::δᵢ) N`). At `n = 0`, `crel_zero` (any pair related). -/
theorem compat_letC {n : Nat} {q1 : Mult} {A : VTy Eff Mult} {B : CTy Eff Mult} {φ₁ φ₂ : Eff}
    {M₁ M₂ N₁' N₂' : Comp}
    (hM : Crel n (CTy.F q1 A) φ₁ M₁ M₂)
    (hN : ∀ v₁ v₂, Val.Closed v₁ → Val.Closed v₂ → Vrel n A v₁ v₂ →
      Crel n B φ₂ (Comp.subst v₁ N₁') (Comp.subst v₂ N₂')) :
    Crel n B (φ₁ ⊔ φ₂) (Comp.letC M₁ N₁') (Comp.letC M₂ N₂') := by
  cases n with
  | zero => exact crel_zero B (φ₁ ⊔ φ₂) (Comp.letC M₁ N₁') (Comp.letC M₂ N₂')
  | succ m =>
      rw [Crel]
      intro K₁ K₂ hK
      -- REFOCUS: plug Kᵢ (letC Mᵢ Nᵢ') = plug (letF Nᵢ' :: Kᵢ) Mᵢ.
      have hrefocus₁ : Stack.plug K₁ (Comp.letC M₁ N₁') = Stack.plug (Frame.letF N₁' :: K₁) M₁ := by
        rw [Stack.plug, Stack.plug, plug_cons]; rfl
      have hrefocus₂ : Stack.plug K₂ (Comp.letC M₂ N₂') = Stack.plug (Frame.letF N₂' :: K₂) M₂ := by
        rw [Stack.plug, Stack.plug, plug_cons]; rfl
      rw [hrefocus₁, hrefocus₂]
      -- the letF-extended stacks are Krel-related at (F q1 A, φ₁); run M through them.
      have hKletF := krel_letF (q1 := q1) hK hN
      rw [Crel] at hM
      exact hM (Frame.letF N₁' :: K₁) (Frame.letF N₂' :: K₂) hKletF

/-- The `case` compatibility core (`compat_case`): `Vrel`-related sum scrutinees force both `case`s to
the SAME branch (both `inl` or both `inr`, with `Vrel`-related payloads), and `case (inl v) … ↦ N₁[v]`
is a CIStep (stack-independent in-place reduction). So `Crel_head_step` reduces to the chosen branch's
continuation relation on the substituted payload. Scrutinee closedness (from the closed environment in
the fundamental induction) supplies the payload-closedness the branch IH needs. -/
theorem compat_case {n : Nat} {A B : VTy Eff Mult} {C : CTy Eff Mult} {φ : Eff}
    {w₁ w₂ : Val} {N₁₁ N₂₁ N₁₂ N₂₂ : Comp}
    (hw : Vrel n (VTy.sum A B) w₁ w₂) (hcw₁ : Val.Closed w₁) (hcw₂ : Val.Closed w₂)
    (hN₁ : ∀ v₁ v₂, Val.Closed v₁ → Val.Closed v₂ → Vrel n A v₁ v₂ →
      Crel n C φ (Comp.subst v₁ N₁₁) (Comp.subst v₂ N₁₂))
    (hN₂ : ∀ v₁ v₂, Val.Closed v₁ → Val.Closed v₂ → Vrel n B v₁ v₂ →
      Crel n C φ (Comp.subst v₁ N₂₁) (Comp.subst v₂ N₂₂)) :
    Crel n C φ (Comp.case w₁ N₁₁ N₂₁) (Comp.case w₂ N₁₂ N₂₂) := by
  rw [Vrel] at hw
  rcases hw with ⟨u₁, u₂, rfl, rfl, hu⟩ | ⟨u₁, u₂, rfl, rfl, hu⟩
  · -- both inl: reduce to the left branch, related by hN₁ on the (closed) payloads.
    refine Crel_head_step (c₁' := Comp.subst u₁ N₁₁) (c₂' := Comp.subst u₂ N₁₂) ?_ ?_ ?_
    · exact ⟨fun K => rfl, by intro v; simp⟩
    · exact ⟨fun K => rfl, by intro v; simp⟩
    · exact hN₁ u₁ u₂ hcw₁.inl_inv hcw₂.inl_inv hu
  · -- both inr: reduce to the right branch, related by hN₂.
    refine Crel_head_step (c₁' := Comp.subst u₁ N₂₁) (c₂' := Comp.subst u₂ N₂₂) ?_ ?_ ?_
    · exact ⟨fun K => rfl, by intro v; simp⟩
    · exact ⟨fun K => rfl, by intro v; simp⟩
    · exact hN₂ u₁ u₂ hcw₁.inr_inv hcw₂.inr_inv hu

/-- The `split` compatibility core (`compat_split`): a `Vrel`-related product scrutinee gives both
`split`s a `pair` with `Vrel`-related components, and `split (pair v w) N ↦ N[fst][shift snd]` is a
CIStep. The continuation relation `hN` (the two-binder IH, at `B :: A :: Γ`) is applied at the reduct's
exact substitution shape `Comp.subst v (Comp.subst (Val.shift w) N)`. Component closedness comes from the
closed scrutinee. -/
theorem compat_split {n : Nat} {A B : VTy Eff Mult} {C : CTy Eff Mult} {φ : Eff}
    {w₁ w₂ : Val} {N₁' N₂' : Comp}
    (hw : Vrel n (VTy.prod A B) w₁ w₂) (hcw₁ : Val.Closed w₁) (hcw₂ : Val.Closed w₂)
    (hN : ∀ a₁ a₂ b₁ b₂, Val.Closed a₁ → Val.Closed a₂ → Val.Closed b₁ → Val.Closed b₂ →
      Vrel n A a₁ a₂ → Vrel n B b₁ b₂ →
      Crel n C φ (Comp.subst a₁ (Comp.subst (Val.shift b₁) N₁'))
                 (Comp.subst a₂ (Comp.subst (Val.shift b₂) N₂'))) :
    Crel n C φ (Comp.split w₁ N₁') (Comp.split w₂ N₂') := by
  rw [Vrel] at hw
  obtain ⟨a₁, a₂, b₁, b₂, rfl, rfl, ha, hb⟩ := hw
  obtain ⟨hca₁, hcb₁⟩ := hcw₁.pair_inv
  obtain ⟨hca₂, hcb₂⟩ := hcw₂.pair_inv
  refine Crel_head_step
    (c₁' := Comp.subst a₁ (Comp.subst (Val.shift b₁) N₁'))
    (c₂' := Comp.subst a₂ (Comp.subst (Val.shift b₂) N₂')) ?_ ?_ ?_
  · exact ⟨fun K => rfl, by intro v; simp⟩
  · exact ⟨fun K => rfl, by intro v; simp⟩
  · exact hN a₁ a₂ b₁ b₂ hca₁ hca₂ hcb₁ hcb₂ ha hb

/-- `unfold` of `Vrel`-related folds: `unfold (fold w) ↦ ret w` is a CIStep, so the goal reduces to
`crel_ret` on the payloads. INDEX SUBTLETY (documented blocker): `Vrel (n+1) (mu A)` gives the
payloads related at the UNROLLED type but at index `n` (the `▷` guard, LR.lean §5.2), whereas
`Crel (n+1) (F 1 _) (ret u₁) (ret u₂)` consumes a `Krel (n+1)` whose return-half inspects
`Vrel (n+1)`. Bridging needs Vrel/Krel step-index MONOTONICITY (downward-closure): `Krel (n+1)`'s
return obligation, restricted to the reduct that only ever observes the value at index ≤ n, holds
from `Vrel n`. The monotonicity lemmas (`Vrel_mono`, `Krel_mono`, standard ahmed-esop06
downward-closure by induction on the lex measure) are the missing primitive — sequenced after the
clean cases. -/
theorem crel_unfold {n : Nat} {A : VTy Eff Mult} {e : Eff} {w₁ w₂ : Val}
    (hv : Vrel (n + 1) (VTy.mu A) w₁ w₂) :
    Crel (n + 1) (CTy.F 1 (VTy.unrollMu A)) e (Comp.unfold w₁) (Comp.unfold w₂) := by
  rw [Vrel] at hv
  obtain ⟨u₁, u₂, rfl, rfl, hu⟩ := hv
  refine Crel_head_step (c₁' := Comp.ret u₁) (c₂' := Comp.ret u₂) ?_ ?_ ?_
  · exact ⟨fun K => rfl, by intro v; simp⟩
  · exact ⟨fun K => rfl, by intro v; simp⟩
  · -- BLOCKER: needs `Vrel (n+1) (unrollMu A) u₁ u₂`; have `Vrel n …` (the μ ▷-guard drop).
    -- Resolved by Vrel/Krel downward-closure monotonicity (TODO — see docstring).
    sorry


/-! ## B.4 `krel_refl` — the interface contract for `lr_sound` (the capstone)

The downstream `lr_sound` capstone (separate thread) closes as `lr_sound_closed ∘ krel_refl`: the
biorthogonal adequacy (LR.lean §5.3) instantiates `Crel`'s `∀ K₁ K₂, Krel … → CoApprox` at a
self-pair `(C, C)` known to be `Krel`-self-related, yielding the `⊑` clause for observation context
`C`. `krel_refl` is that "identity extension" (Biernacki/Pitts) — a well-typed stack is `Krel`-related
to ITSELF. It is the IDENTITY INSTANCE of `lr_fundamental` (the context's sub-computations
self-related, `c₁ = c₂`), so it falls out of the SAME induction; surfaced here as a NAMED lemma so the
capstone composes cleanly rather than re-extracting from `lr_fundamental`'s internals.

PREMISE: the stack is well-typed — `HasStack C e B eo Co` carries a focus of type `(e, B)` to the
whole-program type `(eo, Co)`. The typing is load-bearing in the STUCK half: a stack must eventually
handle-or-escape every operation it does not catch (the `Srel` clause's `splitAt = none` operations
tunnel out), which only a typed stack guarantees.

STATUS (gated on the two U6 blockers — see `crel_unfold` docstring + the lead handoff):
  - the OPEN/CLOSED statement-shape decision (the `letF N :: K` case substitutes `N[v]`, needing the
    `EnvRel`/`closeC` env-closure for the continuation's self-relation under its binder);
  - the μ/▷ index alignment (a `letF`-bound continuation returning at a μ-type hits the same
    off-by-one).
Both resolve `krel_refl` mechanically; the named contract is fixed NOW so the capstone thread can
reference it. -/
/-- A well-typed value is `ScopedIn Γ.length` (`HasVTy.shift_closed`: shifting at a cutoff `≥ Γ.length`
is the identity). The bridge from the typing derivation to the syntactic scope bound that
`closeV_closed_scoped` consumes. -/
theorem HasVTy.scopedIn {γ : GradeVec Mult} {Γ : TyCtx Eff Mult} {v : Val} {A : VTy Eff Mult}
    (h : HasVTy γ Γ v A) : Val.ScopedIn Γ.length v := fun k hk => h.shift_closed k hk


theorem krel_refl {n : Nat} {C : Stack} {e eo : Eff} {B Co : CTy Eff Mult}
    (_hC : HasStack C e B eo Co) : Krel n B e C C := by
  -- IDENTITY INSTANCE of the fundamental theorem: induct on `HasStack C …`, mirroring the
  -- `lr_fundamental` HasCTy induction (each frame's stored sub-computation related to itself via the
  -- matching compat core). The `nil` case is `krel_nil_succ` (LR.lean) at successor indices; the
  -- frame cases (`letF`/`appF`/`handleF`/`stateF`/`transactionF`) extend a `Krel`-related stack by
  -- one frame, using the sub-computation's self-relation. BLOCKED identically to `lr_fundamental`
  -- (statement-shape for the `letF` continuation's binder; μ/▷ for μ-typed returns). Contract fixed;
  -- body lands with the fundamental theorem.
  sorry


/-! ## B.5 The mutual fundamental theorem (`vrel_fund` / `crel_fund`)

The capstone: a well-typed value/computation relates to ITSELF under every pair of `Vrel`-related
closing environments. Proven by mutual induction over the typing derivation (`HasCTy.rec` with both
motives, mirroring `Metatheory.HasCTy.subst_gen`), each case dispatching to its compat core:

  value side (`vrel_fund`):  vunit/vint (BaseRel), vvar (`closeV_vvar` + `EnvRel.vrel_at`),
                             vthunk (→ `crel_fund` IH), inl/inr/pair/fold (structural).
  comp side  (`crel_fund`):  ret (→ `crel_ret` + `vrel_fund` + `closeV_closed_scoped`),
                             letC (→ `compat_letC`, the IHs through `closeC_letC`/`closeC_subst_comm`),
                             force (→ `crel_force` + `vrel_fund`), case (→ `compat_case`),
                             split (→ `compat_split`); unfold (→ `crel_unfold`, μ Blocker 2 sorry);
                             lam/app (arrow-clause sorry, decision #2 pending);
                             up/handle* (Srel/handler, PROOF_ORDER-last sorry).

STATUS: PARTIAL — NOT closed. The sorried cases (lam, app, unfold, up, handleThrows/State/Transaction)
are documented blockers; `lr_fundamental` carries `sorryAx` until all close. -/

mutual
theorem vrel_fund {γ : GradeVec Mult} {Γ : TyCtx Eff Mult} {v : Val} {A : VTy Eff Mult}
    (h : HasVTy γ Γ v A) :
    ∀ (n : Nat) (δ₁ δ₂ : List Val), EnvRel n Γ δ₁ δ₂ →
      Vrel n A (closeV δ₁ v) (closeV δ₂ v) := by
  cases h with
  | vunit => intro n δ₁ δ₂ _; rw [closeV_vunit, closeV_vunit, Vrel]; exact ⟨rfl, rfl⟩
  | vint  => intro n δ₁ δ₂ _; rw [closeV_vint, closeV_vint, Vrel]; exact ⟨_, rfl, rfl⟩
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
      rw [closeV_vthunk, closeV_vthunk, Vrel]
      exact ⟨closeC δ₁ M, closeC δ₂ M, rfl, rfl, crel_fund hM n δ₁ δ₂ hδ⟩
  | @inl _ _ w A B hw =>
      intro n δ₁ δ₂ hδ
      rw [closeV_inl, closeV_inl, Vrel]
      exact Or.inl ⟨_, _, rfl, rfl, vrel_fund hw n δ₁ δ₂ hδ⟩
  | @inr _ _ w A B hw =>
      intro n δ₁ δ₂ hδ
      rw [closeV_inr, closeV_inr, Vrel]
      exact Or.inr ⟨_, _, rfl, rfl, vrel_fund hw n δ₁ δ₂ hδ⟩
  | @pair _ _ _ _ a b A B ha hb _ =>
      intro n δ₁ δ₂ hδ
      rw [closeV_pair, closeV_pair, Vrel]
      exact ⟨_, _, _, _, rfl, rfl, vrel_fund ha n δ₁ δ₂ hδ, vrel_fund hb n δ₁ δ₂ hδ⟩
  | @fold _ _ w A hw =>
      intro n δ₁ δ₂ hδ
      -- fold at μ: Vrel (n+1) (mu A) needs payload at unrolled type, index n (the ▷ guard); the
      -- recursive call gives Vrel n (unrollMu A) at the SAME n. BLOCKER (shared with crel_unfold,
      -- Blocker 2): the μ ▷ step-index drop / downward-closure. Documented sorry.
      sorry

theorem crel_fund {γ : GradeVec Mult} {Γ : TyCtx Eff Mult} {c : Comp} {e : Eff} {B : CTy Eff Mult}
    (h : HasCTy γ Γ c e B) :
    ∀ (n : Nat) (δ₁ δ₂ : List Val), EnvRel n Γ δ₁ δ₂ →
      Crel n B e (closeC δ₁ c) (closeC δ₂ c) := by
  cases h with
  | @ret _ _ _ v A q hv _ =>
      intro n δ₁ δ₂ hδ
      rw [closeC_ret, closeC_ret]
      have hsc₁ : Val.Closed (closeV δ₁ v) :=
        closeV_closed_scoped hδ.closed_left (by have := hv.scopedIn; rwa [hδ.length_left])
      have hsc₂ : Val.Closed (closeV δ₂ v) :=
        closeV_closed_scoped hδ.closed_right (by have := hv.scopedIn; rwa [hδ.length_right])
      exact crel_ret hsc₁ hsc₂ (vrel_fund hv n δ₁ δ₂ hδ)
  | @letC _ _ _ _ M N φ₁ φ₂ q1 q2 A B hM hN _ =>
      intro n δ₁ δ₂ hδ
      rw [closeC_letC, closeC_letC]
      refine compat_letC (q1 := q1) (crel_fund hM n δ₁ δ₂ hδ) ?_
      -- continuation: (closeCUnderBinders 1 δᵢ N).subst v = closeC δᵢ (N.subst v) = closeC (v::δᵢ) N
      -- (closeC_subst_comm); the extended EnvRel uses the closed Vrel-related bound value v.
      intro v₁ v₂ hcv₁ hcv₂ hvrel
      rw [closeC_subst_comm hδ.closed_left hcv₁, closeC_subst_comm hδ.closed_right hcv₂]
      have hδ' : EnvRel n (A :: Γ) (v₁ :: δ₁) (v₂ :: δ₂) := by
        rw [EnvRel]; exact ⟨hcv₁, hcv₂, hvrel, hδ⟩
      have := crel_fund hN n (v₁ :: δ₁) (v₂ :: δ₂) hδ'
      rwa [show closeC (v₁ :: δ₁) N = closeC δ₁ (Comp.subst v₁ N) from rfl,
           show closeC (v₂ :: δ₂) N = closeC δ₂ (Comp.subst v₂ N) from rfl] at this
  | @force _ _ v φ B hv =>
      intro n δ₁ δ₂ hδ
      rw [closeC_force, closeC_force]
      exact crel_force (vrel_fund hv n δ₁ δ₂ hδ)
  | @lam _ _ M φ q A B hM =>
      -- BLOCKER (decision #2, Krel arrow clause pending): Crel at arr q A B requires the
      -- arrow-observation clause; lam is the arrow normal-form. Documented sorry.
      intro n δ₁ δ₂ hδ; sorry
  | @app _ _ _ _ M v φ q A B hM hv _ =>
      -- BLOCKER (decision #2): app observes M at arr q A B under the appF frame — same arrow gap.
      intro n δ₁ δ₂ hδ; sorry
  | @case _ _ _ _ v N₁ N₂ φ q A B C hv hN₁ hN₂ _ =>
      intro n δ₁ δ₂ hδ
      rw [closeC_case, closeC_case]
      have hscv₁ : Val.Closed (closeV δ₁ v) :=
        closeV_closed_scoped hδ.closed_left (by have := hv.scopedIn; rwa [hδ.length_left])
      have hscv₂ : Val.Closed (closeV δ₂ v) :=
        closeV_closed_scoped hδ.closed_right (by have := hv.scopedIn; rwa [hδ.length_right])
      refine compat_case (vrel_fund hv n δ₁ δ₂ hδ) hscv₁ hscv₂ ?_ ?_
      · intro u₁ u₂ hcu₁ hcu₂ hu
        rw [closeC_subst_comm hδ.closed_left hcu₁, closeC_subst_comm hδ.closed_right hcu₂]
        have hδ' : EnvRel n (A :: Γ) (u₁ :: δ₁) (u₂ :: δ₂) := by rw [EnvRel]; exact ⟨hcu₁, hcu₂, hu, hδ⟩
        exact crel_fund hN₁ n (u₁ :: δ₁) (u₂ :: δ₂) hδ'
      · intro u₁ u₂ hcu₁ hcu₂ hu
        rw [closeC_subst_comm hδ.closed_left hcu₁, closeC_subst_comm hδ.closed_right hcu₂]
        have hδ' : EnvRel n (B :: Γ) (u₁ :: δ₁) (u₂ :: δ₂) := by rw [EnvRel]; exact ⟨hcu₁, hcu₂, hu, hδ⟩
        exact crel_fund hN₂ n (u₁ :: δ₁) (u₂ :: δ₂) hδ'
  | @split _ _ _ _ v N φ q A B C hv hN _ =>
      -- split binds TWO (B :: A :: Γ); the continuation needs the two-binder closeC commutation
      -- (closeCUnderBinders 2 vs the reduct's subst v (subst (shift w) N)) — the d=2 analogue of
      -- closeC_subst_comm, not yet built. Documented sorry (the d=2 substitution-descent gap).
      intro n δ₁ δ₂ hδ; sorry
  | @unfold _ _ v A hv =>
      -- unfold: reduces to crel_unfold, which carries the μ ▷ Blocker 2 sorry. Same blocker.
      intro n δ₁ δ₂ hδ; sorry
  | @up _ _ ℓ op v φ q A B hℓ hArg hRes hv =>
      -- BLOCKER (PROOF_ORDER-last): up is the Srel control-stuck term; compat_up's handled case
      -- (splitAt ≠ none) couples into compat_handle. Documented sorry.
      intro n δ₁ δ₂ hδ; sorry
  | @handleThrows _ _ ℓ M e φ q A hArg hIface hM hsub =>
      intro n δ₁ δ₂ hδ; sorry   -- BLOCKER (PROOF_ORDER-last): compat_handle [KEY], Srel resumption.
  | @handleState _ _ ℓ s₀ M e φ q S A _ _ _ _ _ hs hM hsub =>
      intro n δ₁ δ₂ hδ; sorry   -- BLOCKER (PROOF_ORDER-last): compat_handle, resumptive state.
  | @handleTransaction _ _ ℓ Θ₀ M e φ q A _ _ _ _ _ _ _ hcells hM hsub =>
      intro n δ₁ δ₂ hδ; sorry   -- BLOCKER (PROOF_ORDER-last): compat_handle, transaction.
end

end Bang
