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

/-- The `letF` REDUCE bridge: plugging `letF N :: K` with `ret v` co-converges with plugging `K` with
`N.subst v`. The step `(letF N :: K, ret v) ↦ (K, N.subst v)` is context-dependent (it consumes the
`letF` frame), so this is NOT a `CIStep` — proven directly through `converges_cfg_step`. The frame
`letF N :: K` is never `([], ret _)` (it has a head frame), so the no-terminal side-condition holds. -/
theorem converges_letF_ret (K : Stack) (N : Comp) (v : Val) :
    Converges (Stack.plug (Frame.letF N :: K) (Comp.ret v)) ↔ Converges (Stack.plug K (Comp.subst v N)) := by
  rw [Stack.plug, Stack.plug, converges_plug_iff, converges_plug_iff]
  exact converges_cfg_step (Frame.letF N :: K, Comp.ret v) (K, Comp.subst v N)
    rfl (by intro u; simp)

/-- The `appF` REDUCE bridge: plugging `appF w :: K` with `lam M` co-converges with plugging `K` with
`M.subst w`. The step `(appF w :: K, lam M) ↦ (K, M.subst w)` (β) consumes the `appF` frame — the
`lam`-elimination analogue of `converges_letF_ret`. -/
theorem converges_appF_lam (K : Stack) (w : Val) (M : Comp) :
    Converges (Stack.plug (Frame.appF w :: K) (Comp.lam M)) ↔ Converges (Stack.plug K (Comp.subst w M)) := by
  rw [Stack.plug, Stack.plug, converges_plug_iff, converges_plug_iff]
  exact converges_cfg_step (Frame.appF w :: K, Comp.lam M) (K, Comp.subst w M)
    rfl (by intro u; simp)

/-- The `handleF` RETURN bridge: a handler frame's return clause is the IDENTITY (ADR-0023 Q6) —
`handleF h :: K, ret v ↦ K, ret v` — so plugging the handler frame with a returned value co-converges
with plugging the bare stack. Holds for ANY handler `h` (throws/state/transaction all share the
identity return). -/
theorem converges_handleF_ret (K : Stack) (h : Handler) (v : Val) :
    Converges (Stack.plug (Frame.handleF h :: K) (Comp.ret v)) ↔ Converges (Stack.plug K (Comp.ret v)) := by
  rw [Stack.plug, Stack.plug, converges_plug_iff, converges_plug_iff]
  exact converges_cfg_step (Frame.handleF h :: K, Comp.ret v) (K, Comp.ret v)
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

@[simp] theorem closeC_unfold (δ : List Val) (w : Val) :
    closeC δ (Comp.unfold w) = Comp.unfold (closeV δ w) := by
  induction δ generalizing w with
  | nil => rfl
  | cons v δ ih => simp only [closeC, closeV, Comp.subst, Comp.substFrom]; exact ih _

/-- `closeC` distributes through a `throws` handler: the handler carries no value
(`Handler.subst _ (throws ℓ) = throws ℓ`), and `handle` does not bind, so the body closes structurally.
(`state`/`transaction` carry values/heaps — their closeC is the resumptive-fragment follow-up.) -/
@[simp] theorem closeC_handleThrows (δ : List Val) (ℓ : Label) (M : Comp) :
    closeC δ (Comp.handle (Handler.throws ℓ) M) = Comp.handle (Handler.throws ℓ) (closeC δ M) := by
  induction δ generalizing M with
  | nil => rfl
  | cons v δ ih => simp only [closeC, Comp.subst, Comp.substFrom, Handler.substFrom]; exact ih _

/-- ◊4.5 RESUME INFRA: `closeC` distributes through a `state ℓ s` handler. UNLIKE `throws`, the `state`
handler CARRIES a value `s` (`Handler.substFrom k v (state ℓ s) = state ℓ (substFrom k v s)`), so the
stored value closes too — `closeC δ (handle (state ℓ s) M) = handle (state ℓ (closeV δ s)) (closeC δ M)`.
The `handle` former does not bind, so both `s` and the body `M` close at level 0 (structural). -/
@[simp] theorem closeC_handleState (δ : List Val) (ℓ : Label) (s : Val) (M : Comp) :
    closeC δ (Comp.handle (Handler.state ℓ s) M)
      = Comp.handle (Handler.state ℓ (closeV δ s)) (closeC δ M) := by
  induction δ generalizing s M with
  | nil => rfl
  | cons v δ ih => simp only [closeC, closeV, Comp.subst, Comp.substFrom, Handler.substFrom]; exact ih _ _

/-- ◊4.5 RESUME INFRA: `closeC` distributes through a `transaction ℓ Θ` handler. The heap cells are
treated as CLOSED (ADR-0030: `Handler.substFrom _ (transaction ℓ Θ) = transaction ℓ Θ`, identity), so
the heap is untouched — exactly like `throws`. Only the body `M` closes:
`closeC δ (handle (transaction ℓ Θ) M) = handle (transaction ℓ Θ) (closeC δ M)`. -/
@[simp] theorem closeC_handleTransaction (δ : List Val) (ℓ : Label) (Θ : Store) (M : Comp) :
    closeC δ (Comp.handle (Handler.transaction ℓ Θ) M)
      = Comp.handle (Handler.transaction ℓ Θ) (closeC δ M) := by
  induction δ generalizing M with
  | nil => rfl
  | cons v δ ih => simp only [closeC, Comp.subst, Comp.substFrom, Handler.substFrom]; exact ih _

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

/-! ### B.1c′ NON-ADJACENT substitution-swap (for the d=2 `split` descent)

`closeC_subst2_comm` (the `split` case) fills two level-0 binders through `closeCUnderBinders 2`, which
after the first descent leaves the two substitutions at NON-adjacent levels (0 and `d+1`). The adjacent
swap above (`i, i+1`) doesn't reach it, so here is the general `i ≤ j` form, both fillers CLOSED:
  `substFrom i w (substFrom (j+1) u t) = substFrom j u (substFrom i w t)`.
The adjacent lemma is the `i = j` instance; this generalizes the cutoff gap. Mutual structural
induction; the binder cases step BOTH cutoffs (`i+1 ≤ j+1`). -/
mutual
theorem Val.substFrom_swap_closed_ge {u w : Val} (hu : Val.Closed u) (hw : Val.Closed w) :
    ∀ (i j : Nat), i ≤ j → ∀ (t : Val),
      Val.substFrom i w (Val.substFrom (j + 1) u t) = Val.substFrom j u (Val.substFrom i w t)
  | _, _, _,   .vunit => rfl
  | _, _, _,   .vint _ => rfl
  | i, j, hij, .vvar m => by
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
  | i, j, hij, .vthunk M => by
      simp only [Val.substFrom]; rw [Comp.substFrom_swap_closed_ge hu hw i j hij M]
  | i, j, hij, .inl t => by simp only [Val.substFrom]; rw [Val.substFrom_swap_closed_ge hu hw i j hij t]
  | i, j, hij, .inr t => by simp only [Val.substFrom]; rw [Val.substFrom_swap_closed_ge hu hw i j hij t]
  | i, j, hij, .pair a b => by
      simp only [Val.substFrom]
      rw [Val.substFrom_swap_closed_ge hu hw i j hij a, Val.substFrom_swap_closed_ge hu hw i j hij b]
  | i, j, hij, .fold t => by simp only [Val.substFrom]; rw [Val.substFrom_swap_closed_ge hu hw i j hij t]

theorem Comp.substFrom_swap_closed_ge {u w : Val} (hu : Val.Closed u) (hw : Val.Closed w) :
    ∀ (i j : Nat), i ≤ j → ∀ (t : Comp),
      Comp.substFrom i w (Comp.substFrom (j + 1) u t) = Comp.substFrom j u (Comp.substFrom i w t)
  | i, j, hij, .ret t => by simp only [Comp.substFrom]; rw [Val.substFrom_swap_closed_ge hu hw i j hij t]
  | i, j, hij, .letC M N => by
      simp only [Comp.substFrom, hu.shift, hw.shift]
      rw [Comp.substFrom_swap_closed_ge hu hw i j hij M,
        Comp.substFrom_swap_closed_ge hu hw (i + 1) (j + 1) (by omega) N]
  | i, j, hij, .force t => by simp only [Comp.substFrom]; rw [Val.substFrom_swap_closed_ge hu hw i j hij t]
  | i, j, hij, .lam M => by
      simp only [Comp.substFrom, hu.shift, hw.shift]
      rw [Comp.substFrom_swap_closed_ge hu hw (i + 1) (j + 1) (by omega) M]
  | i, j, hij, .app M t => by
      simp only [Comp.substFrom]
      rw [Comp.substFrom_swap_closed_ge hu hw i j hij M, Val.substFrom_swap_closed_ge hu hw i j hij t]
  | i, j, hij, .up ℓ op t => by simp only [Comp.substFrom]; rw [Val.substFrom_swap_closed_ge hu hw i j hij t]
  | i, j, hij, .handle h M => by
      simp only [Comp.substFrom]
      rw [Handler.substFrom_swap_closed_ge hu hw i j hij h, Comp.substFrom_swap_closed_ge hu hw i j hij M]
  | i, j, hij, .case t N₁ N₂ => by
      simp only [Comp.substFrom, hu.shift, hw.shift]
      rw [Val.substFrom_swap_closed_ge hu hw i j hij t,
        Comp.substFrom_swap_closed_ge hu hw (i + 1) (j + 1) (by omega) N₁,
        Comp.substFrom_swap_closed_ge hu hw (i + 1) (j + 1) (by omega) N₂]
  | i, j, hij, .split t N => by
      simp only [Comp.substFrom, hu.shift, hw.shift]
      rw [Val.substFrom_swap_closed_ge hu hw i j hij t,
        Comp.substFrom_swap_closed_ge hu hw (i + 2) (j + 2) (by omega) N]
  | i, j, hij, .unfold t => by simp only [Comp.substFrom]; rw [Val.substFrom_swap_closed_ge hu hw i j hij t]
  | _, _, _, .oom => rfl
  | _, _, _, .wrong _ => rfl

theorem Handler.substFrom_swap_closed_ge {u w : Val} (hu : Val.Closed u) (hw : Val.Closed w) :
    ∀ (i j : Nat), i ≤ j → ∀ (h : Handler),
      Handler.substFrom i w (Handler.substFrom (j + 1) u h)
        = Handler.substFrom j u (Handler.substFrom i w h)
  | i, j, hij, .state ℓ s => by
      simp only [Handler.substFrom]; rw [Val.substFrom_swap_closed_ge hu hw i j hij s]
  | _, _, _, .throws _ => rfl
  | _, _, _, .transaction _ _ => rfl
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

/-- General level-0 descent through `closeCUnderBinders (d+1)`: filling the outermost (level-0) binder
with a CLOSED `w` commutes past the `d+1`-level fillers (closed), dropping the binder-depth by one. The
engine behind `closeC_subst_comm` (d=0) and the d=2 `split` descent. Uses the NON-adjacent swap
(`Comp.substFrom_swap_closed_ge` at `i=0, j=d`). -/
theorem closeCUnderBinders_subst0 (d : Nat) {δ : List Val} (hδ : ∀ v ∈ δ, Val.Closed v)
    {w : Val} (hw : Val.Closed w) (N : Comp) :
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
  rw [CrelK]; intro D K₁ K₂ hK hconv
  have hstep₁ : Source.step (K₁, c₁) = some (K₁, c₁') := h₁.1 K₁
  have hne₁ : ∀ v, (K₁, c₁) ≠ ([], Comp.ret v) := by intro v; simp [h₁.2 v]
  cases n with
  | zero => exact absurd hconv (not_convergesC_le_zero _)
  | succ k =>
      rw [convergesC_le_step hstep₁ hne₁] at hconv
      have hCk : CrelK k B e c₁' c₂' := hlater k (Nat.lt_succ_self k)
      rw [CrelK] at hCk
      have hKk : KrelS k B D e K₁ K₂ := KrelS_mono (Nat.le_succ k) hK
      have hstep₂ : Source.step (K₂, c₂) = some (K₂, c₂') := h₂.1 K₂
      have hne₂ : ∀ v, (K₂, c₂) ≠ ([], Comp.ret v) := by intro v; simp [h₂.2 v]
      exact converges_anti_step hstep₂ hne₂ (hCk D K₁ K₂ hKk hconv)

/-- ◊4.5b `force` of `VrelK`-related thunks. The U-clause is `∀ j < n, CrelK j` — exactly the `m < n`
reducts `CrelK_head_step` consumes (cleaner than the old `∀ j ≤ n` + `le_of_lt`). -/
theorem crelK_force {n : Nat} {φ : Eff} {B : CTy Eff Mult} {w₁ w₂ : Val}
    (hv : VrelK n (VTy.U φ B) w₁ w₂) : CrelK n B φ (Comp.force w₁) (Comp.force w₂) := by
  rw [VrelK] at hv
  obtain ⟨c₁, c₂, rfl, rfl, hc⟩ := hv
  refine CrelK_head_step (c₁' := c₁) (c₂' := c₂) ?_ ?_ (fun m hm => hc m hm)
  · exact ⟨fun K => rfl, by intro v; simp⟩
  · exact ⟨fun K => rfl, by intro v; simp⟩

/-- ◊4.5b `unfold` of `VrelK`-related μ-values. `unfold (fold u) ↦ ret u` (CIStep); the ▷-head-step
needs `CrelK m (ret u₁) (ret u₂)` at each `m < n`, from `crelK_ret` on the μ-payload. -/
theorem crelK_unfold {n : Nat} {A : VTy Eff Mult} {e : Eff} {w₁ w₂ : Val}
    (hcw₁ : Val.Closed w₁) (hcw₂ : Val.Closed w₂) (hv : VrelK n (VTy.mu A) w₁ w₂) :
    CrelK n (CTy.F 1 (VTy.unrollMu A)) e (Comp.unfold w₁) (Comp.unfold w₂) := by
  rw [VrelK] at hv
  obtain ⟨u₁, u₂, rfl, rfl, hu⟩ := hv
  refine CrelK_head_step (c₁' := Comp.ret u₁) (c₂' := Comp.ret u₂) ?_ ?_
    (fun m hm => crelK_ret hcw₁.fold_inv hcw₂.fold_inv (hu m hm))
  · exact ⟨fun K => rfl, by intro v; simp⟩
  · exact ⟨fun K => rfl, by intro v; simp⟩


/-! ### B.3′b `CrelK` frame extensions + `compat` cores (`letC`/`app`)

The answer-typed frame lemmas. `krelS_letF_intro` builds a `KrelS (F q A)` from a `▷`-guarded
continuation relation + a tail `KrelS B` — directly packing the def's letF clause (the tail weakens
from the ambient `ε` to the continuation row `φ` via `KrelS_eff_anti`, `φ ≤ ε`). `compatK_letC`/`_app`
refocus the source redex (`letC`/`app` PUSH) and run the bound computation through the extended stack. -/

/-- ◊4.5b build a letF-extended `KrelS` from a continuation relation (`▷`-guarded, `∀ m < n`) + the
ambient tail. The continuation row `φ ≤ ε`; the tail weakens `ε → φ` via `KrelS_eff_anti`. -/
theorem krelS_letF_intro {n : Nat} {q : Mult} {A : VTy Eff Mult} {B D : CTy Eff Mult} {ε φ : Eff}
    {N₁ N₂ : Comp} {K₁ K₂ : Stack} (hφε : φ ≤ ε)
    (hN : ∀ m, m < n → ∀ v₁ v₂, Val.Closed v₁ → Val.Closed v₂ → VrelK m A v₁ v₂ →
      CrelK m B φ (Comp.subst v₁ N₁) (Comp.subst v₂ N₂))
    (hK : KrelS n B D ε K₁ K₂) :
    KrelS n (CTy.F q A) D ε (Frame.letF N₁ :: K₁) (Frame.letF N₂ :: K₂) := by
  rw [krelS_letF]
  exact ⟨q, A, B, φ, rfl, hN, KrelS_eff_anti hφε hK⟩

/-- ◊4.5b the `letC` compat core at `CrelK` (the answer-typed `compat_letC`). REFOCUS
`(K, letC M N) ↦ (letF N::K, M)` (one PUSH step), then run `M` (related at `F q1 A`, row φ₁) through the
letF-extended stack, shown `KrelS`-related by `krelS_letF_intro`. The continuation `hN` is `▷`-guarded
(`∀ m < n`) at row φ₂; the block is at `φ₁ ⊔ φ₂`. -/
theorem compatK_letC {n : Nat} {q1 : Mult} {A : VTy Eff Mult} {B : CTy Eff Mult} {φ₁ φ₂ : Eff}
    {M₁ M₂ N₁' N₂' : Comp}
    (hM : CrelK n (CTy.F q1 A) φ₁ M₁ M₂)
    (hN : ∀ m, m < n → ∀ v₁ v₂, Val.Closed v₁ → Val.Closed v₂ → VrelK m A v₁ v₂ →
      CrelK m B φ₂ (Comp.subst v₁ N₁') (Comp.subst v₂ N₂')) :
    CrelK n B (φ₁ ⊔ φ₂) (Comp.letC M₁ N₁') (Comp.letC M₂ N₂') := by
  rw [CrelK]
  intro D K₁ K₂ hK
  refine coApproxC_le_reduce (cfg₁' := (Frame.letF N₁' :: K₁, M₁)) (cfg₂' := (Frame.letF N₂' :: K₂, M₂))
    rfl (by intro u; simp) rfl (by intro u; simp) ?_
  -- the letF-extended stack is `KrelS`-related at `(F q1 A, φ₁)`: tail at the block row φ₁⊔φ₂ weakens
  -- to the continuation row φ₂ (≤ φ₁⊔φ₂); `hM` (related at F q1 A, row φ₁) discharges the reduct.
  have hKletF : KrelS n (CTy.F q1 A) D (φ₁ ⊔ φ₂) (Frame.letF N₁' :: K₁) (Frame.letF N₂' :: K₂) :=
    krelS_letF_intro le_sup_right hN hK
  rw [CrelK] at hM
  -- `hM` is at row φ₁; the letF-extended stack is at φ₁⊔φ₂. Weaken the stack φ₁⊔φ₂ → φ₁ (antitone).
  exact hM D (Frame.letF N₁' :: K₁) (Frame.letF N₂' :: K₂) (KrelS_eff_anti le_sup_left hKletF)

/-- ◊4.5b build an appF-extended `KrelS` from a `VrelK`-related closed argument + the codomain tail.
The appF frame doesn't bind a continuation row, so the tail stays at the ambient `ε` (no weakening). -/
theorem krelS_appF_intro {n : Nat} {q : Mult} {A : VTy Eff Mult} {B D : CTy Eff Mult} {ε : Eff}
    {v₁ v₂ : Val} {K₁ K₂ : Stack} (hcv₁ : Val.Closed v₁) (hcv₂ : Val.Closed v₂)
    (hv : VrelK n A v₁ v₂) (hK : KrelS n B D ε K₁ K₂) :
    KrelS n (CTy.arr q A B) D ε (Frame.appF v₁ :: K₁) (Frame.appF v₂ :: K₂) := by
  rw [krelS_appF]
  exact ⟨q, A, B, rfl, hcv₁, hcv₂, hv, hK⟩

/-- ◊4.5b the `app` compat core at `CrelK` (the answer-typed `compat_app`). REFOCUS
`(K, app M v) ↦ (appF v::K, M)`, then run `M` (related at `arr q A B`) through the appF-extended
stack, shown `KrelS`-related by `krelS_appF_intro`. -/
theorem compatK_app {n : Nat} {q : Mult} {A : VTy Eff Mult} {B : CTy Eff Mult} {φ : Eff}
    {M₁ M₂ : Comp} {v₁ v₂ : Val}
    (hM : CrelK n (CTy.arr q A B) φ M₁ M₂)
    (hcv₁ : Val.Closed v₁) (hcv₂ : Val.Closed v₂) (hv : VrelK n A v₁ v₂) :
    CrelK n B φ (Comp.app M₁ v₁) (Comp.app M₂ v₂) := by
  rw [CrelK]
  intro D K₁ K₂ hK
  refine coApproxC_le_reduce (cfg₁' := (Frame.appF v₁ :: K₁, M₁)) (cfg₂' := (Frame.appF v₂ :: K₂, M₂))
    rfl (by intro u; simp) rfl (by intro u; simp) ?_
  rw [CrelK] at hM
  exact hM D (Frame.appF v₁ :: K₁) (Frame.appF v₂ :: K₂) (krelS_appF_intro hcv₁ hcv₂ hv hK)

/-- ◊4.5b the `lam` compat core at `CrelK` (the answer-typed `compat_lam`). A `lam` only β-reduces under
an `appF` frame; other stacks are STUCK on a `lam` (observation vacuous). Stack induction: appF-headed
β-reduces `(appF w::K', lam M') ↦ (K', M'.subst w)`, the body IH discharges; nil/letF are stuck on a
`lam`; handleF passes the lam through (`handleF h::K, lam M` is STUCK too — handleF only reduces a
`ret`). So only the appF case is non-vacuous. -/
theorem compatK_lam {n : Nat} {q : Mult} {A : VTy Eff Mult} {B : CTy Eff Mult} {φ : Eff}
    {M₁' M₂' : Comp}
    (hbody : ∀ w₁ w₂, Val.Closed w₁ → Val.Closed w₂ → VrelK n A w₁ w₂ →
      CrelK n B φ (Comp.subst w₁ M₁') (Comp.subst w₂ M₂')) :
    CrelK n (CTy.arr q A B) φ (Comp.lam M₁') (Comp.lam M₂') := by
  rw [CrelK]
  intro D K₁ K₂ hK
  cases K₁ with
  | nil =>
      -- nil arrow: `([], lam M)` is STUCK (lam reduces only under appF). Vacuous.
      intro hconv; exact absurd hconv (not_convergesC_le_of_stuck rfl (by intro u; simp))
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
                  refine coApproxC_le_reduce (cfg₁' := (K₁', Comp.subst w₁ M₁'))
                    (cfg₂' := (K₂', Comp.subst w₂ M₂')) rfl (by intro u; simp) rfl (by intro u; simp) ?_
                  have hb := hbody w₁ w₂ hcw₁ hcw₂ hw
                  rw [CrelK] at hb
                  exact hb D K₁' K₂' htail
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
          intro hconv; exact absurd hconv (not_convergesC_le_of_stuck rfl (by intro u; simp))

/-- ◊4.5b the `case` (sum elim) compat core at `CrelK`. `case (inl u) ↦ N₁[u]` / `case (inr u) ↦ N₂[u]`
are CISteps; the ▷-head-step needs the chosen branch related at every `m < n`, from the matching branch
IH on the `VrelK m`-related payload (the sum scrutinee gives the tag + payload). -/
theorem compatK_case {n : Nat} {A B : VTy Eff Mult} {C : CTy Eff Mult} {φ : Eff}
    {w₁ w₂ : Val} {N₁₁ N₂₁ N₁₂ N₂₂ : Comp}
    (hw : VrelK n (VTy.sum A B) w₁ w₂) (hcw₁ : Val.Closed w₁) (hcw₂ : Val.Closed w₂)
    (hN₁ : ∀ m, m < n → ∀ v₁ v₂, Val.Closed v₁ → Val.Closed v₂ → VrelK m A v₁ v₂ →
      CrelK m C φ (Comp.subst v₁ N₁₁) (Comp.subst v₂ N₁₂))
    (hN₂ : ∀ m, m < n → ∀ v₁ v₂, Val.Closed v₁ → Val.Closed v₂ → VrelK m B v₁ v₂ →
      CrelK m C φ (Comp.subst v₁ N₂₁) (Comp.subst v₂ N₂₂)) :
    CrelK n C φ (Comp.case w₁ N₁₁ N₂₁) (Comp.case w₂ N₁₂ N₂₂) := by
  rw [VrelK] at hw
  rcases hw with ⟨u₁, u₂, rfl, rfl, hu⟩ | ⟨u₁, u₂, rfl, rfl, hu⟩
  · refine CrelK_head_step (c₁' := Comp.subst u₁ N₁₁) (c₂' := Comp.subst u₂ N₁₂) ?_ ?_
      (fun m hm => hN₁ m hm u₁ u₂ hcw₁.inl_inv hcw₂.inl_inv (VrelK_mono (le_of_lt hm) hu))
    · exact ⟨fun K => rfl, by intro v; simp⟩
    · exact ⟨fun K => rfl, by intro v; simp⟩
  · refine CrelK_head_step (c₁' := Comp.subst u₁ N₂₁) (c₂' := Comp.subst u₂ N₂₂) ?_ ?_
      (fun m hm => hN₂ m hm u₁ u₂ hcw₁.inr_inv hcw₂.inr_inv (VrelK_mono (le_of_lt hm) hu))
    · exact ⟨fun K => rfl, by intro v; simp⟩
    · exact ⟨fun K => rfl, by intro v; simp⟩

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
  · exact ⟨fun K => rfl, by intro v; simp⟩
  · exact ⟨fun K => rfl, by intro v; simp⟩


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
theorem krelS_handleF_intro {n : Nat} {C D : CTy Eff Mult} {e φ : Eff} {h₁ h₂ : Handler}
    {K₁ K₂ : Stack} (hHR : HandlerRel Eff Mult n h₁ h₂) (hK : KrelS n C D φ K₁ K₂)
    (hres : ∀ m, m < n → ∀ (op : OpId) (w₁ w₂ : Val) (Cᵢ : CTy Eff Mult) (εᵢ : Eff)
              (Kᵢ Kᵢ' : Stack) (cfg₁ cfg₂ : Config),
        Bang.handlesOp h₁ h₁.label op = true →
        Val.Closed w₁ → Val.Closed w₂ →
        (∀ Aop, EffSig.opArg (Eff := Eff) (Mult := Mult) h₁.label op = some Aop → VrelK m Aop w₁ w₂) →
        KrelS m Cᵢ C εᵢ Kᵢ Kᵢ' →
        (∀ Aᵣ, EffSig.opRes (Eff := Eff) (Mult := Mult) h₁.label op = some Aᵣ →
          ∃ qᵣ, Cᵢ = CTy.F qᵣ Aᵣ) →
        Bang.dispatchOn op w₁ (Kᵢ, h₁, K₁) = some cfg₁ →
        Bang.dispatchOn op w₂ (Kᵢ', h₂, K₂) = some cfg₂ →
        CoApproxC_le m cfg₁ cfg₂) :
    KrelS n C D e (Frame.handleF h₁ :: K₁) (Frame.handleF h₂ :: K₂) := by
  rw [krelS_handleF]; exact ⟨hHR, KrelS_eff_cast hK, hres⟩

/-- ◊4.5b-append `krelS_append` — the config-level Biernacki Lemma-2 analogue. Compose a related captured
continuation `Kᵢ ~ Kᵢ'` (answer type `Dᵢ`) with a related handleF-extended tail (`handleF h :: K`, hole
`Dᵢ`) into the appended stack `Kᵢ ++ handleF h :: K`. The inner `Kᵢ`'s answer type MUST equal the
reinstalled-handler frame's hole type `Dᵢ` (the resume value flows out of `Kᵢ` into the handler frame).
Proven by induction on `Kᵢ` (structural, like `crelK_ret`/`KrelS_mono`): nil = `krelS_handleF_intro`;
letF/appF peel + reconstruct over the appended tail. The handleF-in-`Kᵢ` sub-case (a handler NESTED in
the captured continuation) needs the resume-conjunct RELOCATED to the appended tail — same as the
decomp-miss-wrap; one documented sorry. shape: biernacki-popl18 §5.4 Lemma 2 (config-level append). -/
theorem krelS_append {m : Nat} {Cᵢ Dᵢ D' : CTy Eff Mult} {εᵢ e' : Eff} {h₁ h₂ : Handler}
    {Kᵢ Kᵢ' K₁ K₂ : Stack}
    (hin : KrelS m Cᵢ Dᵢ εᵢ Kᵢ Kᵢ')
    (hHR : HandlerRel Eff Mult m h₁ h₂)
    (htail : KrelS m Dᵢ D' e' K₁ K₂)
    (hres : ∀ k, k < m → ∀ (op : OpId) (w₁ w₂ : Val) (Cⱼ : CTy Eff Mult) (εⱼ : Eff)
              (Kⱼ Kⱼ' : Stack) (cfg₁ cfg₂ : Config),
        Bang.handlesOp h₁ h₁.label op = true →
        Val.Closed w₁ → Val.Closed w₂ →
        (∀ Aop, EffSig.opArg (Eff := Eff) (Mult := Mult) h₁.label op = some Aop → VrelK k Aop w₁ w₂) →
        KrelS k Cⱼ Dᵢ εⱼ Kⱼ Kⱼ' →
        (∀ Aᵣ, EffSig.opRes (Eff := Eff) (Mult := Mult) h₁.label op = some Aᵣ →
          ∃ qᵣ, Cⱼ = CTy.F qᵣ Aᵣ) →
        Bang.dispatchOn op w₁ (Kⱼ, h₁, K₁) = some cfg₁ →
        Bang.dispatchOn op w₂ (Kⱼ', h₂, K₂) = some cfg₂ →
        CoApproxC_le k cfg₁ cfg₂) :
    KrelS m Cᵢ D' εᵢ (Kᵢ ++ Frame.handleF h₁ :: K₁) (Kᵢ' ++ Frame.handleF h₂ :: K₂) := by
  induction Kᵢ generalizing Cᵢ εᵢ Kᵢ' with
  | nil =>
      -- Kᵢ' = [] (nil clause), Cᵢ = Dᵢ; the append is `handleF h :: K` — `krelS_handleF_intro`.
      cases Kᵢ' with
      | nil =>
          rw [krelS_nil] at hin
          obtain ⟨rfl, _⟩ := hin
          simpa using krelS_handleF_intro (e := εᵢ) hHR htail hres
      | cons _ _ => simp only [KrelS] at hin
  | cons fr Kᵢrest ih =>
      cases Kᵢ' with
      | nil => exact absurd hin (by simp only [KrelS]; cases fr <;> exact not_false)
      | cons fr₂ Kᵢ'rest =>
          cases fr with
          | letF N₁ =>
              cases fr₂ with
              | letF N₂ =>
                  rw [krelS_letF] at hin
                  obtain ⟨q, A, B, φ, hC, hbody, htin⟩ := hin
                  rw [List.cons_append, List.cons_append, krelS_letF]
                  exact ⟨q, A, B, φ, hC, hbody, ih htin⟩
              | _ => simp only [KrelS] at hin
          | appF u₁ =>
              cases fr₂ with
              | appF u₂ =>
                  rw [krelS_appF] at hin
                  obtain ⟨q, A, B, hC, hcu₁, hcu₂, hu, htin⟩ := hin
                  rw [List.cons_append, List.cons_append, krelS_appF]
                  exact ⟨q, A, B, hC, hcu₁, hcu₂, hu, ih htin⟩
              | _ => simp only [KrelS] at hin
          | handleF hh₁ =>
              cases fr₂ with
              | handleF hh₂ =>
                  -- ◊4.5b-append: a handler NESTED in the captured continuation. Its resume conjunct
                  -- (from `hin`) is at the OLD tail; the append puts it over `Kᵢrest ++ handleF h :: K`,
                  -- so the conjunct must RELOCATE. Same gap as the decomp-miss-wrap; documented sorry.
                  -- letF/appF/nil are PROVEN; this is the nested-handler-in-continuation case (rare).
                  sorry
              | _ => simp only [KrelS] at hin

/-- ◊4.5b-append the STATE-reinstall lemma — the resumptive heart. A `state ℓ s` handler frame over a
related tail self-relates at every index, with the resume conjunct supplied by GUARDED RECURSION on the
index: the get/put dispatch reinstalls `state ℓ s` and resumes `ret r` (r = s for get, unit for put)
through the captured continuation `Kᵢ`, which `krelS_append`s onto the reinstalled frame + tail at the
DROPPED index `m' < m` (the IH). The stored state `s` self-relates at `S` (hsv, from the caller's typing
via `vrelK_fund`). shape: biernacki-popl18 §5.4 resumptive clause + the ▷-guarded reinstall. -/
theorem krelS_state_reinstall {q : Mult} {A S : VTy Eff Mult} {D : CTy Eff Mult} {φ : Eff} {ℓ : Label}
    (hgr : EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "get" = some S)
    (hp : EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "put" = some S)
    (hpr : EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "put" = some VTy.unit)
    (hrestrict : ∀ op s, Bang.handlesOp (Handler.state ℓ s) ℓ op = true → op = "get" ∨ op = "put") :
    ∀ m (s₁ s₂ : Val), Val.Closed s₁ → Val.Closed s₂ → VrelK m S s₁ s₂ →
      ∀ (K₁ K₂ : Stack), KrelS m (CTy.F q A) D φ K₁ K₂ →
      KrelS m (CTy.F q A) D φ (Frame.handleF (Handler.state ℓ s₁) :: K₁)
                              (Frame.handleF (Handler.state ℓ s₂) :: K₂) := by
  -- GUARDED RECURSION on the index: the reinstalled handler (over the SAME tail, at the put-updated state
  -- pair) relates at the DROPPED index m' < m (the IH), supplying `krelS_append`'s resume conjunct.
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro s₁ s₂ hcs₁ hcs₂ hsv K₁ K₂ hK
    refine krelS_handleF_intro
      (show HandlerRel Eff Mult m (Handler.state ℓ s₁) (Handler.state ℓ s₂) from ⟨rfl, S, hsv⟩) hK ?_
    intro m' hm' op w₁ w₂ Cᵢ εᵢ Kᵢ Kᵢ' cfg₁ cfg₂ hcatch hcw₁ hcw₂ hVrel hKi hCᵢ hd₁ hd₂
    rcases hrestrict op s₁ hcatch with rfl | rfl
    · -- GET: cfg = (Kᵢ ++ handleF(state ℓ sⱼ)::Kⱼ, ret sⱼ); resume value = the stored state (related).
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
        (KrelS_mono (le_of_lt hm') hK) hreinst.2.2
      have hret := crelK_ret (q := qᵣ) (A := S) (e := εᵢ) hcs₁ hcs₂ (VrelK_mono (le_of_lt hm') hsv)
      rw [CrelK] at hret
      exact hret D _ _ happ
    · -- PUT: cfg = (Kᵢ ++ handleF(state ℓ wⱼ)::Kⱼ, ret unit); reinstalled state = the payload (related at
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
        (KrelS_mono (le_of_lt hm') hK) hreinst.2.2
      have hret := crelK_ret (q := qᵣ) (A := VTy.unit) (e := εᵢ)
        (fun k => rfl) (fun k => rfl)
        (by show VrelK m' VTy.unit Val.vunit Val.vunit; rw [VrelK, BaseRel]; exact ⟨rfl, rfl⟩)
      rw [CrelK] at hret
      exact hret D _ _ happ

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
theorem dispatchOn_state_isSome (op : OpId) (v : Val) (Kᵢ Kₒ : Stack) (ℓ : Label) (s : Val) :
    ∃ c, Bang.dispatchOn op v (Kᵢ, Handler.state ℓ s, Kₒ) = some c := by
  rw [dispatchOn]; split <;> exact ⟨_, rfl⟩

/-- `dispatchOn (transaction _)` is total. -/
theorem dispatchOn_transaction_isSome (op : OpId) (v : Val) (Kᵢ Kₒ : Stack) (ℓ : Label) (Θ : Store) :
    ∃ c, Bang.dispatchOn op v (Kᵢ, Handler.transaction ℓ Θ, Kₒ) = some c := by
  unfold dispatchOn; split_ifs <;> first | exact ⟨_, rfl⟩ | (cases v <;> exact ⟨_, rfl⟩)

/-- ◊4.5b-append the TRANSACTION-reinstall lemma — the multi-cell resumptive heart (the `state` analogue
with a heap). GUARDED RECURSION on the index; newTVar/readTVar/writeTVar reinstall + resume,
`krelS_append`ed onto the reinstalled frame at the dropped index. Each op preserves `HeapRel` (int cells
related = equal). All heap `getD` via the GetD-free `heap_getD_*`. -/
theorem krelS_transaction_reinstall {q : Mult} {A : VTy Eff Mult} {D : CTy Eff Mult} {φ : Eff}
    {ℓ : Label}
    (hnewA : EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "newTVar" = some VTy.int)
    (hnewR : EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "newTVar" = some VTy.int)
    (hreadA : EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "readTVar" = some VTy.int)
    (hreadR : EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "readTVar" = some VTy.int)
    (hwriteA : EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "writeTVar"
      = some (VTy.prod (VTy.int : VTy Eff Mult) VTy.int))
    (hwriteR : EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "writeTVar" = some VTy.unit)
    (hrestrict : ∀ op Θ', Bang.handlesOp (Handler.transaction ℓ Θ') ℓ op = true →
      op = "newTVar" ∨ op = "readTVar" ∨ op = "writeTVar") :
    ∀ m (Θ₁ Θ₂ : Store), HeapRel Eff Mult m Θ₁ Θ₂ →
      ∀ (K₁ K₂ : Stack), KrelS m (CTy.F q A) D φ K₁ K₂ →
      KrelS m (CTy.F q A) D φ (Frame.handleF (Handler.transaction ℓ Θ₁) :: K₁)
                              (Frame.handleF (Handler.transaction ℓ Θ₂) :: K₂) := by
  intro m
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
          from ⟨rfl, happend.1, happend.2⟩) (KrelS_mono (le_of_lt hm') hK) hreinst.2.2
      have hret := crelK_ret (q := qᵣ) (A := VTy.int) (e := εᵢ)
        (fun k => rfl) (fun k => rfl)
        (by show VrelK m' VTy.int (Val.vint Θ₁.length) (Val.vint Θ₂.length)
            rw [VrelK, BaseRel]; exact ⟨Θ₁.length, rfl, by rw [hheap'.1]⟩)
      rw [CrelK] at hret
      exact hret D _ _ happ
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
          from ⟨rfl, hheap'.1, hheap'.2⟩) (KrelS_mono (le_of_lt hm') hK) hreinst.2.2
      have hret := crelK_ret (q := qᵣ) (A := VTy.int) (e := εᵢ)
        (by rw [hca₁]; intro k; rfl) (by rw [hca₂]; intro k; rfl) hcellrel
      rw [CrelK] at hret
      exact hret D _ _ happ
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
          from ⟨rfl, hset.1, hset.2⟩) (KrelS_mono (le_of_lt hm') hK) hreinst.2.2
      have hret := crelK_ret (q := qᵣ) (A := VTy.unit) (e := εᵢ)
        (fun k => rfl) (fun k => rfl)
        (by show VrelK m' VTy.unit Val.vunit Val.vunit; rw [VrelK, BaseRel]; exact ⟨rfl, rfl⟩)
      rw [CrelK] at hret
      exact hret D _ _ happ

/-- ◊4.5b sub-block (f) — `splitAt`-DECOMPOSITION over `KrelS` (the producer-`up` enabler). With the
`h₁ = h₂` handleF clause, `splitAt` fires IDENTICALLY on the two related stacks: the SAME catching
handler `h` at the SAME position (same inner-prefix length), and the OUTER tails `K₁ₒ, K₂ₒ` stay
`KrelS`-related at SOME hole type/row `(C', e')`. Proven by induction on `K₁` (the `KrelS` def forces
matching frame shapes; `letF`/`appF` skip the frame; the `handleF`-HIT case is the split point with the
tail-relatedness from the clause; the `handleF`-MISS case recurses). The `(C', e')` are existential —
they are the hole type/row threaded to the split point; the dispatch consumer pins them via the supplied
resume relation. shape: biernacki-popl18 §5.4 (set-row `ρ`-free split). -/
theorem krelS_splitAt_decomp {n : Nat} {C D : CTy Eff Mult} {e : Eff}
    {K₁ K₂ : Stack} {ℓ : Label} {op : OpId} {K₁ᵢ K₁ₒ : Stack} {h : Handler}
    (hK : KrelS n C D e K₁ K₂)
    (hsp : Bang.splitAt K₁ ℓ op = some (K₁ᵢ, h, K₁ₒ)) :
    -- ◊4.5b-append: `splitAt K₂` fires at the SAME position (HandlerRel fixes label+kind, which
    -- `splitAt`/`handlesOp` read) with a RELATED handler `h'` (`HandlerRel n h h'`, stored state related),
    -- the INNER prefixes related at SOME `(Cᵢ,Dᵢ,εᵢ)` (the producer threads the resume value through them),
    -- the OUTER tails related at SOME `(C',e')`, AND the Kᵢ-threading resume conjunct from the catching
    -- handleF clause. state/txn use the inner-prefix relation (Kᵢ KEPT); throws ignores it (Kᵢ discarded).
    ∃ (K₂ᵢ K₂ₒ : Stack) (h' : Handler) (Dᵢ : CTy Eff Mult) (C' : CTy Eff Mult) (e' : Eff),
      Bang.splitAt K₂ ℓ op = some (K₂ᵢ, h', K₂ₒ) ∧ HandlerRel Eff Mult n h h' ∧
      KrelS n C Dᵢ e K₁ᵢ K₂ᵢ ∧ KrelS n C' D e' K₁ₒ K₂ₒ
      ∧ (∀ m, m < n → ∀ (op' : OpId) (w₁ w₂ : Val) (Cᵢ' : CTy Eff Mult) (εᵢ' : Eff)
            (Kᵢ Kᵢ' : Stack) (cfg₁ cfg₂ : Config),
          Bang.handlesOp h h.label op' = true →
          Val.Closed w₁ → Val.Closed w₂ →
          (∀ Aop, EffSig.opArg (Eff := Eff) (Mult := Mult) h.label op' = some Aop → VrelK m Aop w₁ w₂) →
          -- inner-prefix answer = the SPLIT-POINT hole `Dᵢ` (the catching frame's hole, threaded above).
          KrelS m Cᵢ' Dᵢ εᵢ' Kᵢ Kᵢ' →
          (∀ Aᵣ, EffSig.opRes (Eff := Eff) (Mult := Mult) h.label op' = some Aᵣ →
            ∃ qᵣ, Cᵢ' = CTy.F qᵣ Aᵣ) →
          Bang.dispatchOn op' w₁ (Kᵢ, h, K₁ₒ) = some cfg₁ →
          Bang.dispatchOn op' w₂ (Kᵢ', h', K₂ₒ) = some cfg₂ →
          CoApproxC_le m cfg₁ cfg₂) := by
  induction K₁ generalizing K₂ K₁ᵢ K₁ₒ C e with
  | nil => simp [Bang.splitAt] at hsp
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
                  rw [splitAt_letF, Option.map_eq_some_iff] at hsp
                  obtain ⟨⟨Ki', hh, Ko'⟩, hsp', heq⟩ := hsp
                  simp only [Prod.mk.injEq] at heq
                  obtain ⟨rfl, rfl, rfl⟩ := heq
                  obtain ⟨K₂ᵢ, K₂ₒ, h', Dᵢ, C', e', hsp2, hHR, hin, htail2, hres2⟩ := ih htail hsp'
                  -- inner prefix grows by THIS letF frame: prepend it (the frame body self-relates via hbody).
                  -- `ih` recursed on `htail : KrelS n B D φ K₁' K₂'`, so `hin : KrelS n B Dᵢ φ K₁ᵢ K₂ᵢ`; the
                  -- letF wrap is at hole F q A, row e (the ambient), tail at φ — matches `hbody`.
                  refine ⟨Frame.letF N₂ :: K₂ᵢ, K₂ₒ, h', Dᵢ, C', e',
                    by rw [splitAt_letF, hsp2]; rfl, hHR, ?_, htail2, hres2⟩
                  rw [krelS_letF]; exact ⟨q, A, B, φ, hC, hbody, hin⟩
              | _ => simp only [KrelS] at hK
          | appF w₁ =>
              cases fr₂ with
              | appF w₂ =>
                  rw [krelS_appF] at hK
                  obtain ⟨q, A, B, hC, hcw₁, hcw₂, hw, htail⟩ := hK
                  rw [splitAt_appF, Option.map_eq_some_iff] at hsp
                  obtain ⟨⟨Ki', hh, Ko'⟩, hsp', heq⟩ := hsp
                  simp only [Prod.mk.injEq] at heq
                  obtain ⟨rfl, rfl, rfl⟩ := heq
                  obtain ⟨K₂ᵢ, K₂ₒ, h', Dᵢ, C', e', hsp2, hHR, hin, htail2, hres2⟩ := ih htail hsp'
                  refine ⟨Frame.appF w₂ :: K₂ᵢ, K₂ₒ, h', Dᵢ, C', e',
                    by rw [splitAt_appF, hsp2]; rfl, hHR, ?_, htail2, hres2⟩
                  rw [krelS_appF]; exact ⟨q, A, B, hC, hcw₁, hcw₂, hw, hin⟩
              | _ => simp only [KrelS] at hK
          | handleF hh₁ =>
              cases fr₂ with
              | handleF hh₂ =>
                  rw [krelS_handleF] at hK
                  obtain ⟨hHRtop, htail, hres⟩ := hK
                  by_cases hcatch : handlesOp hh₁ ℓ op = true
                  · -- the catching frame: inner prefix = `[]` (nil at hole C), outer tail = K₁'/K₂'
                    -- (related via `htail`), and the clause's resume conjunct `hres` is the Kᵢ-threading one.
                    rw [splitAt_handleF_hit K₁' hcatch] at hsp
                    rw [Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hsp
                    obtain ⟨rfl, rfl, rfl⟩ := hsp
                    have hcatch2 : handlesOp hh₂ ℓ op = true := by
                      cases hh₁ <;> cases hh₂ <;>
                        simp_all only [HandlerRel, handlesOp] <;> obtain ⟨rfl, _⟩ := hHRtop <;> assumption
                    refine ⟨[], K₂', hh₂, C, C, e, splitAt_handleF_hit K₂' hcatch2, hHRtop, ?_, htail, hres⟩
                    rw [krelS_nil]; exact ⟨rfl, fun q A hC v₁ v₂ _ _ _ _ => ⟨1, v₂, rfl⟩⟩
                  · simp only [Bool.not_eq_true] at hcatch
                    rw [splitAt_handleF_miss K₁' hcatch, Option.map_eq_some_iff] at hsp
                    obtain ⟨⟨Ki', hh, Ko'⟩, hsp', heq⟩ := hsp
                    simp only [Prod.mk.injEq] at heq
                    obtain ⟨rfl, rfl, rfl⟩ := heq
                    obtain ⟨K₂ᵢ, K₂ₒ, h', Dᵢ, C', e', hsp2, hHR, hin, htail2, hres2⟩ := ih htail hsp'
                    have hcatch2 : handlesOp hh₂ ℓ op = false := by
                      -- HandlerRel fixes label+kind ⇒ handlesOp hh₂ = handlesOp hh₁ = false (the miss).
                      cases hh₁ <;> cases hh₂ <;>
                        simp_all only [HandlerRel, handlesOp, false_iff, not_true, reduceCtorEq] <;>
                        (first
                          | exact absurd hHRtop not_false
                          | (obtain ⟨rfl, _⟩ := hHRtop; simpa [handlesOp] using hcatch)
                          | (obtain ⟨rfl, _, _⟩ := hHRtop; simpa [handlesOp] using hcatch))
                    refine ⟨Frame.handleF hh₂ :: K₂ᵢ, K₂ₒ, h', Dᵢ, C', e',
                      by rw [splitAt_handleF_miss K₂' hcatch2, hsp2]; rfl, hHR, ?_, htail2, hres2⟩
                    rw [krelS_handleF]
                    refine ⟨hHRtop, hin, ?_⟩
                    -- ◊4.5b-append: the wrapping (non-catching) handleF inside the captured continuation
                    -- needs its resume conjunct re-stated at the inner-prefix tail `Ki'` (not the original
                    -- `K₁'`). `hres` is at `K₁'`; bridging needs a conjunct-at-Ki' lemma. PENDING — a handler
                    -- nested in the captured continuation (rare); documented sorry, the other 3 decomp cases
                    -- (letF/appF/handleF-hit) are PROVEN. Closes with the conjunct-relocation helper.
                    sorry
              | _ => simp only [KrelS] at hK

/-- `splitAt` returns a handler that CATCHES `(ℓ, op)` (the split point is a matching frame). The
producer reads this off to discharge the resume conjunct's `handlesOp` guard. -/
theorem splitAt_some_handlesOp {K : EvalCtx} {ℓ : Label} {op : OpId} {Kᵢ Kₒ : EvalCtx} {h : Handler}
    (hsp : Bang.splitAt K ℓ op = some (Kᵢ, h, Kₒ)) : Bang.handlesOp h ℓ op = true := by
  induction K generalizing Kᵢ Kₒ h with
  | nil => simp [Bang.splitAt] at hsp
  | cons fr K ih =>
    cases fr with
    | letF N =>
        rw [splitAt_letF, Option.map_eq_some_iff] at hsp
        obtain ⟨⟨Ki', h', Ko'⟩, hsp', heq⟩ := hsp
        simp only [Prod.mk.injEq] at heq; exact heq.2.1 ▸ ih hsp'
    | appF w =>
        rw [splitAt_appF, Option.map_eq_some_iff] at hsp
        obtain ⟨⟨Ki', h', Ko'⟩, hsp', heq⟩ := hsp
        simp only [Prod.mk.injEq] at heq; exact heq.2.1 ▸ ih hsp'
    | handleF hh =>
        by_cases hc : handlesOp hh ℓ op = true
        · rw [splitAt_handleF_hit K hc] at hsp
          rw [Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hsp
          obtain ⟨_, rfl, _⟩ := hsp; exact hc
        · simp only [Bool.not_eq_true] at hc
          rw [splitAt_handleF_miss K hc, Option.map_eq_some_iff] at hsp
          obtain ⟨⟨Ki', h', Ko'⟩, hsp', heq⟩ := hsp
          simp only [Prod.mk.injEq] at heq; exact heq.2.1 ▸ ih hsp'

-- ◊4.5b-append the op-PRODUCER, EXTRACTED from `crelK_fund`'s `up` case into a STANDALONE lemma (taking
-- the arg-value relation `hvk` precomputed, so NO `vrelK_fund` recursion inside). This keeps `crelK_fund`'s
-- `up`-arm a one-line call, so the mutual block's match stays small enough for structural-recursion inference
-- (the full producer arm — esp. with state+txn — overflows it otherwise). Goal: `CrelK n (F q B) φ`.
-- none-half: stuck ⇒ vacuous (`not_convergesC_le_up_splitNone`). some-half: `krelS_splitAt_decomp` gives the
-- related handler + inner-prefix relation + the Kᵢ-threading resume conjunct; throws aborts (Kᵢ discarded),
-- state/txn dispatch through the kept Kᵢ — all discharged by the conjunct + `coApproxC_le_anti_step`.
-- STANDALONE ⇒ a `set_option maxHeartbeats` is safe here — no mutual structural-recursion inference.
set_option maxHeartbeats 1000000 in
theorem crelK_fund_up {n : Nat} {ℓ : Label} {op : OpId} {q : Mult} {A B : VTy Eff Mult} {φ : Eff}
    {v₁ v₂ : Val}
    (hArg : EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ op = some A)
    (hRes : EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ op = some B)
    (hcv₁ : Val.Closed v₁) (hcv₂ : Val.Closed v₂) (hvk : VrelK n A v₁ v₂) :
    CrelK n (CTy.F q B) φ (Comp.up ℓ op v₁) (Comp.up ℓ op v₂) := by
  rw [CrelK]
  intro D K₁ K₂ hK
  cases hsp1 : Bang.splitAt K₁ ℓ op with
  | none =>
      intro hconv; exact absurd hconv (not_convergesC_le_up_splitNone K₁ ℓ op v₁ hsp1)
  | some t =>
      obtain ⟨K₁ᵢ, h, K₁ₒ⟩ := t
      have hcatch : Bang.handlesOp h ℓ op = true := splitAt_some_handlesOp hsp1
      have hlbl : h.label = ℓ := handlesOp_label hcatch
      obtain ⟨K₂ᵢ, K₂ₒ, h', Dᵢ, C', e', hsp2, hHR, hinner, htail, hres⟩ := krelS_splitAt_decomp hK hsp1
      cases h with
      | throws lh =>
          obtain ⟨lh', rfl⟩ : ∃ lh', h' = Handler.throws lh' := by
            cases h' <;> simp_all only [HandlerRel] <;> exact ⟨_, rfl⟩
          cases n with
          | zero => exact coApproxC_le_zero _ _
          | succ k =>
              have hstep1 : Source.step (K₁, Comp.up ℓ op v₁) = some (K₁ₒ, Comp.ret v₁) := by
                show Bang.dispatch K₁ ℓ op v₁ = _; unfold Bang.dispatch; rw [hsp1]; simp [dispatchOn]
              have hstep2 : Source.step (K₂, Comp.up ℓ op v₂) = some (K₂ₒ, Comp.ret v₂) := by
                show Bang.dispatch K₂ ℓ op v₂ = _; unfold Bang.dispatch; rw [hsp2]; simp [dispatchOn]
              refine coApproxC_le_anti_step hstep1 (by intro u; simp) hstep2 (by intro u; simp) ?_
              have hcatch' : Bang.handlesOp (Handler.throws lh) (Handler.throws lh).label op = true := by
                rw [hlbl]; exact hcatch
              refine hres k (Nat.lt_succ_self k) op v₁ v₂ _ _ K₁ᵢ K₂ᵢ
                (K₁ₒ, Comp.ret v₁) (K₂ₒ, Comp.ret v₂)
                hcatch' hcv₁ hcv₂ ?_ (KrelS_mono (le_of_lt (Nat.lt_succ_self k)) hinner)
                ?_ (by simp [dispatchOn]) (by simp [dispatchOn])
              · intro Aop hAop
                rw [hlbl, hArg] at hAop; obtain rfl := (Option.some.injEq _ _).mp hAop.symm
                exact VrelK_mono (le_of_lt (Nat.lt_succ_self k)) hvk
              · intro Aᵣ hAᵣ; rw [hlbl, hRes] at hAᵣ
                obtain rfl := (Option.some.injEq _ _).mp hAᵣ.symm; exact ⟨q, rfl⟩
      | state lh s =>
          cases n with
          | zero => exact coApproxC_le_zero _ _
          | succ k =>
              obtain ⟨c₁, hc₁⟩ := dispatchOn_state_isSome op v₁ K₁ᵢ K₁ₒ lh s
              obtain ⟨c₂, hc₂⟩ : ∃ c, Bang.dispatchOn op v₂ (K₂ᵢ, h', K₂ₒ) = some c := by
                cases h' <;> simp only [HandlerRel] at hHR
                obtain ⟨rfl, _⟩ := hHR; exact dispatchOn_state_isSome op v₂ K₂ᵢ K₂ₒ _ _
              have hstep1 : Source.step (K₁, Comp.up ℓ op v₁) = some c₁ := by
                show Bang.dispatch K₁ ℓ op v₁ = _; unfold Bang.dispatch; rw [hsp1]; exact hc₁
              have hstep2 : Source.step (K₂, Comp.up ℓ op v₂) = some c₂ := by
                show Bang.dispatch K₂ ℓ op v₂ = _; unfold Bang.dispatch; rw [hsp2]; exact hc₂
              refine coApproxC_le_anti_step hstep1 (by intro u; simp) hstep2 (by intro u; simp) ?_
              have hcatch' : Bang.handlesOp (Handler.state lh s) (Handler.state lh s).label op = true := by
                rw [hlbl]; exact hcatch
              refine hres k (Nat.lt_succ_self k) op v₁ v₂ _ _ K₁ᵢ K₂ᵢ c₁ c₂
                hcatch' hcv₁ hcv₂ ?_ (KrelS_mono (le_of_lt (Nat.lt_succ_self k)) hinner) ?_ hc₁ hc₂
              · intro Aop hAop
                rw [hlbl, hArg] at hAop; obtain rfl := (Option.some.injEq _ _).mp hAop.symm
                exact VrelK_mono (le_of_lt (Nat.lt_succ_self k)) hvk
              · intro Aᵣ hAᵣ; rw [hlbl, hRes] at hAᵣ
                obtain rfl := (Option.some.injEq _ _).mp hAᵣ.symm; exact ⟨q, rfl⟩
      | transaction lh Θ' =>
          cases n with
          | zero => exact coApproxC_le_zero _ _
          | succ k =>
              obtain ⟨c₁, hc₁⟩ := dispatchOn_transaction_isSome op v₁ K₁ᵢ K₁ₒ lh Θ'
              obtain ⟨c₂, hc₂⟩ : ∃ c, Bang.dispatchOn op v₂ (K₂ᵢ, h', K₂ₒ) = some c := by
                cases h' <;> simp only [HandlerRel] at hHR
                obtain ⟨rfl, _, _⟩ := hHR; exact dispatchOn_transaction_isSome op v₂ K₂ᵢ K₂ₒ _ _
              have hstep1 : Source.step (K₁, Comp.up ℓ op v₁) = some c₁ := by
                show Bang.dispatch K₁ ℓ op v₁ = _; unfold Bang.dispatch; rw [hsp1]; exact hc₁
              have hstep2 : Source.step (K₂, Comp.up ℓ op v₂) = some c₂ := by
                show Bang.dispatch K₂ ℓ op v₂ = _; unfold Bang.dispatch; rw [hsp2]; exact hc₂
              refine coApproxC_le_anti_step hstep1 (by intro u; simp) hstep2 (by intro u; simp) ?_
              have hcatch' : Bang.handlesOp (Handler.transaction lh Θ') (Handler.transaction lh Θ').label op
                  = true := by rw [hlbl]; exact hcatch
              refine hres k (Nat.lt_succ_self k) op v₁ v₂ _ _ K₁ᵢ K₂ᵢ c₁ c₂
                hcatch' hcv₁ hcv₂ ?_ (KrelS_mono (le_of_lt (Nat.lt_succ_self k)) hinner) ?_ hc₁ hc₂
              · intro Aop hAop
                rw [hlbl, hArg] at hAop; obtain rfl := (Option.some.injEq _ _).mp hAop.symm
                exact VrelK_mono (le_of_lt (Nat.lt_succ_self k)) hvk
              · intro Aᵣ hAᵣ; rw [hlbl, hRes] at hAᵣ
                obtain rfl := (Option.some.injEq _ _).mp hAᵣ.symm; exact ⟨q, rfl⟩

/-- ◊4.5b the `handleThrows` compat core at `CrelK`. REFOCUS `(K, handle h M) ↦ (handleF h::K, M)`
(one PUSH step), then run `M` (related at its body row `e`) through the handleF-extended stack, shown
`KrelS`-related by `krelS_handleF_intro`. The block discharges `ℓ` from `e` to `φ`. ▷-free. -/
theorem compatK_handleThrows {n : Nat} {q : Mult} {A : VTy Eff Mult} {e φ : Eff} {ℓ : Label}
    {M₁ M₂ : Comp}
    (hArg : EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "raise" = some A)
    (hM : CrelK n (CTy.F q A) e M₁ M₂) :
    CrelK n (CTy.F q A) φ (Comp.handle (Handler.throws ℓ) M₁) (Comp.handle (Handler.throws ℓ) M₂) := by
  rw [CrelK]
  intro D K₁ K₂ hK
  refine coApproxC_le_reduce
    (cfg₁' := (Frame.handleF (Handler.throws ℓ) :: K₁, M₁))
    (cfg₂' := (Frame.handleF (Handler.throws ℓ) :: K₂, M₂))
    rfl (by intro u; simp) rfl (by intro u; simp) ?_
  rw [CrelK] at hM
  refine hM D (Frame.handleF (Handler.throws ℓ) :: K₁) (Frame.handleF (Handler.throws ℓ) :: K₂)
    (krelS_handleF_intro (by simp only [HandlerRel]) hK ?_)
  -- THROWS resume supply: `dispatchOn op w (Kᵢ, throws ℓ, Kⱼ) = (Kⱼ, ret w)` (zero-shot abort — Kᵢ
  -- DISCARDED). The `handlesOp` guard forces `op = "raise"`, so `opArg ℓ "raise" = A` (hArg) gives
  -- `VrelK m A w` from `hVrel`; the dispatched config relation IS the tail's return-half — `crelK_ret`
  -- on the (downward-closed) tail `hK` at hole type `F q A`. The threaded `Kᵢ` is irrelevant for throws.
  intro m hm op w₁ w₂ Cᵢ εᵢ Kᵢ Kᵢ' cfg₁ cfg₂ hcatch hcw₁ hcw₂ hVrel _hKi _hCᵢ hd₁ hd₂
  -- `hcatch` (handlesOp (throws ℓ) ℓ op) forces `op = "raise"`.
  have hop : op = "raise" := by
    simp only [Handler.label, handlesOp, Bool.and_eq_true, beq_iff_eq] at hcatch; exact hcatch.2
  subst hop
  have hw : VrelK m A w₁ w₂ := hVrel A (by rw [Handler.label]; exact hArg)
  -- dispatchOn throws ignores op AND Kᵢ: cfgⱼ = (Kⱼ, ret w).
  simp only [dispatchOn] at hd₁ hd₂
  obtain rfl := (Option.some.injEq _ _).mp hd₁.symm
  obtain rfl := (Option.some.injEq _ _).mp hd₂.symm
  have hret := crelK_ret (q := q) (e := φ) hcw₁ hcw₂ hw
  rw [CrelK] at hret
  exact hret D K₁ K₂ (KrelS_mono (le_of_lt hm) hK)

/-- ◊4.5b-append the `handleState` compat core at `CrelK`. REFOCUS `(K, handle (state ℓ s) M) ↦
(handleF (state ℓ s)::K, M)`, then run `M` (related at body row `e`) through the reinstalling stack, shown
`KrelS`-related by `krelS_state_reinstall` (the resumptive heart). The interface (get/put sig) + the stored
state's self-relation `hsv` are threaded from the caller's `HasCTy.handleState` typing. -/
theorem compatK_handleState {n : Nat} {q : Mult} {A S : VTy Eff Mult} {e φ : Eff} {ℓ : Label} {s : Val}
    {M₁ M₂ : Comp}
    (hgr : EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "get" = some S)
    (hp : EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "put" = some S)
    (hpr : EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "put" = some VTy.unit)
    (hrestrict : ∀ op s', Bang.handlesOp (Handler.state ℓ s') ℓ op = true → op = "get" ∨ op = "put")
    (hcs : Val.Closed s) (hsv : ∀ k, VrelK k S s s)
    (hM : CrelK n (CTy.F q A) e M₁ M₂) :
    CrelK n (CTy.F q A) φ (Comp.handle (Handler.state ℓ s) M₁) (Comp.handle (Handler.state ℓ s) M₂) := by
  rw [CrelK]
  intro D K₁ K₂ hK
  refine coApproxC_le_reduce
    (cfg₁' := (Frame.handleF (Handler.state ℓ s) :: K₁, M₁))
    (cfg₂' := (Frame.handleF (Handler.state ℓ s) :: K₂, M₂))
    rfl (by intro u; simp) rfl (by intro u; simp) ?_
  rw [CrelK] at hM
  -- discharge the row `φ → e` (the handler block discharges `ℓ`); `KrelS_eff_cast` (ε inert in KrelS).
  exact hM D (Frame.handleF (Handler.state ℓ s) :: K₁) (Frame.handleF (Handler.state ℓ s) :: K₂)
    (krelS_state_reinstall hgr hp hpr hrestrict n s s hcs hcs (hsv n) K₁ K₂ (KrelS_eff_cast hK))

/-- ◊4.5b the `handleTransaction` compat core at `CrelK`. The multi-cell resumptive analogue — same
handler-agnostic argument, closes like state/throws (`krelS_handleF_intro`); the heap `Θ` is arbitrary. -/
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
    (hM : CrelK n (CTy.F q A) e M₁ M₂) :
    CrelK n (CTy.F q A) φ (Comp.handle (Handler.transaction ℓ Θ) M₁)
                          (Comp.handle (Handler.transaction ℓ Θ) M₂) := by
  rw [CrelK]
  intro D K₁ K₂ hK
  refine coApproxC_le_reduce
    (cfg₁' := (Frame.handleF (Handler.transaction ℓ Θ) :: K₁, M₁))
    (cfg₂' := (Frame.handleF (Handler.transaction ℓ Θ) :: K₂, M₂))
    rfl (by intro u; simp) rfl (by intro u; simp) ?_
  rw [CrelK] at hM
  exact hM D (Frame.handleF (Handler.transaction ℓ Θ) :: K₁) (Frame.handleF (Handler.transaction ℓ Θ) :: K₂)
    (krelS_transaction_reinstall hnewA hnewR hreadA hreadR hwriteA hwriteR hrestrict n Θ Θ hheap
      K₁ K₂ (KrelS_eff_cast hK))


/-- A well-typed value is `ScopedIn Γ.length` (`HasVTy.shift_closed`: shifting at a cutoff `≥ Γ.length`
is the identity). The bridge from the typing derivation to the syntactic scope bound that
`closeV_closed_scoped` consumes. -/
theorem HasVTy.scopedIn {γ : GradeVec Mult} {Γ : TyCtx Eff Mult} {v : Val} {A : VTy Eff Mult}
    (h : HasVTy γ Γ v A) : Val.ScopedIn Γ.length v := fun k hk => h.shift_closed k hk



/-! ### B.5′ ◊4.5b — the migrated fundamental theorem (`vrelK_fund` / `crelK_fund`) over `CrelK`/`KrelS`

The answer-typed migration of `vrel_fund`/`crel_fund`, wiring the `compatK_*` cores (sub-block c) over
`EnvRelK`. STATUS: all NON-handler cases closed; the 3 handler cases + `up` carry `sorry` (→ sub-block f,
where the handler row-discharge / producer-`up` close together — exactly as the old `crel_fund`'s `up`
sorry). The Kripke continuation indices use `∀ m < n` at the letC/case/split seams (the `compatK_*`
cores' ▷-guarded shape) and `∀ j ≤ n` would over-supply. -/
mutual
theorem vrelK_fund {γ : GradeVec Mult} {Γ : TyCtx Eff Mult} {v : Val} {A : VTy Eff Mult}
    (h : HasVTy γ Γ v A) :
    ∀ (n : Nat) (δ₁ δ₂ : List Val), EnvRelK n Γ δ₁ δ₂ →
      VrelK n A (closeV δ₁ v) (closeV δ₂ v) := by
  cases h with
  | vunit => intro n δ₁ δ₂ _; rw [closeV_vunit, closeV_vunit, VrelK]; exact ⟨rfl, rfl⟩
  | vint  => intro n δ₁ δ₂ _; rw [closeV_vint, closeV_vint, VrelK]; exact ⟨_, rfl, rfl⟩
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
      exact crelK_ret hsc₁ hsc₂ (vrelK_fund hv n δ₁ δ₂ hδ)
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
            ⟨fun K => rfl, by intro u; simp⟩ ⟨fun K => rfl, by intro u; simp⟩
            (fun m hm => crelK_ret hsa₁ hsa₂ (vrelK_fund ha m δ₁ δ₂ (EnvRelK_mono (le_of_lt hm) hδ)))
      | @vvar _ i _ hget =>
          have hsc₁ : Val.Closed (closeV δ₁ (Val.vvar i)) :=
            closeV_closed_scoped hδ.closed_left (by
              have := (HasVTy.vvar hget).scopedIn; rwa [hδ.length_left])
          have hsc₂ : Val.Closed (closeV δ₂ (Val.vvar i)) :=
            closeV_closed_scoped hδ.closed_right (by
              have := (HasVTy.vvar hget).scopedIn; rwa [hδ.length_right])
          exact crelK_unfold hsc₁ hsc₂ (vrelK_fund (HasVTy.vvar hget) n δ₁ δ₂ hδ)
  | @up _ _ ℓ op v φ q A B hℓ hArg hRes hv =>
      -- ◊4.5b-append: the op-PRODUCER, now a THIN call to `crelK_fund_up` (extracted outside the mutual
      -- block so its match stays small enough for structural-recursion inference). `hvk` precomputed via
      -- `vrelK_fund hv` (the only mutual recursion); the rest is self-contained in `crelK_fund_up`.
      intro n δ₁ δ₂ hδ
      rw [closeC_up, closeC_up]
      have hvk : VrelK n A (closeV δ₁ v) (closeV δ₂ v) := vrelK_fund hv n δ₁ δ₂ hδ
      have hcv₁ : Val.Closed (closeV δ₁ v) :=
        closeV_closed_scoped hδ.closed_left (by have := hv.scopedIn; rwa [hδ.length_left])
      have hcv₂ : Val.Closed (closeV δ₂ v) :=
        closeV_closed_scoped hδ.closed_right (by have := hv.scopedIn; rwa [hδ.length_right])
      exact crelK_fund_up hArg hRes hcv₁ hcv₂ hvk
  | @handleThrows _ _ ℓ M e φ q A hArg hIface hM hsub =>
      -- ◊4.5b sub-block (f): handler row-discharge over `CrelK`. throws is ▷-free (zero-shot abort, no
      -- resume); `compatK_handleThrows` + `closeC_handleThrows` close it, mirroring the old `crel_fund`.
      intro n δ₁ δ₂ hδ
      rw [closeC_handleThrows, closeC_handleThrows]
      exact compatK_handleThrows hArg (crelK_fund hM n δ₁ δ₂ hδ)
  | @handleState _ _ ℓ s₀ M e φ q S A _hg hgr hp hpr hrestrict hs hM hsub =>
      -- ◊4.5b-append: state-resume closes via `compatK_handleState` (→ `krelS_state_reinstall`, the
      -- resumptive heart). The stored state `s₀` is CLOSED (`HasVTy [] []`, so `closeV δᵢ s₀ = s₀`); its
      -- self-relation `VrelK k S s₀ s₀` comes from `vrelK_fund hs` (the fundamental theorem on a closed value).
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
      exact compatK_handleState hgr hp hpr hrestrict' hcs₀ hsv (crelK_fund hM n δ₁ δ₂ hδ)
  | @handleTransaction _ _ ℓ Θ₀ M e φ q A hnewA hnewR hreadA hreadR hwriteA hwriteR _ hcells hM hsub =>
      -- ◊4.5b-append: transaction-resume via `compatK_handleTransaction` (→ `krelS_transaction_reinstall`).
      -- `HeapRel n Θ₀ Θ₀` from `hcells` via `heapRel_self_of_cells_int` (NO `vrelK_fund` — int is base, so
      -- this is NOT a recursive call on the side-condition `hcells`; that would break the block's recursion).
      intro n δ₁ δ₂ hδ
      rw [closeC_handleTransaction, closeC_handleTransaction]
      have hrestrict' : ∀ op Θ', Bang.handlesOp (Handler.transaction ℓ Θ') ℓ op = true →
          op = "newTVar" ∨ op = "readTVar" ∨ op = "writeTVar" := fun op Θ' hc => by
        simp only [handlesOp, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc; tauto
      exact compatK_handleTransaction hnewA hnewR hreadA hreadR hwriteA hwriteR hrestrict'
        (heapRel_self_of_cells_int n Θ₀ hcells) (crelK_fund hM n δ₁ δ₂ hδ)
end


/-! ### B.6′ ◊4.5b — `krelS_refl` (the answer-typed `lr_sound` capstone)

A well-typed stack is `KrelS`-self-related at answer type `Co` (the whole-program returner type, the
`D` parameter). Induction over `HasStack`: nil = `krelS_nil_succ`; letF/appF reuse the frame intros +
`crelK_fund`/`vrelK_fund` for the continuation/arg self-relation. The 3 handler arms carry `sorry`
(→ sub-block f, with the handler row-discharge + the `crelK_fund` handler cases). -/
theorem krelS_refl {n : Nat} {C : Stack} {e eo : Eff} {B Co : CTy Eff Mult} {qo : Mult}
    {Ao : VTy Eff Mult} (hCo : Co = CTy.F qo Ao)
    (hC : HasStack C e B eo Co) : KrelS n B Co e C C := by
  induction hC with
  | @nil e' C' =>
      -- `B = C' = Co = F qo Ao` (`hCo`): the returner empty stack is `krelS_nil_succ`.
      subst hCo; exact krelS_nil_succ n _ _ _
  | @letF K N e₁ e₂ eo q qk A B Co hN hK ihK =>
      -- HasStack.letF: tail `K` at the JOINED row `e₁⊔e₂` (ihK), continuation `N` at `e₂`, frame hole
      -- at `e₁`. Build the letF-extended `KrelS` at the joined row `e₁⊔e₂` (continuation row e₂ ≤ e₁⊔e₂),
      -- then WEAKEN the whole frame down to the goal's hole row `e₁` (`e₁ ≤ e₁⊔e₂`, antitone). The frame
      -- body self-relates the continuation `N` via `crelK_fund` (▷-guarded, ∀ m < n).
      have hframe : KrelS n (CTy.F q A) Co (e₁ ⊔ e₂) (Frame.letF N :: K) (Frame.letF N :: K) := by
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
  | @handleF K ℓ e φ eo q A Co hArg hIface hsub hK ihK =>
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
      refine ⟨by simp only [HandlerRel], KrelS_eff_cast (ihK hCo), ?_⟩
      intro m hm op w₁ w₂ Cᵢ εᵢ Kᵢ Kᵢ' cfg₁ cfg₂ hcatch hcw₁ hcw₂ hVrel _hKi _hCᵢ hd₁ hd₂
      have hop : op = "raise" := by
        simp only [Handler.label, handlesOp, Bool.and_eq_true, beq_iff_eq] at hcatch; exact hcatch.2
      subst hop
      have hw : VrelK m A w₁ w₂ := hVrel A (by rw [Handler.label]; exact hArg)
      simp only [dispatchOn] at hd₁ hd₂
      obtain rfl := (Option.some.injEq _ _).mp hd₁.symm
      obtain rfl := (Option.some.injEq _ _).mp hd₂.symm
      have hret := crelK_ret (q := q) (e := φ) hcw₁ hcw₂ hw
      rw [CrelK] at hret
      exact hret Co K K (KrelS_mono (le_of_lt hm) (KrelS_eff_cast (ihK hCo)))
  | @stateF K ℓ s e φ eo q A S Co hg hgr hp hpr hIface hcs hsub hK ihK =>
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
      exact krelS_state_reinstall hgr hp hpr hrestrict' n s s hcss hcss (hsv n) K K
        (KrelS_eff_cast (ihK hCo))
  | @transactionF K ℓ Θ e φ eo q A Co hnewA hnewR hreadA hreadR hwriteA hwriteR _ hcells hsub hK ihK =>
      -- ◊4.5b-append: transaction-frame self-relation IS `krelS_transaction_reinstall` at Θ=Θ; tail via
      -- `ihK` (cast φ→e); heap self-relation `HeapRel n Θ Θ` from `hcells` (all cells closed int).
      have hrestrict' : ∀ op Θ', Bang.handlesOp (Handler.transaction ℓ Θ') ℓ op = true →
          op = "newTVar" ∨ op = "readTVar" ∨ op = "writeTVar" := fun op Θ' hc => by
        simp only [handlesOp, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc; tauto
      exact krelS_transaction_reinstall hnewA hnewR hreadA hreadR hwriteA hwriteR hrestrict' n Θ Θ
        (heapRel_self_of_cells_int n Θ hcells) K K (KrelS_eff_cast (ihK hCo))

end Bang
