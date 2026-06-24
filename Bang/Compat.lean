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

/-- ◊4.5b `▷`-guarded head-expansion of `Crel` over the METERED observation: a context-independent
head-step on both sides reduces `Crel n` to the reducts related at every STRICTLY-SMALLER index
(`∀ m < n`). The `▷` lives in the OBSERVATION (`CoApproxC_le`): a left machine step spends one budget
unit (`convergesC_le_step`), so the reduct is observed one-step-LATER. At `n=0` the goal is vacuous
(`CoApproxC_le 0`). This is the index-RAISING the μ-unfold / resume seams use (replacing the old
blanket `Crel_mono`, which is FALSE under metering). Same proof as the `CrelExp` PoC (§B.0a), now over
the real `Crel`/`Krel`; config level, so NO `K.length` refocus offset (the lr45 wall). -/
theorem Crel_head_step {n : Nat} {B : CTy Eff Mult} {e : Eff} {c₁ c₁' c₂ c₂' : Comp}
    (h₁ : CIStep c₁ c₁') (h₂ : CIStep c₂ c₂')
    (hlater : ∀ m, m < n → Crel m B e c₁' c₂') :
    Crel n B e c₁ c₂ := by
  rw [Crel]; intro K₁ K₂ hK hconv
  have hstep₁ : Source.step (K₁, c₁) = some (K₁, c₁') := h₁.1 K₁
  have hne₁ : ∀ v, (K₁, c₁) ≠ ([], Comp.ret v) := by intro v; simp [h₁.2 v]
  cases n with
  | zero => exact absurd hconv (not_convergesC_le_zero _)
  | succ k =>
      rw [convergesC_le_step hstep₁ hne₁] at hconv
      have hCk : Crel k B e c₁' c₂' := hlater k (Nat.lt_succ_self k)
      rw [Crel] at hCk
      have hKk : Krel k B e K₁ K₂ := Krel_mono (Nat.le_succ k) hK
      have hstep₂ : Source.step (K₂, c₂) = some (K₂, c₂') := h₂.1 K₂
      have hne₂ : ∀ v, (K₂, c₂) ≠ ([], Comp.ret v) := by intro v; simp [h₂.2 v]
      exact converges_anti_step hstep₂ hne₂ (hCk K₁ K₂ hKk hconv)


-- ◊4.5b: the EXPERIMENTAL `CrelExp`/`Crel_head_step_le` PoC (the make-or-break that validated the
-- config-level metered `▷` before the full rewire) is REMOVED — it is subsumed by the real
-- `Crel_head_step` above (single source of truth). The PoC's verdict (the config-level metering localizes
-- the offset; ADR-0041 alt-1 overturned) is recorded in ADR-0041 (amended `560ba82`).


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
  -- ◊4.5: consume the downward-closed body at the TOP index `j = n` (`le_refl n`) — the strongest body,
  -- which carries the original `Vrel n` return half unchanged (no weakening on the consume side).
  exact (hK n (le_refl n)).1 q A rfl v₁ v₂ hc₁ hc₂ hv


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
  -- ◊4.5b: `force (vthunk c) ↦ c` is a CIStep; the `▷`-guarded head-expansion needs the reducts related
  -- at every `m < n`, supplied by the U-clause `hc : ∀ j ≤ n, Crel j …` (Kripke) at `j = m ≤ n`.
  refine Crel_head_step (c₁' := c₁) (c₂' := c₂) ?_ ?_ (fun m hm => hc m (le_of_lt hm))
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
    (hK : Krel n B (φ₁ ⊔ φ₂) K₁ K₂)
    -- ◊4.5 Kripke continuation IH: the continuation relates at EVERY `j ≤ n` (not fixed at `n`), so
    -- the downward-closed return half can fire it at its OWN index `j` with the `Vrel j` it has — no
    -- Vrel-up. Stated at GENERAL `n` (stuck half vacuous at all j via `Srel 0 := False`), so the caller
    -- `compat_letC` needs NO `cases n`/`crel_zero` base. The caller supplies `hN` from the fundamental IH.
    (hN : ∀ j, j ≤ n → ∀ v₁ v₂, Val.Closed v₁ → Val.Closed v₂ → Vrel j A v₁ v₂ →
      Crel j B φ₂ (Comp.subst v₁ N₁') (Comp.subst v₂ N₂')) :
    Krel n (CTy.F q1 A) φ₁ (Frame.letF N₁' :: K₁) (Frame.letF N₂' :: K₂) := by
  rw [Krel]
  -- ◊4.5 downward-closed shape: `∀ j ≤ n, (return ∧ stuck ∧ arrow)`.
  intro j hj
  refine ⟨?_, ?_, ?_⟩
  · -- RETURN half: F q1 A = F q A' ⟹ q = q1, A' = A; the letF frame reduces to the continuation.
    intro q A' hEq v₁ v₂ hc₁ hc₂ hv
    rw [CTy.F.injEq] at hEq
    obtain ⟨rfl, rfl⟩ := hEq
    -- ◊4.5b: the `letF` REDUCE `(letF N::K, ret v) ↦ (K, N.subst v)` is ONE config step. Route the metered
    -- return-half through `coApproxC_le_anti_step` (the generic ▷-anti-reduction): the reduct relation at
    -- the DROPPED index `j-1` comes from `hN` (continuation IH) at `j-1`, with `Vrel`/`Krel` weakened.
    cases j with
    | zero => exact coApproxC_le_zero _ _
    | succ k =>
        refine coApproxC_le_anti_step (cfg₁' := (K₁, Comp.subst v₁ N₁')) (cfg₂' := (K₂, Comp.subst v₂ N₂'))
          rfl (by intro u; simp) rfl (by intro u; simp) ?_
        -- fire `hN` at index `k` (≤ n): weaken `Vrel (k+1) → Vrel k`, ambient `Krel (k+1) → Krel k → φ₂`.
        have hKk : Krel k B (φ₁ ⊔ φ₂) K₁ K₂ := Krel_mono (Nat.le_of_succ_le hj) hK
        have hKφ₂ : Krel k B φ₂ K₁ K₂ := Krel_eff_anti k B φ₂ (φ₁ ⊔ φ₂) K₁ K₂ le_sup_right hKk
        have hCrel := hN k (Nat.le_of_succ_le hj) v₁ v₂ hc₁ hc₂ (Vrel_mono (Nat.le_succ k) hv)
        rw [Crel] at hCrel
        exact hCrel K₁ K₂ hKφ₂
  · -- STUCK half: the Srel pair is an unhandled op under letF :: K — `ConvergesC_le j` is False, vacuous.
    intro c₁ c₂ hS
    -- ◊4.5 (Srel 0 := False): `j = 0` is vacuous (`hS : Srel 0 = False`). `j = k+1` is the REAL
    -- unhandled-op argument — `Srel (k+1)` forces `c₁ = up …`, never convergent under `letF :: K`.
    cases j with
    | succ k =>
        rw [Srel] at hS
        obtain ⟨ℓ, op, v₁, v₂, _, _, hc₁, _, _, _, _, _, hsp₁, _, _⟩ := hS
        intro hconv₁
        rw [hc₁] at hconv₁
        exact absurd hconv₁ (not_convergesC_le_up_splitNone (Frame.letF N₁' :: K₁) ℓ op v₁ hsp₁)
    | zero => exact absurd hS (by unfold Srel; exact not_false)
  · -- ARROW half: VACUOUS — the let-block returns at `F q1 A`, not an arrow type (`F ≠ arr`).
    intro q A' B' hEq
    exact absurd hEq (by simp)

/-- The `appF` frame-extension `Krel` lemma: extending a codomain-`Krel n B ε K₁ K₂` by an `appF v`
frame gives an arrow-`Krel n (arr q A B) ε (appF v₁::K₁) (appF v₂::K₂)` — for `Vrel`-related closed
args. The PEELING arrow clause (ADR-0038) makes this DIRECT: it just exposes the appF cap (w := v) +
the codomain remainder (K' := K), no recursion (the double-appF wall the extending form hit). Return
half vacuous (arr≠F), stuck half vacuous (unhandled op under appF::K). The engine of `compat_app`. -/
theorem krel_appF_intro {n : Nat} {q : Mult} {A : VTy Eff Mult} {B : CTy Eff Mult} {ε : Eff}
    {v₁ v₂ : Val} {K₁ K₂ : Stack}
    (hcv₁ : Val.Closed v₁) (hcv₂ : Val.Closed v₂) (hv : Vrel n A v₁ v₂)
    (hK : Krel n B ε K₁ K₂) :
    Krel n (CTy.arr q A B) ε (Frame.appF v₁ :: K₁) (Frame.appF v₂ :: K₂) := by
  rw [Krel]
  -- ◊4.5 downward-closed shape: `∀ j ≤ n, (return ∧ stuck ∧ arrow)`. General `n` (stuck halves vacuous
  -- at all j). The arrow half needs `Vrel j` + `Krel j B` from the `n`-hyps, both DOWNWARD (Vrel_mono /
  -- Krel_mono) — no Vrel-UP, no wall.
  intro j hj
  refine ⟨?_, ?_, ?_⟩
  · intro q' A' hEq; exact absurd hEq (by simp)   -- return half: arr ≠ F, vacuous.
  · -- stuck half: an Srel pair under appF::K is an unhandled op (splitAt = none) — never converges.
    intro c₁ c₂ hS
    -- ◊4.5 (Srel 0 := False): `j = 0` vacuous; `j = k+1` is the real unhandled-op argument.
    cases j with
    | succ k =>
        rw [Srel] at hS
        obtain ⟨ℓ, op, w₁, w₂, _, _, hc₁, _, _, _, _, _, hsp₁, _, _⟩ := hS
        intro hconv₁; rw [hc₁] at hconv₁
        exact absurd hconv₁ (not_convergesC_le_up_splitNone (Frame.appF v₁ :: K₁) ℓ op w₁ hsp₁)
    | zero => exact absurd hS (by unfold Srel; exact not_false)
  · -- arrow half (peeling): the cap IS appF v, the remainder IS K — supply them at index `j`.
    intro q' A' B' hEq
    obtain ⟨rfl, rfl, rfl⟩ : q = q' ∧ A = A' ∧ B = B' := by
      rw [CTy.arr.injEq] at hEq; exact ⟨hEq.1, hEq.2.1, hEq.2.2⟩
    -- ◊4.5: needs `Vrel j A v₁ v₂` + `Krel j B ε K₁ K₂` at `j ≤ n+1`. `Krel_mono hj hK` gives the second;
    -- `Vrel_mono hj hv` gives the first — Vrel-down is now STRUCTURAL (Vrel U-clause ∀j≤n). Wall dissolved.
    exact ⟨v₁, v₂, K₁, K₂, rfl, rfl, hcv₁, hcv₂, Vrel_mono hj hv, Krel_mono hj hK⟩

/-- The `letC` compatibility core (`compat_letC`): a `Crel` for `M` (the bound computation, at its
returner type `F q1 A` and effect `φ₁`) plus a continuation relation `hN` (the IH for `N`: for every
closed `Vrel`-related bound value, the substituted continuations are `Crel`-related at `(B, φ₂)`) give
`Crel` for the whole `letC` at the joined effect `φ₁ ⊔ φ₂`. The engine is the definitional REFOCUS
`plug K (letC M N') = plug (letF N' :: K) M` (`plug_cons`), turning the goal into running `M` under the
`letF`-extended stacks, which `krel_letF` shows `Krel`-related at `(F q1 A, φ₁)`. The fundamental
induction supplies `hN` via `closeC_subst_comm` + `closeC_letC` (`Nᵢ'.subst v = closeC δᵢ (N.subst v)`
= the IH instance `closeC (v::δᵢ) N`). ◊4.5: `n = 0` is covered by the single argument (`krel_letF` at
general `n`), no `crel_zero` base. -/
theorem compat_letC {n : Nat} {q1 : Mult} {A : VTy Eff Mult} {B : CTy Eff Mult} {φ₁ φ₂ : Eff}
    {M₁ M₂ N₁' N₂' : Comp}
    (hM : Crel n (CTy.F q1 A) φ₁ M₁ M₂)
    -- ◊4.5 Kripke continuation: relate the continuation at EVERY `j ≤ n` (the fundamental IH gives this).
    (hN : ∀ j, j ≤ n → ∀ v₁ v₂, Val.Closed v₁ → Val.Closed v₂ → Vrel j A v₁ v₂ →
      Crel j B φ₂ (Comp.subst v₁ N₁') (Comp.subst v₂ N₂')) :
    Crel n B (φ₁ ⊔ φ₂) (Comp.letC M₁ N₁') (Comp.letC M₂ N₂') := by
  -- ◊4.5: NO `cases n`/`crel_zero` base — `krel_letF` at GENERAL `n` makes the single argument cover
  -- `n = 0` (the stuck halves are vacuous at all j; the index-free `CoApprox` is discharged the same way).
  rw [Crel]
  intro K₁ K₂ hK
  -- ◊4.5b CONFIG REFOCUS: `(K, letC M N') ↦ (letF N'::K, M)` is one PUSH config step (non-dropping
  -- `coApproxC_le_reduce`); the letF-extended stacks are `Krel`-related at `(F q1 A, φ₁)` (`krel_letF`),
  -- so `hM` (related at the arrow type, index `n`) discharges the reduct.
  refine coApproxC_le_reduce (cfg₁' := (Frame.letF N₁' :: K₁, M₁)) (cfg₂' := (Frame.letF N₂' :: K₂, M₂))
    rfl (by intro u; simp) rfl (by intro u; simp) ?_
  have hKletF := krel_letF (q1 := q1) hK hN
  rw [Crel] at hM
  exact hM (Frame.letF N₁' :: K₁) (Frame.letF N₂' :: K₂) hKletF

/-- The `app` compatibility core (`compat_app`): `Crel`-related arrow computations applied to
`Vrel`-related closed args give `Crel`-related results. REFOCUS `plug K (app M v) = plug (appF v::K) M`
(`plug_cons`), then run `M` (related at the arrow type) through the `appF`-extended stacks, which
`krel_appF_intro` shows `Krel`-related at `(arr q A B, φ)`. ◊4.5: `n=0` covered by the single argument. -/
theorem compat_app {n : Nat} {q : Mult} {A : VTy Eff Mult} {B : CTy Eff Mult} {φ : Eff}
    {M₁ M₂ : Comp} {v₁ v₂ : Val}
    (hM : Crel n (CTy.arr q A B) φ M₁ M₂)
    (hcv₁ : Val.Closed v₁) (hcv₂ : Val.Closed v₂) (hv : Vrel n A v₁ v₂) :
    Crel n B φ (Comp.app M₁ v₁) (Comp.app M₂ v₂) := by
  -- ◊4.5: NO `cases n`/`crel_zero` — `krel_appF_intro` at general `n` covers `n = 0`.
  rw [Crel]
  intro K₁ K₂ hK
  -- ◊4.5b CONFIG REFOCUS: `(K, app M v) ↦ (appF v::K, M)` is one PUSH config step (non-dropping); the
  -- appF-extended stacks are `Krel`-related at `(arr q A B, φ)` (`krel_appF_intro`), so `hM` discharges.
  refine coApproxC_le_reduce (cfg₁' := (Frame.appF v₁ :: K₁, M₁)) (cfg₂' := (Frame.appF v₂ :: K₂, M₂))
    rfl (by intro u; simp) rfl (by intro u; simp) ?_
  rw [Crel] at hM
  exact hM (Frame.appF v₁ :: K₁) (Frame.appF v₂ :: K₂) (krel_appF_intro hcv₁ hcv₂ hv hK)

/-- The `lam` compatibility core (`compat_lam`): two `lam`s relate at `arr q A B` when their bodies
relate at `(B, φ)` under every closed `Vrel`-related argument substituted at the binder. The PEELING
arrow clause (ADR-0038) exposes any arrow-observation stack as `appF w`-capped with a codomain-`Krel`
remainder; `converges_appF_lam` β-reduces `plug (appF w::K') (lam M') ⟺ plug K' (M'.subst w)`, and the
body relation discharges it. (Non-appF stacks can't converge on a `lam` — peeling never produces them.)
◊4.5: covered uniformly (no `crel_zero` base — the arrow half is consumed at the top index). -/
theorem compat_lam {n : Nat} {q : Mult} {A : VTy Eff Mult} {B : CTy Eff Mult} {φ : Eff}
    {M₁' M₂' : Comp}
    (hbody : ∀ w₁ w₂, Val.Closed w₁ → Val.Closed w₂ → Vrel n A w₁ w₂ →
      Crel n B φ (Comp.subst w₁ M₁') (Comp.subst w₂ M₂')) :
    Crel n (CTy.arr q A B) φ (Comp.lam M₁') (Comp.lam M₂') := by
  rw [Crel]
  intro K₁ K₂ hK
  -- the arrow-observation stack is appF-capped (peeling): expose the cap + codomain remainder.
  rw [Krel] at hK
  -- ◊4.5: consume the arrow half at the TOP index `j = n` (downward-closed body, strongest at `n`).
  obtain ⟨w₁, w₂, K₁', K₂', rfl, rfl, hcw₁, hcw₂, hw, hKrem⟩ := (hK n (le_refl n)).2.2 q A B rfl
  -- ◊4.5b: β `(appF w::K', lam M') ↦ (K', M'.subst w)` is one config step; the body IH gives the reduct
  -- related at the SAME index `n`, so the NON-dropping `coApproxC_le_reduce` discharges it.
  refine coApproxC_le_reduce (cfg₁' := (K₁', Comp.subst w₁ M₁')) (cfg₂' := (K₂', Comp.subst w₂ M₂'))
    rfl (by intro u; simp) rfl (by intro u; simp) ?_
  have hb := hbody w₁ w₂ hcw₁ hcw₂ hw
  rw [Crel] at hb
  exact hb K₁' K₂' hKrem

/-- The `handleF (throws ℓ)` frame-extension `Krel` lemma: extending a `Krel n (F q A) φ K₁ K₂` by a
`throws ℓ` handler frame gives `Krel n (F q A) e (handleF (throws ℓ)::K₁) (handleF (throws ℓ)::K₂)` for
any body effect `e`. KEY INSIGHT (the same-M / no-handled-op-clause-needed argument): Krel quantifies
ONLY over `ret` (return half) and `splitAt = none` ops (stuck half = UNHANDLED). The op the throws frame
CATCHES (`ℓ`'s raise) is neither — it's consumed by the MACHINE's dispatch inside the body's run, NOT
observed by this stack relation. So no "handled-op clause" is needed:
  • RETURN half: `handleF h :: K, ret v ↦ K, ret v` (identity return, ADR-0023 Q6) → `converges_handleF_ret`
    reduces to the ambient Krel return half.
  • STUCK half: an `Srel` pair under `handleF::K` has `splitAt = none` (unhandled) → never converges
    (`not_converges_up_splitNone`) → vacuous.
  • ARROW half: vacuous (`F q A ≠ arr`).
This is the THROWS fragment — zero-shot abort, ▷-free (no resume). state/transaction RESUME is the
follow-up (needs the Kripke/▷ reshape). -/
theorem krel_handleF_throws {n : Nat} {q : Mult} {A : VTy Eff Mult} {e φ : Eff} {ℓ : Label}
    {K₁ K₂ : Stack} (hK : Krel n (CTy.F q A) φ K₁ K₂) :
    Krel n (CTy.F q A) e (Frame.handleF (Handler.throws ℓ) :: K₁)
                         (Frame.handleF (Handler.throws ℓ) :: K₂) := by
  rw [Krel]
  -- ◊4.5 downward-closed shape: `∀ j ≤ n, (return ∧ stuck ∧ arrow)`. General `n`. The ambient `hK` is
  -- consumed at the MATCHING index `j` (return half), so the `Vrel j` we receive feeds `hK`'s `Vrel j`
  -- return half directly — no Vrel-up (the throws frame relays the ambient return at every `j`).
  rw [Krel] at hK
  intro j hj
  refine ⟨?_, ?_, ?_⟩
  · -- RETURN half: the handler frame returns identically (`handleF h::K, ret v ↦ K, ret v`, one config
    -- step); ambient `Krel` return half gives the reduct related at the SAME index `j` (non-dropping).
    intro q' A' hEq v₁ v₂ hcv₁ hcv₂ hv
    refine coApproxC_le_reduce (cfg₁' := (K₁, Comp.ret v₁)) (cfg₂' := (K₂, Comp.ret v₂))
      rfl (by intro u; simp) rfl (by intro u; simp) ?_
    exact (hK j hj).1 q' A' hEq v₁ v₂ hcv₁ hcv₂ hv
  · -- STUCK half: the Srel pair is an unhandled op under handleF::K — `ConvergesC_le j` is False, vacuous.
    intro c₁ c₂ hS
    -- ◊4.5 (Srel 0 := False): `j = 0` vacuous; `j = k+1` is the real unhandled-op argument.
    cases j with
    | succ k =>
        rw [Srel] at hS
        obtain ⟨ℓ', op, v₁, v₂, _, _, hc₁, _, _, _, _, _, hsp₁, _, _⟩ := hS
        intro hconv₁
        rw [hc₁] at hconv₁
        exact absurd hconv₁
          (not_convergesC_le_up_splitNone (Frame.handleF (Handler.throws ℓ) :: K₁) ℓ' op v₁ hsp₁)
    | zero => exact absurd hS (by unfold Srel; exact not_false)
  · -- ARROW half: VACUOUS — F q A ≠ arr.
    intro q' A' B' hEq; exact absurd hEq (by simp)

/-- ◊4.5 RESUME INFRA: the `handleF h` frame-extension `Krel` lemma GENERALIZED to ANY handler `h`
(the `krel_handleF_throws` argument is handler-AGNOSTIC). KEY INSIGHT (unchanged from throws): `Krel`'s
stuck-half quantifies ONLY over `Srel` pairs, which carry `splitAt (handleF h :: K) = none` — i.e. ops
the WHOLE extended stack leaves UNHANDLED. The op a `state`/`transaction` frame CATCHES (`get`/`put`/
`newTVar`/…) has `splitAt ≠ none`, so it never appears in the `Srel` premise; it is consumed by the
MACHINE's dispatch inside the body's run, NOT observed by this stack relation. So NO resume reasoning is
needed at the `Krel` level — the `Srel` RESUME clause is consumed elsewhere (in `crel_fund`'s body
relatedness), not here. The three halves hold for every `h`:
  • RETURN half: `handleF h :: K, ret v ↦ K, ret v` (identity return, ADR-0023 Q6) → `converges_handleF_ret`.
  • STUCK half: an `Srel` pair under `handleF h::K` has `splitAt = none` → never converges
    (`not_converges_up_splitNone`) → vacuous. Handler-agnostic (uses only the stack + the none-split).
  • ARROW half: vacuous (`F q A ≠ arr`).
EnvRel-INDEPENDENT (a pure stack/handler lemma — the build arbitrates this independence). -/
theorem krel_handleF {n : Nat} {q : Mult} {A : VTy Eff Mult} {e φ : Eff} {h : Handler}
    {K₁ K₂ : Stack} (hK : Krel n (CTy.F q A) φ K₁ K₂) :
    Krel n (CTy.F q A) e (Frame.handleF h :: K₁) (Frame.handleF h :: K₂) := by
  rw [Krel]; rw [Krel] at hK
  intro j hj
  refine ⟨?_, ?_, ?_⟩
  · -- RETURN half: the handler frame returns identically (any h, one config step); ambient `Krel` return
    -- gives the reduct related at the SAME index `j` (non-dropping `coApproxC_le_reduce`).
    intro q' A' hEq v₁ v₂ hcv₁ hcv₂ hv
    refine coApproxC_le_reduce (cfg₁' := (K₁, Comp.ret v₁)) (cfg₂' := (K₂, Comp.ret v₂))
      rfl (by intro u; simp) rfl (by intro u; simp) ?_
    exact (hK j hj).1 q' A' hEq v₁ v₂ hcv₁ hcv₂ hv
  · -- STUCK half: the Srel pair is an op the WHOLE handleF::K stack leaves unhandled — never converges.
    intro c₁ c₂ hS
    cases j with
    | succ k =>
        rw [Srel] at hS
        obtain ⟨ℓ', op, v₁, v₂, _, _, hc₁, _, _, _, _, _, hsp₁, _, _⟩ := hS
        intro hconv₁
        rw [hc₁] at hconv₁
        exact absurd hconv₁ (not_convergesC_le_up_splitNone (Frame.handleF h :: K₁) ℓ' op v₁ hsp₁)
    | zero => exact absurd hS (by unfold Srel; exact not_false)
  · -- ARROW half: VACUOUS — F q A ≠ arr.
    intro q' A' B' hEq; exact absurd hEq (by simp)

/-- ◊4.5 RESUME INFRA: `krel_handleF` specialized to a `state ℓ s` frame (the resumptive analogue of
`krel_handleF_throws`). The resume seam (`Srel` output `Crel`) is NOT consumed here — see `krel_handleF`'s
docstring: the `get`/`put` ops this frame catches never enter the `Krel` stuck-half. -/
theorem krel_handleF_state {n : Nat} {q : Mult} {A : VTy Eff Mult} {e φ : Eff} {ℓ : Label} {s : Val}
    {K₁ K₂ : Stack} (hK : Krel n (CTy.F q A) φ K₁ K₂) :
    Krel n (CTy.F q A) e (Frame.handleF (Handler.state ℓ s) :: K₁)
                         (Frame.handleF (Handler.state ℓ s) :: K₂) :=
  krel_handleF hK

/-- ◊4.5 RESUME INFRA: `krel_handleF` specialized to a `transaction ℓ Θ` frame (the multi-cell resumptive
analogue). Same handler-agnostic argument — the `newTVar`/`readTVar`/`writeTVar` ops this frame catches
never enter the `Krel` stuck-half, so no heap/resume reasoning is needed at the stack-relation level. -/
theorem krel_handleF_transaction {n : Nat} {q : Mult} {A : VTy Eff Mult} {e φ : Eff} {ℓ : Label}
    {Θ : Store} {K₁ K₂ : Stack} (hK : Krel n (CTy.F q A) φ K₁ K₂) :
    Krel n (CTy.F q A) e (Frame.handleF (Handler.transaction ℓ Θ) :: K₁)
                         (Frame.handleF (Handler.transaction ℓ Θ) :: K₂) :=
  krel_handleF hK

/-- The `handleThrows` compatibility core (`compat_handleThrows`): a body `Crel`-related at its effect
`e` (the IH for `M`) gives the `handle (throws ℓ) M` block `Crel`-related at the discharged effect `φ`.
REFOCUS `plug K (handle (throws ℓ) M) = plug (handleF (throws ℓ)::K) M` (`plug_cons`), then run `M`
through the handler-extended stacks, which `krel_handleF_throws` shows `Krel`-related. The handled raise
(abort) is consumed by the machine inside M's run — no Srel needed (the same-M self-relation observes it
through the IH's biorthogonality). ▷-free. -/
theorem compat_handleThrows {n : Nat} {q : Mult} {A : VTy Eff Mult} {e φ : Eff} {ℓ : Label}
    {M₁ M₂ : Comp}
    (hM : Crel n (CTy.F q A) e M₁ M₂) :
    Crel n (CTy.F q A) φ (Comp.handle (Handler.throws ℓ) M₁) (Comp.handle (Handler.throws ℓ) M₂) := by
  -- ◊4.5: NO `cases n`/`crel_zero` — `krel_handleF_throws` at general `n` covers `n = 0`.
  rw [Crel]
  intro K₁ K₂ hK
  -- ◊4.5b CONFIG REFOCUS: `(K, handle h M) ↦ (handleF h::K, M)` is one PUSH config step (non-dropping);
  -- the handler-extended stacks are `Krel`-related (`krel_handleF_throws`), so `hM` discharges the reduct.
  refine coApproxC_le_reduce
    (cfg₁' := (Frame.handleF (Handler.throws ℓ) :: K₁, M₁))
    (cfg₂' := (Frame.handleF (Handler.throws ℓ) :: K₂, M₂))
    rfl (by intro u; simp) rfl (by intro u; simp) ?_
  rw [Crel] at hM
  exact hM (Frame.handleF (Handler.throws ℓ) :: K₁) (Frame.handleF (Handler.throws ℓ) :: K₂)
    (krel_handleF_throws hK)

/-- ◊4.5b The `handleState` compatibility core. STRUCTURALLY IDENTICAL to `compat_handleThrows` — the
RESUME mechanism is consumed by the MACHINE's dispatch inside `M`'s run (handler-agnostic), NOT observed
by the stack relation, so `krel_handleF_state` (= the handler-agnostic `krel_handleF`) discharges it
exactly like throws. The deferred-▷ worry was misplaced: the `Srel` resume clause is the OP-PRODUCER's
obligation (`up`), not the handler's. The state value `s` is arbitrary (the body IH is `s`-independent). -/
theorem compat_handleState {n : Nat} {q : Mult} {A : VTy Eff Mult} {e φ : Eff} {ℓ : Label} {s : Val}
    {M₁ M₂ : Comp}
    (hM : Crel n (CTy.F q A) e M₁ M₂) :
    Crel n (CTy.F q A) φ (Comp.handle (Handler.state ℓ s) M₁) (Comp.handle (Handler.state ℓ s) M₂) := by
  rw [Crel]
  intro K₁ K₂ hK
  refine coApproxC_le_reduce
    (cfg₁' := (Frame.handleF (Handler.state ℓ s) :: K₁, M₁))
    (cfg₂' := (Frame.handleF (Handler.state ℓ s) :: K₂, M₂))
    rfl (by intro u; simp) rfl (by intro u; simp) ?_
  rw [Crel] at hM
  exact hM (Frame.handleF (Handler.state ℓ s) :: K₁) (Frame.handleF (Handler.state ℓ s) :: K₂)
    (krel_handleF_state hK)

/-- ◊4.5b The `handleTransaction` compatibility core. As `compat_handleState`, the multi-cell resumptive
analogue — `krel_handleF_transaction` (handler-agnostic) discharges it; the heap `Θ` is arbitrary. -/
theorem compat_handleTransaction {n : Nat} {q : Mult} {A : VTy Eff Mult} {e φ : Eff} {ℓ : Label}
    {Θ : Store} {M₁ M₂ : Comp}
    (hM : Crel n (CTy.F q A) e M₁ M₂) :
    Crel n (CTy.F q A) φ (Comp.handle (Handler.transaction ℓ Θ) M₁)
                         (Comp.handle (Handler.transaction ℓ Θ) M₂) := by
  rw [Crel]
  intro K₁ K₂ hK
  refine coApproxC_le_reduce
    (cfg₁' := (Frame.handleF (Handler.transaction ℓ Θ) :: K₁, M₁))
    (cfg₂' := (Frame.handleF (Handler.transaction ℓ Θ) :: K₂, M₂))
    rfl (by intro u; simp) rfl (by intro u; simp) ?_
  rw [Crel] at hM
  exact hM (Frame.handleF (Handler.transaction ℓ Θ) :: K₁) (Frame.handleF (Handler.transaction ℓ Θ) :: K₂)
    (krel_handleF_transaction hK)

/-- The `case` compatibility core (`compat_case`): `Vrel`-related sum scrutinees force both `case`s to
the SAME branch (both `inl` or both `inr`, with `Vrel`-related payloads), and `case (inl v) … ↦ N₁[v]`
is a CIStep (stack-independent in-place reduction). So `Crel_head_step` reduces to the chosen branch's
continuation relation on the substituted payload. Scrutinee closedness (from the closed environment in
the fundamental induction) supplies the payload-closedness the branch IH needs. -/
theorem compat_case {n : Nat} {A B : VTy Eff Mult} {C : CTy Eff Mult} {φ : Eff}
    {w₁ w₂ : Val} {N₁₁ N₂₁ N₁₂ N₂₂ : Comp}
    (hw : Vrel n (VTy.sum A B) w₁ w₂) (hcw₁ : Val.Closed w₁) (hcw₂ : Val.Closed w₂)
    -- ◊4.5b KRIPKE continuation IHs (the head-step's `▷` needs the branch related at every `m < n`).
    (hN₁ : ∀ j, j ≤ n → ∀ v₁ v₂, Val.Closed v₁ → Val.Closed v₂ → Vrel j A v₁ v₂ →
      Crel j C φ (Comp.subst v₁ N₁₁) (Comp.subst v₂ N₁₂))
    (hN₂ : ∀ j, j ≤ n → ∀ v₁ v₂, Val.Closed v₁ → Val.Closed v₂ → Vrel j B v₁ v₂ →
      Crel j C φ (Comp.subst v₁ N₂₁) (Comp.subst v₂ N₂₂)) :
    Crel n C φ (Comp.case w₁ N₁₁ N₂₁) (Comp.case w₂ N₁₂ N₂₂) := by
  rw [Vrel] at hw
  rcases hw with ⟨u₁, u₂, rfl, rfl, hu⟩ | ⟨u₁, u₂, rfl, rfl, hu⟩
  · -- both inl: `case (inl u) ↦ N₁[u]` (CIStep); the ▷-head-step needs the branch at each `m < n`.
    refine Crel_head_step (c₁' := Comp.subst u₁ N₁₁) (c₂' := Comp.subst u₂ N₁₂) ?_ ?_
      (fun m hm => hN₁ m (le_of_lt hm) u₁ u₂ hcw₁.inl_inv hcw₂.inl_inv (Vrel_mono (le_of_lt hm) hu))
    · exact ⟨fun K => rfl, by intro v; simp⟩
    · exact ⟨fun K => rfl, by intro v; simp⟩
  · -- both inr: `case (inr u) ↦ N₂[u]` (CIStep).
    refine Crel_head_step (c₁' := Comp.subst u₁ N₂₁) (c₂' := Comp.subst u₂ N₂₂) ?_ ?_
      (fun m hm => hN₂ m (le_of_lt hm) u₁ u₂ hcw₁.inr_inv hcw₂.inr_inv (Vrel_mono (le_of_lt hm) hu))
    · exact ⟨fun K => rfl, by intro v; simp⟩
    · exact ⟨fun K => rfl, by intro v; simp⟩

/-- The `split` compatibility core (`compat_split`): a `Vrel`-related product scrutinee gives both
`split`s a `pair` with `Vrel`-related components, and `split (pair v w) N ↦ N[fst][shift snd]` is a
CIStep. The continuation relation `hN` (the two-binder IH, at `B :: A :: Γ`) is applied at the reduct's
exact substitution shape `Comp.subst v (Comp.subst (Val.shift w) N)`. Component closedness comes from the
closed scrutinee. -/
theorem compat_split {n : Nat} {A B : VTy Eff Mult} {C : CTy Eff Mult} {φ : Eff}
    {w₁ w₂ : Val} {N₁' N₂' : Comp}
    (hw : Vrel n (VTy.prod A B) w₁ w₂) (hcw₁ : Val.Closed w₁) (hcw₂ : Val.Closed w₂)
    -- ◊4.5b KRIPKE continuation IH (the head-step's `▷` needs the body related at every `m < n`).
    (hN : ∀ j, j ≤ n → ∀ a₁ a₂ b₁ b₂, Val.Closed a₁ → Val.Closed a₂ → Val.Closed b₁ → Val.Closed b₂ →
      Vrel j A a₁ a₂ → Vrel j B b₁ b₂ →
      Crel j C φ (Comp.subst a₁ (Comp.subst (Val.shift b₁) N₁'))
                 (Comp.subst a₂ (Comp.subst (Val.shift b₂) N₂'))) :
    Crel n C φ (Comp.split w₁ N₁') (Comp.split w₂ N₂') := by
  rw [Vrel] at hw
  obtain ⟨a₁, a₂, b₁, b₂, rfl, rfl, ha, hb⟩ := hw
  obtain ⟨hca₁, hcb₁⟩ := hcw₁.pair_inv
  obtain ⟨hca₂, hcb₂⟩ := hcw₂.pair_inv
  -- `split (pair a b) N ↦ N[a][shift b]` (CIStep); the ▷-head-step needs the body at each `m < n`.
  refine Crel_head_step
    (c₁' := Comp.subst a₁ (Comp.subst (Val.shift b₁) N₁'))
    (c₂' := Comp.subst a₂ (Comp.subst (Val.shift b₂) N₂')) ?_ ?_
    (fun m hm => hN m (le_of_lt hm) a₁ a₂ b₁ b₂ hca₁ hca₂ hcb₁ hcb₂
      (Vrel_mono (le_of_lt hm) ha) (Vrel_mono (le_of_lt hm) hb))
  · exact ⟨fun K => rfl, by intro v; simp⟩
  · exact ⟨fun K => rfl, by intro v; simp⟩

/-- ◊4.5b `unfold` of `Vrel`-related folds, over the METERED observation. `Vrel n (mu A)` gives the
fold SHAPE at every `n` plus the payloads `Vrel`-related at the UNROLLED type at every `j < n` (the μ
`▷`-guard). `unfold (fold w) ↦ ret w` is a CIStep, so the `▷`-guarded `Crel_head_step` reduces the goal
to `crel_ret` on the payload at each DROPPED index `m < n` — exactly what the μ-clause's `∀ j < n`
supplies. The conclusion is `Crel n` from `Vrel n` (index-MATCHED, no off-by-one): the metered observation
spends the step, so at `n=0` the goal is vacuous and the floor closes with NO payload (the ADR-0041 wall,
dissolved). This is the textbook iso-recursive step-indexing treatment (ahmed-esop06 / Appel-McAllester):
the recursive-type elimination costs one logical step, now PAID by the metered `▷`. -/
theorem crel_unfold {n : Nat} {A : VTy Eff Mult} {e : Eff} {w₁ w₂ : Val}
    (hcw₁ : Val.Closed w₁) (hcw₂ : Val.Closed w₂) (hv : Vrel n (VTy.mu A) w₁ w₂) :
    Crel n (CTy.F 1 (VTy.unrollMu A)) e (Comp.unfold w₁) (Comp.unfold w₂) := by
  rw [Vrel] at hv
  obtain ⟨u₁, u₂, rfl, rfl, hu⟩ := hv
  -- the ▷-head-step needs `Crel m (ret u₁) (ret u₂)` at each `m < n`, from `crel_ret` on the μ-payload
  -- `hu m : Vrel m (unrollMu A) u₁ u₂`. At `n=0` the `∀ m < 0` is vacuous and the goal `Crel 0` is too.
  refine Crel_head_step (c₁' := Comp.ret u₁) (c₂' := Comp.ret u₂) ?_ ?_
    (fun m hm => crel_ret hcw₁.fold_inv hcw₂.fold_inv (hu m hm))
  · exact ⟨fun K => rfl, by intro v; simp⟩
  · exact ⟨fun K => rfl, by intro v; simp⟩



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

◊4.5b: `krel_refl` PROVEN below the mutual `crel_fund` block (it CALLS `crel_fund` for the frame
continuations' self-relation, so it must follow it). -/
/-- A well-typed value is `ScopedIn Γ.length` (`HasVTy.shift_closed`: shifting at a cutoff `≥ Γ.length`
is the identity). The bridge from the typing derivation to the syntactic scope bound that
`closeV_closed_scoped` consumes. -/
theorem HasVTy.scopedIn {γ : GradeVec Mult} {Γ : TyCtx Eff Mult} {v : Val} {A : VTy Eff Mult}
    (h : HasVTy γ Γ v A) : Val.ScopedIn Γ.length v := fun k hk => h.shift_closed k hk


/-! ## B.5 The mutual fundamental theorem (`vrel_fund` / `crel_fund`)

The capstone: a well-typed value/computation relates to ITSELF under every pair of `Vrel`-related
closing environments. Proven by mutual induction over the typing derivation (`HasCTy.rec` with both
motives, mirroring `Metatheory.HasCTy.subst_gen`), each case dispatching to its compat core:

  value side (`vrel_fund`):  vunit/vint (BaseRel), vvar (`closeV_vvar` + `EnvRel.vrel_at`),
                             vthunk (→ `crel_fund` IH), inl/inr/pair/fold (structural).
  comp side  (`crel_fund`):  ret (→ `crel_ret`), letC (→ `compat_letC`), force (→ `crel_force`),
                             lam (→ `compat_lam`), app (→ `compat_app`), case (→ `compat_case`),
                             split (→ `compat_split`), unfold (→ `crel_unfold` — μ-floor CLOSED ◊4.5b),
                             handleThrows/State/Transaction (→ `compat_handle*` — CLOSED ◊4.5b, the
                             handler-agnostic `krel_handleF`), up (the op-PRODUCER — OPEN, see its case).

STATUS (◊4.5b): all CLOSED except `up` (the resume-PRODUCER wall — `Krel`/`Srel` lack handler/row
compatibility for the `splitAt = some` half) and `krel_refl` (the `lr_sound` capstone interface).
`lr_fundamental` carries `sorryAx` from exactly these two until they close. -/

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
      -- ◊4.5 (Vrel U-clause ∀j≤n): supply `Crel j` at EVERY `j ≤ n` via the IH `crel_fund` at index `j`
      -- on the `EnvRel_mono`-weakened environment — Kripke, no Crel-down needed.
      exact ⟨closeC δ₁ M, closeC δ₂ M, rfl, rfl,
        fun j hjn => crel_fund hM j δ₁ δ₂ (EnvRel_mono hjn hδ)⟩
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
      -- μ intro (◊4.5 ROUTE 1). `Vrel n (mu A) := ∃ fold, ∀ j < n, Vrel j (unrollMu A)`. The fold SHAPE
      -- holds at every n (incl. the floor); for each `j < n` the IH `vrel_fund hw` at index `j` on the
      -- `EnvRel_mono`-weakened env supplies the unrolled payload — Kripke, the `▷`-guard is `∀ j <`.
      rw [closeV_fold, closeV_fold, Vrel]
      exact ⟨_, _, rfl, rfl,
        fun j hjn => vrel_fund hw j δ₁ δ₂ (EnvRel_mono (Nat.le_of_lt hjn) hδ)⟩

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
      -- ◊4.5 Kripke continuation: at EVERY `j ≤ n`, on the `EnvRel_mono`-weakened env. (closeC_subst_comm
      -- threads the bound value through the binder; the extended EnvRel at `j` uses `Vrel j`.)
      intro j hjn v₁ v₂ hcv₁ hcv₂ hvrel
      rw [closeC_subst_comm hδ.closed_left hcv₁, closeC_subst_comm hδ.closed_right hcv₂]
      have hδ' : EnvRel j (A :: Γ) (v₁ :: δ₁) (v₂ :: δ₂) := by
        rw [EnvRel]; exact ⟨hcv₁, hcv₂, hvrel, EnvRel_mono hjn hδ⟩
      have := crel_fund hN j (v₁ :: δ₁) (v₂ :: δ₂) hδ'
      rwa [show closeC (v₁ :: δ₁) N = closeC δ₁ (Comp.subst v₁ N) from rfl,
           show closeC (v₂ :: δ₂) N = closeC δ₂ (Comp.subst v₂ N) from rfl] at this
  | @force _ _ v φ B hv =>
      intro n δ₁ δ₂ hδ
      rw [closeC_force, closeC_force]
      exact crel_force (vrel_fund hv n δ₁ δ₂ hδ)
  | @lam _ _ M φ q A B hM =>
      intro n δ₁ δ₂ hδ
      rw [closeC_lam, closeC_lam]
      -- body relation at A :: Γ: (closeCUnderBinders 1 δᵢ M).subst w = closeC δᵢ (M.subst w)
      -- = closeC (w::δᵢ) M (closeC_subst_comm); IH on M at the extended EnvRel.
      refine compat_lam ?_
      intro w₁ w₂ hcw₁ hcw₂ hw
      rw [closeC_subst_comm hδ.closed_left hcw₁, closeC_subst_comm hδ.closed_right hcw₂]
      have hδ' : EnvRel n (A :: Γ) (w₁ :: δ₁) (w₂ :: δ₂) := by
        rw [EnvRel]; exact ⟨hcw₁, hcw₂, hw, hδ⟩
      have := crel_fund hM n (w₁ :: δ₁) (w₂ :: δ₂) hδ'
      rwa [show closeC (w₁ :: δ₁) M = closeC δ₁ (Comp.subst w₁ M) from rfl,
           show closeC (w₂ :: δ₂) M = closeC δ₂ (Comp.subst w₂ M) from rfl] at this
  | @app _ _ _ _ M v φ q A B hM hv _ =>
      intro n δ₁ δ₂ hδ
      rw [closeC_app, closeC_app]
      have hscv₁ : Val.Closed (closeV δ₁ v) :=
        closeV_closed_scoped hδ.closed_left (by have := hv.scopedIn; rwa [hδ.length_left])
      have hscv₂ : Val.Closed (closeV δ₂ v) :=
        closeV_closed_scoped hδ.closed_right (by have := hv.scopedIn; rwa [hδ.length_right])
      exact compat_app (crel_fund hM n δ₁ δ₂ hδ) hscv₁ hscv₂ (vrel_fund hv n δ₁ δ₂ hδ)
  | @case _ _ _ _ v N₁ N₂ φ q A B C hv hN₁ hN₂ _ =>
      intro n δ₁ δ₂ hδ
      rw [closeC_case, closeC_case]
      have hscv₁ : Val.Closed (closeV δ₁ v) :=
        closeV_closed_scoped hδ.closed_left (by have := hv.scopedIn; rwa [hδ.length_left])
      have hscv₂ : Val.Closed (closeV δ₂ v) :=
        closeV_closed_scoped hδ.closed_right (by have := hv.scopedIn; rwa [hδ.length_right])
      -- ◊4.5b KRIPKE: the branch IHs fire at each `j ≤ n` on the `EnvRel_mono`-weakened env.
      refine compat_case (vrel_fund hv n δ₁ δ₂ hδ) hscv₁ hscv₂ ?_ ?_
      · intro j hj u₁ u₂ hcu₁ hcu₂ hu
        rw [closeC_subst_comm hδ.closed_left hcu₁, closeC_subst_comm hδ.closed_right hcu₂]
        have hδ' : EnvRel j (A :: Γ) (u₁ :: δ₁) (u₂ :: δ₂) := by
          rw [EnvRel]; exact ⟨hcu₁, hcu₂, hu, EnvRel_mono hj hδ⟩
        exact crel_fund hN₁ j (u₁ :: δ₁) (u₂ :: δ₂) hδ'
      · intro j hj u₁ u₂ hcu₁ hcu₂ hu
        rw [closeC_subst_comm hδ.closed_left hcu₁, closeC_subst_comm hδ.closed_right hcu₂]
        have hδ' : EnvRel j (B :: Γ) (u₁ :: δ₁) (u₂ :: δ₂) := by
          rw [EnvRel]; exact ⟨hcu₁, hcu₂, hu, EnvRel_mono hj hδ⟩
        exact crel_fund hN₂ j (u₁ :: δ₁) (u₂ :: δ₂) hδ'
  | @split _ _ _ _ v N φ q A B C hv hN _ =>
      intro n δ₁ δ₂ hδ
      rw [closeC_split, closeC_split]
      have hscv₁ : Val.Closed (closeV δ₁ v) :=
        closeV_closed_scoped hδ.closed_left (by have := hv.scopedIn; rwa [hδ.length_left])
      have hscv₂ : Val.Closed (closeV δ₂ v) :=
        closeV_closed_scoped hδ.closed_right (by have := hv.scopedIn; rwa [hδ.length_right])
      -- ◊4.5b KRIPKE: the body IH fires at each `j ≤ n` on the `EnvRel_mono`-weakened two-extended env.
      refine compat_split (vrel_fund hv n δ₁ δ₂ hδ) hscv₁ hscv₂ ?_
      -- continuation at B :: A :: Γ: the reduct `subst a (subst (shift b) (closeCUnderBinders 2 δ N))`
      -- = closeC δ (subst a (subst b N)) = closeC (b :: a :: δ) N (closeC_subst2_comm); IH at the
      -- two-extended env (snd=b at idx0, fst=a at idx1).
      intro j hj a₁ a₂ b₁ b₂ hca₁ hca₂ hcb₁ hcb₂ ha hb
      rw [closeC_subst2_comm hδ.closed_left hca₁ hcb₁, closeC_subst2_comm hδ.closed_right hca₂ hcb₂]
      have hδ' : EnvRel j (B :: A :: Γ) (b₁ :: a₁ :: δ₁) (b₂ :: a₂ :: δ₂) := by
        rw [EnvRel]; refine ⟨hcb₁, hcb₂, hb, ?_⟩; rw [EnvRel]; exact ⟨hca₁, hca₂, ha, EnvRel_mono hj hδ⟩
      have := crel_fund hN j (b₁ :: a₁ :: δ₁) (b₂ :: a₂ :: δ₂) hδ'
      rwa [show closeC (b₁ :: a₁ :: δ₁) N = closeC δ₁ (Comp.subst a₁ (Comp.subst b₁ N)) from rfl,
           show closeC (b₂ :: a₂ :: δ₂) N = closeC δ₂ (Comp.subst a₂ (Comp.subst b₂ N)) from rfl] at this
  | @unfold _ _ v A hv =>
      intro n δ₁ δ₂ hδ
      rw [closeC_unfold, closeC_unfold]
      -- μ elim. Split on the scrutinee's typing derivation:
      --   • `v = fold a`: the closure is `unfold (fold (closeV δ a))`, a CIStep to `ret (closeV δ a)`.
      --     `Crel_head_step` reduces to `crel_ret` on the payload `Vrel n (unrollMu A)` (= `vrel_fund ha`)
      --     — ▷-FREE, closes at EVERY `n` (the fold is syntactically present, no μ-clause index gate).
      --   • `v = vvar i`: the closure is `unfold δ[i]`. For `n = m+1` the env supplies the fold + payload
      --     (`crel_unfold` spends the step, `Crel_mono` re-raises). For `n = 0` it is the WALL (below).
      cases hv with
      | @fold _ _ a _ ha =>
          rw [closeV_fold, closeV_fold]
          have hsa₁ : Val.Closed (closeV δ₁ a) :=
            closeV_closed_scoped hδ.closed_left (by have := ha.scopedIn; rwa [hδ.length_left])
          have hsa₂ : Val.Closed (closeV δ₂ a) :=
            closeV_closed_scoped hδ.closed_right (by have := ha.scopedIn; rwa [hδ.length_right])
          -- ◊4.5b: `unfold (fold a) ↦ ret a` (CIStep); the ▷-head-step needs `Crel m (ret a) (ret a)` at
          -- each `m < n`, from `crel_ret` on `vrel_fund ha` at index `m` (EnvRel_mono-weakened). ▷-FREE in
          -- the sense that the fold is SYNTACTIC (no μ-clause index gate) — closes at EVERY `n` incl. 0.
          refine Crel_head_step (c₁' := Comp.ret (closeV δ₁ a)) (c₂' := Comp.ret (closeV δ₂ a))
            ⟨fun K => rfl, by intro u; simp⟩ ⟨fun K => rfl, by intro u; simp⟩
            (fun m hm => crel_ret hsa₁ hsa₂ (vrel_fund ha m δ₁ δ₂ (EnvRel_mono (le_of_lt hm) hδ)))
      | @vvar _ i _ hget =>
          have hsc₁ : Val.Closed (closeV δ₁ (Val.vvar i)) :=
            closeV_closed_scoped hδ.closed_left (by
              have := (HasVTy.vvar hget).scopedIn; rwa [hδ.length_left])
          have hsc₂ : Val.Closed (closeV δ₂ (Val.vvar i)) :=
            closeV_closed_scoped hδ.closed_right (by
              have := (HasVTy.vvar hget).scopedIn; rwa [hδ.length_right])
          -- ◊4.5b: the μ-FLOOR WALL DISSOLVED. The env supplies `Vrel n (mu A)` (= `vrel_fund` of the
          -- vvar), and the metered `crel_unfold` consumes it DIRECTLY at the goal index `n` — no
          -- `Crel_mono` re-raise (it's false now), no `cases n`. At `n=0` `crel_unfold`'s ▷-head-step is
          -- vacuous (the metered `Crel 0`), so the floor closes with NO payload — the reconciliation
          -- ADR-0041's plain-Nat proof said was impossible, now build-PROVEN over the metered observation.
          exact crel_unfold hsc₁ hsc₂ (vrel_fund (HasVTy.vvar hget) n δ₁ δ₂ hδ)
  | @up _ _ ℓ op v φ q A B hℓ hArg hRes hv =>
      -- ◊4.5b WALL (op-PRODUCER, the last ▷-case). `Crel n (F q B) φ (up ℓ op v₁') (up ℓ op v₂')` against an
      -- ARBITRARY `Krel`-stack. CASE on `splitAt K₁ ℓ op`:
      --   • `none` (stack leaves `(ℓ,op)` unhandled): `(K₁, up…)` is STUCK ⇒ `ConvergesC_le` False ⇒ the
      --     metered observation is VACUOUS — this half CLOSES (and is all `lr_sound`/`[]`-adequacy needs).
      --   • `some` (stack HANDLES it): `(K₁, up…)` dispatches/resumes — needs a `Krel`-level handler-
      --     COMPATIBILITY fact our `Krel`/`Srel` don't carry. TWO precise gaps (build-isolated):
      --       (i)  the `Srel` RESUME clause obligation `Crel k (plug K₁ (ret u)) (plug K₂ (ret u))` does NOT
      --            follow from `Krel`'s return half `CoApproxC_le k (K₁, ret u) (K₂, ret u)`: the resume
      --            RE-quantifies over fresh outer stacks (nested observation), the return half is direct.
      --       (ii) no `Krel` clause relates how two `Krel`-stacks DISPATCH the same op (row-discipline:
      --            a stack typed at row `φ ∋ ℓ` should leave `ℓ` unhandled — not encoded in `Krel`).
      --   Both stem from the SAME root: `Krel`/`Srel` lack the op-producer's handler/row compatibility.
      --   STOPPED + reported (the resume-composition wall). The 3 CONSUMER cases (handleThrows/State/Txn)
      --   ARE closed — `krel_handleF` is handler-agnostic; the producer is the genuinely-open one.
      intro n δ₁ δ₂ hδ; sorry
  | @handleThrows _ _ ℓ M e φ q A hArg hIface hM hsub =>
      -- throws is ▷-free (zero-shot abort, no resume): compat_handleThrows + closeC_handleThrows.
      intro n δ₁ δ₂ hδ
      rw [closeC_handleThrows, closeC_handleThrows]
      exact compat_handleThrows (crel_fund hM n δ₁ δ₂ hδ)
  | @handleState _ _ ℓ s₀ M e φ q S A _ _ _ _ _ hs hM hsub =>
      -- ◊4.5b: state-resume is handler-agnostic at the stack level (`krel_handleF_state`); the resume
      -- mechanism is consumed by the machine inside M's run, not the stack relation. So this closes
      -- exactly like throws. The stored state `closeV δ s₀` is closed (typing `HasVTy [] []`), but the
      -- core is `s`-generic so no closedness obligation is discharged here.
      intro n δ₁ δ₂ hδ
      rw [closeC_handleState, closeC_handleState]
      -- the stored state `s₀` is CLOSED (`HasVTy [] []`), so `closeV δᵢ s₀ = s₀` (same on both sides).
      have hcs₀ : Val.Closed s₀ := fun k => hs.shift_closed k (Nat.zero_le k)
      rw [closeV_closed hcs₀, closeV_closed hcs₀]
      exact compat_handleState (crel_fund hM n δ₁ δ₂ hδ)
  | @handleTransaction _ _ ℓ Θ₀ M e φ q A _ _ _ _ _ _ _ hcells hM hsub =>
      -- ◊4.5b: transaction-resume is handler-agnostic at the stack level (`krel_handleF_transaction`),
      -- the multi-cell analogue — closes like state/throws.
      intro n δ₁ δ₂ hδ
      rw [closeC_handleTransaction, closeC_handleTransaction]
      exact compat_handleTransaction (crel_fund hM n δ₁ δ₂ hδ)
end


/-! ## B.6 `krel_refl` — the `lr_sound` capstone (identity extension)

A well-typed stack is `Krel`-self-related. The IDENTITY INSTANCE of the fundamental theorem: each frame's
continuation self-relates via `crel_fund` (closed over a singleton env), so `krel_refl` CALLS `crel_fund`
and must follow it. Proven for `n+1` (the `nil` return half observes a RETURNER `F q A` — `krel_nil_succ`;
ADR-0038: the empty stack only observes returners, arrow-typed programs are `⊑`-vacuous). The frame cases
reuse the metered `krel_letF`/`krel_appF_intro`/`krel_handleF*`. Inherits `crel_fund`'s `up` sorryAx (a
continuation may `up`), so `lr_sound` is 0-sorry exactly when `up` closes — NOT independently. -/
theorem krel_refl {n : Nat} {C : Stack} {e eo : Eff} {B Co : CTy Eff Mult} {qo : Mult}
    {Ao : VTy Eff Mult} (hCo : Co = CTy.F qo Ao)
    (hC : HasStack C e B eo Co) : Krel (n + 1) B e C C := by
  -- `Co` (the whole-program answer type) is a RETURNER (ADR-0038: only returners are observed). This
  -- EXCLUDES arrow-`nil`: a `letF`/handler frame with an arrow continuation `B` over `K=[]` would force
  -- `Co = B = arr`, contradicting `hCo`. So `nil`'s focus type `B = Co` is always `F`-typed.
  induction hC with
  | @nil e' C' =>
      -- `B = C' = Co = F qo Ao` (`hCo`): the returner empty stack is `krel_nil_succ`.
      subst hCo; exact krel_nil_succ n _ _ _
  | @letF K N e₁ e₂ eo q qk A B Co hN hK ihK =>
      refine krel_letF (q1 := q) (ihK hCo) ?_
      -- continuation `N` (open at `[A]`) self-relates via `crel_fund` closed over `[v₁],[v₂]`.
      intro j _hj v₁ v₂ hcv₁ hcv₂ hv
      have hδ' : EnvRel j [A] [v₁] [v₂] := by
        rw [EnvRel]; exact ⟨hcv₁, hcv₂, hv, EnvRel_nil_iff j [] [] |>.mpr ⟨rfl, rfl⟩⟩
      have := crel_fund hN j [v₁] [v₂] hδ'
      rwa [show closeC [v₁] N = Comp.subst v₁ N from rfl,
           show closeC [v₂] N = Comp.subst v₂ N from rfl] at this
  | @appF K v e eo q A B Co hv hK ihK =>
      -- `appF v::K` at `arr q A B`: the arrow cap IS `appF v`, the remainder `K` (IH `ihK`). The closed
      -- arg `v` (`HasVTy [] []`) self-relates `Vrel`; `krel_appF_intro` assembles.
      have hcv : Val.Closed v := fun k => hv.shift_closed k (Nat.zero_le k)
      -- `Vrel (n+1) A v v` from `vrel_fund` on the closed `v` (closed over the empty env).
      have hvr : Vrel (n + 1) A v v := by
        have := vrel_fund hv (n + 1) [] [] (EnvRel_nil_iff (n + 1) [] [] |>.mpr ⟨rfl, rfl⟩)
        rwa [closeV_closed hcv] at this
      exact krel_appF_intro hcv hcv hvr (ihK hCo)
  | @handleF K ℓ e φ eo q A Co hArg hIface hsub hK ihK =>
      exact krel_handleF_throws (ihK hCo)
  | @stateF K ℓ s e φ eo q A S Co hg hgr hp hpr hIface hcs hsub hK ihK =>
      exact krel_handleF_state (ihK hCo)
  | @transactionF K ℓ Θ e φ eo q A Co _ _ _ _ _ _ _ hcells hsub hK ihK =>
      exact krel_handleF_transaction (ihK hCo)

end Bang
