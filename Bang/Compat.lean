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
import Bang.Spec

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

@[simp] theorem closeV_vthunk (δ : List Val) (c : Comp) :
    closeV δ (Val.vthunk c) = Val.vthunk (closeC δ c) := by
  induction δ generalizing c with
  | nil => rfl
  | cons v δ ih => simp only [closeV, closeC, Val.subst, Val.substFrom, Comp.subst]; exact ih _


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

end Bang
