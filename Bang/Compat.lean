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
(`Comp.subst v (ret w) = ret (Val.subst v w)`, definitional) through the fold. The BINDING formers
(`letC`/`lam`/`case`/`split`) are deferred — their commutation needs the shifted-environment form
(`Comp.substFrom 1 (shift v) N`), which for CLOSED fillers (the `EnvRel` invariant) collapses to
`Comp.substFrom 1 v N`; that closedness bridge is the next layer. -/

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


/-! ## B.2 The return / value-injection compat core (`crel_ret`)

`Crel`-relatedness of `ret v₁` and `ret v₂` follows from `Vrel`-relatedness of `v₁,v₂`: a
`Krel`-related stack pair, by its RETURN half, co-converges when plugged with `Vrel`-related returns.
This is the biorthogonal "values inject into computations" closure (Biernacki Fig 7, the `F q A`
clause of `Krel`). It is the `compat_ret` core and the engine of every `▷`-free leaf. -/

theorem crel_ret {n : Nat} {q : Mult} {A : VTy Eff Mult} {e : Eff} {v₁ v₂ : Val}
    (hv : Vrel n A v₁ v₂) : Crel n (CTy.F q A) e (Comp.ret v₁) (Comp.ret v₂) := by
  unfold Crel
  intro K₁ K₂ hK
  unfold Krel at hK
  -- the RETURN half of Krel fires on `Vrel n A v₁ v₂` at the returner type `F q A`.
  exact hK.1 q A rfl v₁ v₂ hv


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
