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


/-! ## B.1 The environment relation `EnvRel` (the open-term closure)

The fundamental theorem is `Crel n B e c c` — but the induction over `HasCTy` descends through
binders (`letC`/`lam`/`case`/`split`) into sub-derivations over a NON-empty `Γ`, where the
sub-computation is OPEN. The literal `c c` self-relation is then UNPROVABLE for the open sub-term: a
bare `vvar i` is not `Vrel`-related to itself (`Vrel n unit (vvar 0) (vvar 0)` demands
`vvar 0 = vunit`). So the faithful induction invariant closes the open term over a pair of
`Vrel`-RELATED substitution environments δ₁,δ₂ (Biernacki/Ahmed `G⟦Γ⟧`):

  shape: biernacki-popl18 §5.2 fundamental theorem (`G⟦Γ⟧η`); ahmed-esop06 closing substitution.

An environment is a `List Val` of CLOSED fillers (the CK focus is always closed). Applying it
(`closeC`) folds single `Comp.subst`s, innermost binder first. `EnvRel n Γ δ₁ δ₂` relates two
environments pointwise by `Vrel` at the corresponding `Γ` types.

STATUS: the frozen `lr_fundamental` (`Spec.lean`) is the `Γ = []` instance (empty environments,
`closeC [] c = c`). The `∀ Γ` form of the frozen statement is provable ONLY at `Γ = []` — surfaced to
the lead as a statement-shape concern (the open form needs the two-sided `c[δ₁] c[δ₂]` env-closed
conclusion, the ADR-0033-style tightening). -/

/-- Apply a closing environment δ to a computation: substitute index 0 with `δ[0]`, renumbering, then
recurse on the tail (each `Comp.subst` removes the nearest binder). `closeC [] c = c`. -/
def closeC : List Val → Comp → Comp
  | [],      c => c
  | v :: δ,  c => closeC δ (Comp.subst v c)

/-- Pointwise `Vrel`-relatedness of two closing environments at the context `Γ`. The two
environments have the same length as `Γ`; position `i` relates at type `Γ[i]`. -/
def EnvRel (n : Nat) : TyCtx Eff Mult → List Val → List Val → Prop
  | [],      [],        []        => True
  | A :: Γ', v₁ :: δ₁', v₂ :: δ₂' => Vrel n A v₁ v₂ ∧ EnvRel n Γ' δ₁' δ₂'
  | _,       _,         _         => False

/-- Apply a closing environment δ to a value (the value-level `closeC`). -/
def closeV : List Val → Val → Val
  | [],      v => v
  | u :: δ,  v => closeV δ (Val.subst u v)

@[simp] theorem closeC_nil (c : Comp) : closeC [] c = c := rfl
@[simp] theorem closeV_nil (v : Val) : closeV [] v = v := rfl

@[simp] theorem EnvRel_nil_iff (n : Nat) (δ₁ δ₂ : List Val) :
    EnvRel n ([] : TyCtx Eff Mult) δ₁ δ₂ ↔ δ₁ = [] ∧ δ₂ = [] := by
  cases δ₁ <;> cases δ₂ <;> simp [EnvRel]


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

end Bang
