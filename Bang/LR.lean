/-
  Bang/LR.lean — logical relations + observational equivalence + recovery.
  ─────────────────────────────────────────────────────────────────────────
    §5 helpers — Stack, BaseRel, asThunk, asReturner, raise (opArg/opRes → EffSig, ADR-0022)
    §5 ⊑ / ≈ — ctxApprox, ctxEquiv, Converges, CoApprox, Cxt, Cxt.plug
    §5 LR — Vrel, Srel, Krel, Crel (axioms; PROOF_ORDER #1 will replace)
    §6 helpers — seqComp, idComp, recover

  Theorem STATEMENTS (lr_sound, lr_fundamental, seq_unit, group_recovers)
  live in Bang/Spec.lean. -/

import Bang.Core
import Bang.Syntax
import Bang.Operational

namespace Bang

open Bang.EffectRow (Label)

variable {Eff  : Type} [Lattice Eff] [OrderBot Eff]
variable {Mult : Type} [CommSemiring Mult] [DecidableEq Mult]


/-! ## 5. Observational equivalence — `≈` is the spec notion of equality -/

-- §6 recovery algebra (used by recovery theorems in Spec.lean). The
-- `(seqComp, idComp, recover)` triple is the monoid/group structure on
-- computations from ADR-0018's Trinity table (`monoid ⇒ sequencing w/ identity`,
-- `group ⇒ rollback`). Concretized from the kernel's `Comp`, not hand-axiomatized.

/-- Sequencing (the monoid multiplication): run `c₁`, DISCARD its value, run `c₂`.
`Comp.shift c₂` lifts `c₂` over the `letC` binder so it ignores index 0 — this is
`c₁ ; c₂` (Biernacki/CBPV `let _ = c₁ in c₂`). With `idComp` (`ret unit`) it forms
a monoid: `seqComp (ret v) c` head-reduces `letC (ret v) (shift c) ↦ (shift c)[v] = c`
(subst-after-shift is the identity), which is exactly `seq_unit`'s LEFT-unit law. -/
def seqComp (c₁ c₂ : Comp) : Comp := Comp.letC c₁ (Comp.shift c₂)

/-- The monoid unit / identity computation: the pure no-op `ret ()`. -/
def idComp : Comp := Comp.ret Val.vunit

/-- Recovery (the group inverse, ADR-0018 `group ⇒ rollback`). The recovery
SCAFFOLD is the identity computation; the rollback CONTENT (`seqComp c (recover c) ≈
idComp`) is delivered by the `[AddGroup Eff]` group structure in `group_recovers`'s
proof, NOT by an inverse-effect TERM. Materializing an inverse as a `Comp` would need
either group-effect operations the kernel does not have or a 6th primitive (invariant
#5) — so the honest faithful def keeps the scaffold pure and lets the relation carry
the inversion. See FORK note in the report; revisit when group effects get term-level
operations. -/
def recover (_c : Comp) : Comp := idComp

-- Computation-to-computation contexts (for ctxApprox). SINGLE SOURCE OF TRUTH
-- (CLAUDE.md invariant): the kernel's CK frame stack `EvalCtx` with its `plug`
-- (`Bang/Operational.lean`) IS Biernacki's evaluation-context notion `ECont`/`E[·]`
-- (popl18 §3 Fig 1). `ctxApprox`/`ctxEquiv` quantify over these. `EvalCtx` is the
-- typed object `HasStack` (Syntax.lean §1.7) is already a judgement over, so reusing
-- it (rather than a parallel `Cxt`) keeps one context algebra everywhere.
abbrev Cxt : Type := EvalCtx
def Cxt.plug (C : Cxt) (c : Comp) : Comp := Bang.plug C c

/-- Observation: fuel-bounded convergence to a returned value. -/
def Converges (c : Comp) : Prop := ∃ fuel v, Source.eval fuel c = Result.done v

/-- THE SPEC NOTION. Contextual approximation (`⊑`) and equivalence (`≈`). -/
def ctxApprox (c₁ c₂ : Comp) : Prop :=
  ∀ C : Cxt, Converges (Cxt.plug C c₁) → Converges (Cxt.plug C c₂)
def ctxEquiv (c₁ c₂ : Comp) : Prop := ctxApprox c₁ c₂ ∧ ctxApprox c₂ c₁
infixl:50 " ⊑ " => ctxApprox
infixl:50 " ≈ " => ctxEquiv

/-- Termination of c₁ implies termination of c₂ (Biernacki's `Obs`, approx form). -/
def CoApprox (c₁ c₂ : Comp) : Prop := Converges c₁ → Converges c₂

/-! ### 5.0a‴ The step-bounded observation — the `▷` (later) modality (◊4.5b / ADR-0041)

The unbounded `CoApprox` cannot carry a `▷`: a machine head-step is observed by an index-PRESERVING
`Converges ↔ Converges` (the reduct co-converges at the SAME budget), so head-expansion cannot be
`▷`-guarded, and the μ-floor's `Crel 0` stays a real (non-vacuous) obligation through the inhabited
`Krel 0`. This is exactly ADR-0041's "unbounded biorthogonal observation + μ = vicious cycle".

The fix is Biernacki's `Obs` (popl18 Fig 7), whose left term is STEP-BOUNDED (`▷Obs` on every
left-reduction): we METER THE LEFT term's machine steps while leaving the right UNBOUNDED ("e₂ may
use any number of steps"). The bound IS the step index. Two facts make this discharge the μ-floor
WITHOUT touching `Krel_mono` (ADR-0041's `Krel 0`-inhabitation argument is sidestepped):
  • `ConvergesC_le 0 cfg = ∃ v, run 0 cfg = done v` — but `run 0 = oom` (Operational.lean), so this is
    FALSE, so `CoApprox_le 0` is VACUOUSLY TRUE ⇒ `Crel 0` is vacuous (the floor discharges, no payload).
  • the bound is downward-closed (`∀ j ≤ n` in `Krel`), so `Krel_mono` is still free.

DESIGN — config level, no refocus offset (the lr45 wall): the metered observation counts CONFIG steps
(`Config.run n (K, c)`), NOT `Source.eval` fuel on the plugged term. At config level a head-step is a
clean `±1` (`Config.run_step`), with NO `+K.length` `run_plug` offset — that offset (the lr45
"(j+1)+K.length refocus mismatch") never enters because `Krel`/`Crel`/`Srel` observe the FOCUSED
config `(K, c)`, not `plug K c`. The bridge to the frozen index-free `Converges` is `run_plug`, applied
ONCE at the `lr_sound` adequacy boundary (`converges_iff_exists_ConvergesC_le`). -/

/-- Step-bounded convergence of a CONFIG within `n` machine steps. Monotone in `n` (`run_done_add`).
`ConvergesC_le 0 _` is `False` (`run 0 = oom`), the fact that vacates the μ-floor. -/
def ConvergesC_le (n : Nat) (cfg : Config) : Prop := ∃ v, Config.run n cfg = Result.done v

/-- `run 0 = oom`, so 0-step convergence is empty — the floor-vacuity fact. -/
theorem not_convergesC_le_zero (cfg : Config) : ¬ ConvergesC_le 0 cfg := by
  rintro ⟨v, h⟩; rw [show Config.run 0 cfg = Result.oom from rfl] at h; exact absurd h (by simp)

/-- Monotone: convergence within `n` steps persists within any `m ≥ n` (`run_done_add`). -/
theorem ConvergesC_le.mono {n m : Nat} (hnm : n ≤ m) {cfg : Config}
    (h : ConvergesC_le n cfg) : ConvergesC_le m cfg := by
  obtain ⟨v, hv⟩ := h
  obtain ⟨k, rfl⟩ := Nat.le.dest hnm
  exact ⟨v, Config.run_done_add k n cfg v hv⟩

/-- THE step lemma (factored once). A non-terminal config `cfg` stepping to `cfg'` converges within
`n+1` steps iff `cfg'` converges within `n` — a clean `±1` with NO `K.length` offset (config level).
This is the single primitive every `▷`-guarded anti-reduction threads through. -/
theorem convergesC_le_step {n : Nat} {cfg cfg' : Config}
    (hstep : Source.step cfg = some cfg') (hne : ∀ v, cfg ≠ ([], Comp.ret v)) :
    ConvergesC_le (n + 1) cfg ↔ ConvergesC_le n cfg' := by
  unfold ConvergesC_le
  rw [Config.run_step n cfg hne, hstep]

/-- Config-level step-bounded co-approximation: `cfg₁` converges within `n` steps ⇒ `cfg₂` converges
(UNBOUNDED on the right — Biernacki's `Obs`). The `▷`-carrying observation `Krel`/`Crel`/`Srel` use. -/
def CoApproxC_le (n : Nat) (cfg₁ cfg₂ : Config) : Prop :=
  ConvergesC_le n cfg₁ → (∃ m w, Config.run m cfg₂ = Result.done w)

/-- `CoApproxC_le 0` is VACUOUSLY TRUE (premise `ConvergesC_le 0` is `False`). The μ-floor discharge. -/
theorem coApproxC_le_zero (cfg₁ cfg₂ : Config) : CoApproxC_le 0 cfg₁ cfg₂ :=
  fun h => absurd h (not_convergesC_le_zero cfg₁)

/-- Right-side anti-reduction (UNBOUNDED): if `cfg₂ ↦ cfg₂'` and `cfg₂'` converges, so does `cfg₂`. -/
theorem converges_anti_step {cfg₂ cfg₂' : Config} (hstep : Source.step cfg₂ = some cfg₂')
    (hne : ∀ v, cfg₂ ≠ ([], Comp.ret v)) (h : ∃ m w, Config.run m cfg₂' = Result.done w) :
    ∃ m w, Config.run m cfg₂ = Result.done w := by
  obtain ⟨m, w, hm⟩ := h
  exact ⟨m + 1, w, by rw [Config.run_step m cfg₂ hne, hstep]; exact hm⟩

/-- THE generic `▷`-anti-reduction over the metered observation. Both sides take ONE config step
(left metered `−1`, right unbounded anti-reduce); the reducts related at the DROPPED index `n` give the
redexes related at `n+1`. Every frame-reduce return-half (`letF`/`appF`/`handleF`) and every `CIStep`
head-expansion routes through this ONE lemma — the factoring that localizes the metering (ADR-0041
alt-1 overturn). NO `K.length` offset: config level. -/
theorem coApproxC_le_anti_step {n : Nat} {cfg₁ cfg₁' cfg₂ cfg₂' : Config}
    (hstep₁ : Source.step cfg₁ = some cfg₁') (hne₁ : ∀ v, cfg₁ ≠ ([], Comp.ret v))
    (hstep₂ : Source.step cfg₂ = some cfg₂') (hne₂ : ∀ v, cfg₂ ≠ ([], Comp.ret v))
    (h : CoApproxC_le n cfg₁' cfg₂') : CoApproxC_le (n + 1) cfg₁ cfg₂ := by
  intro hconv
  rw [convergesC_le_step hstep₁ hne₁] at hconv
  exact converges_anti_step hstep₂ hne₂ (h hconv)

/-- NON-dropping frame anti-reduction (the β/return-bridge form). When the reduct is already related at
the SAME index `n` (not the dropped one), the left's lost step (`n → n-1` via the step) is re-padded by
monotonicity (`ConvergesC_le (n-1) ⊆ ConvergesC_le n`). Used by `appF`/`handleF` REDUCE bridges where the
reduct relation comes from a body IH at the full index `n`, not a `▷`-dropped one. -/
theorem coApproxC_le_reduce {n : Nat} {cfg₁ cfg₁' cfg₂ cfg₂' : Config}
    (hstep₁ : Source.step cfg₁ = some cfg₁') (hne₁ : ∀ v, cfg₁ ≠ ([], Comp.ret v))
    (hstep₂ : Source.step cfg₂ = some cfg₂') (hne₂ : ∀ v, cfg₂ ≠ ([], Comp.ret v))
    (h : CoApproxC_le n cfg₁' cfg₂') : CoApproxC_le n cfg₁ cfg₂ := by
  intro hconv
  -- ConvergesC_le n redex; if n=0 vacuous. Else step ⇒ ConvergesC_le (n-1) reduct ⊆ ConvergesC_le n reduct.
  cases n with
  | zero => exact absurd hconv (not_convergesC_le_zero _)
  | succ k =>
      rw [convergesC_le_step hstep₁ hne₁] at hconv
      exact converges_anti_step hstep₂ hne₂ (h (hconv.mono (Nat.le_succ k)))

/-! ### 5.0b `NotEvaluated` — the coeffect-erasure notion (`zero_usage_erasable`)

`NotEvaluated i c`: the de Bruijn index `i`'s binder is never EVALUATED in `c` — i.e. WHAT is
substituted at index `i` cannot affect `c`'s observable behaviour. The faithful notion is SEMANTIC,
not structural: a 0-graded variable is still substituted syntactically and still type-checks (QTT
permits 0-graded occurrences, e.g. `ret (vvar 0)` at returner grade `q = 0`), so "index `i` doesn't
occur" is FALSE — only its *evaluation* is absent. We phrase that as observational
substitution-irrelevance: every two fillers produce `≈`-equivalent computations. This is exactly
Torczon's grade-0 erasure (`semtyping.v`), which is proved via the logical relation. -/
def NotEvaluated (i : Nat) (c : Comp) : Prop :=
  ∀ v₁ v₂ : Val, Comp.substFrom i v₁ c ≈ Comp.substFrom i v₂ c


/-! ### 5.0a Plug/run bridge + `seq_unit` (the left-unit head reduction)

`seq_unit` is purely OPERATIONAL — no LR machinery. `seqComp (ret v) c = letC (ret v) (shift c)`
head-reduces to `c` in TWO machine steps (`letC (ret v) N ↦ N[v]`, then `(shift c)[v] = c` by
`Comp.subst_shift`), and this holds in EVERY context. The bridge `run_plug` says loading a
`plug C x` term reaches the focused config `(C, x)` after `C.length` push steps, which lets the
context-quantified `ctxEquiv` reduce to a config-level co-convergence. -/

/-- Loading `plug C c` and running it equals running the focused config `(C, c)`, modulo the
`C.length` push steps that re-decompose `plug C c` back into the frame stack `C`. The machine
PUSHes through each `letC/app/handle` node the `plug` built (those nodes always PUSH, regardless of
the subterm), rebuilding `C` innermost-first. -/
theorem run_plug : ∀ (C : EvalCtx) (c : Comp) (n : Nat),
    Config.run (n + C.length) ([], Bang.plug C c) = Config.run n (C, c)
  | [], c, n => by simp only [Bang.plug, List.length_nil, Nat.add_zero]
  | fr :: K, c, n => by
      -- plug (fr::K) c = plug K (wrap fr c); IH on K reaches (K, wrap fr c); one PUSH ↦ (fr::K, c).
      have hwrap : Source.step (K, fr.wrapStep c) = some (fr :: K, c) := by
        cases fr <;> rfl
      have hne : ∀ v, (K, fr.wrapStep c) ≠ ([], Comp.ret v) := by
        intro v; cases fr <;> simp [Frame.wrapStep]
      have hstep : Config.run (n + 1) (K, fr.wrapStep c) = Config.run n (fr :: K, c) := by
        rw [Config.run_step n (K, fr.wrapStep c) hne, hwrap]
      rw [plug_cons fr K c, List.length_cons,
        show n + (K.length + 1) = (n + 1) + K.length by omega, run_plug K (fr.wrapStep c) (n + 1),
        hstep]

/-- `Converges (plug C x)` is exactly config-level convergence of the focused `(C, x)`. -/
theorem converges_plug_iff (C : EvalCtx) (x : Comp) :
    Converges (Bang.plug C x) ↔ ∃ n w, Config.run n (C, x) = Result.done w := by
  constructor
  · rintro ⟨fuel, w, hfuel⟩
    -- bump fuel to `fuel + C.length` (run_done_add), then run_plug peels the C.length push steps.
    refine ⟨fuel, w, ?_⟩
    have : Config.run (fuel + C.length) ([], Bang.plug C x) = Result.done w :=
      Config.run_done_add C.length fuel ([], Bang.plug C x) w hfuel
    rwa [run_plug C x fuel] at this
  · rintro ⟨n, w, hn⟩
    exact ⟨n + C.length, w, by
      show Source.eval (n + C.length) (Bang.plug C x) = Result.done w
      rw [show Source.eval (n + C.length) (Bang.plug C x)
            = Config.run (n + C.length) ([], Bang.plug C x) from rfl, run_plug C x n]; exact hn⟩

/-- The head reduction at config level: `(C, seqComp (ret v) c)` runs to `(C, c)` after 2 steps. -/
theorem seqComp_ret_run (v : Val) (c : Comp) (C : EvalCtx) (n : Nat) :
    Config.run (n + 2) (C, seqComp (Comp.ret v) c) = Config.run n (C, c) := by
  -- step 1 (PUSH): (C, letC (ret v) (shift c)) ↦ (letF (shift c) :: C, ret v)
  -- step 2 (let-bind): (letF (shift c)::C, ret v) ↦ (C, (shift c)[v]) = (C, c) by subst_shift
  show Config.run (n + 2) (C, Comp.letC (Comp.ret v) (Comp.shift c)) = _
  -- two transitions; neither config is `([], ret _)` (focus is `letC …`, then stack is non-empty).
  have hne1 : ∀ u, (C, Comp.letC (Comp.ret v) (Comp.shift c)) ≠ ([], Comp.ret u) := by
    intro u; simp
  have hne2 : ∀ u, (Frame.letF (Comp.shift c) :: C, Comp.ret v) ≠ ([], Comp.ret u) := by
    intro u; simp
  -- step 1: (C, letC (ret v) (shift c)) ↦ (letF (shift c) :: C, ret v)
  have hr1 : Config.run (n + 1 + 1) (C, Comp.letC (Comp.ret v) (Comp.shift c))
      = Config.run (n + 1) (Frame.letF (Comp.shift c) :: C, Comp.ret v) := by
    rw [Config.run_step (n + 1) _ hne1]; rfl
  -- step 2: (letF (shift c) :: C, ret v) ↦ (C, (shift c)[v]) = (C, c) by subst_shift
  have hr2 : Config.run (n + 1) (Frame.letF (Comp.shift c) :: C, Comp.ret v)
      = Config.run n (C, c) := by
    rw [Config.run_step n _ hne2]
    show Config.run n (C, Comp.subst v (Comp.shift c)) = Config.run n (C, c)
    rw [Comp.subst_shift]
  rw [show n + 2 = (n + 1) + 1 by omega, hr1, hr2]

theorem seq_unit_proof (v : Val) {c : Comp} : seqComp (Comp.ret v) c ≈ c := by
  -- `≈` = approx both ways; each is context-quantified `Converges`. Bridge to config level,
  -- where the 2-step head reduction makes the two foci co-converge with a ±2 fuel offset.
  have fwd : ∀ x y : Comp, (∀ (C : EvalCtx) n w,
      Config.run n (C, x) = Result.done w → ∃ m, Config.run m (C, y) = Result.done w) →
      x ⊑ y := by
    intro x y hco C hx
    rw [Cxt.plug, converges_plug_iff] at hx ⊢
    obtain ⟨n, w, hn⟩ := hx
    obtain ⟨m, hm⟩ := hco C n w hn
    exact ⟨m, w, hm⟩
  refine ⟨fwd _ _ ?_, fwd _ _ ?_⟩
  · -- seqComp (ret v) c ⊑ c : a run of the seqComp reaches `done` ⇒ so does c (drop the 2 steps).
    intro C n w hn
    -- bump n to n+2 (run_done_add), then seqComp_ret_run rewrites it to c's run at fuel n.
    refine ⟨n, ?_⟩
    have h2 : Config.run (n + 2) (C, seqComp (Comp.ret v) c) = Result.done w :=
      Config.run_done_add 2 n (C, seqComp (Comp.ret v) c) w hn
    rwa [seqComp_ret_run v c C n] at h2
  · -- c ⊑ seqComp (ret v) c : run of c reaches done ⇒ feed n+2 fuel through the head reduction.
    intro C n w hn
    exact ⟨n + 2, by rw [seqComp_ret_run v c C n]; exact hn⟩


/-! ## 5.1 LR helpers — concretized from the kernel + Biernacki popl18 §5.1.

shape: biernacki-popl18 §3 Fig 1 (`ECont`), §5.1 Figs 6–9 (Vrel/Srel/Krel/Crel domains). -/

-- The LR's stack/continuation domain (Biernacki Krel domain `K⟦·⟧`, popl18 §5.1
-- Fig 7). SINGLE SOURCE OF TRUTH: this is the same evaluation-context notion as `Cxt`
-- — the kernel's CK frame stack — so `Stack` reuses `EvalCtx` and `Stack.plug` reuses
-- `plug`. (Biernacki keeps one `ECont` grammar across the operational semantics and
-- the LR; we likewise keep one `EvalCtx`.)
abbrev Stack : Type := EvalCtx
def Stack.plug (K : Stack) (c : Comp) : Comp := Bang.plug K c

/-- Base-type value relation (Biernacki `⟦τ⟧` restricted to base types, popl18 §5.1
Fig 6). At base types the relation is SYNTACTIC value identity — `unit`/`int` carry no
latent computation, so observably-equal base values are equal values. Non-base types
(`U`/`sum`/`prod`/`mu`) relate through `Vrel` (the step-indexed LR proper, Unit 2), so
`BaseRel` is `False` there: it is the BASE case the inductive `Vrel` bottoms out in,
not a relation over all types. -/
def BaseRel {Eff Mult : Type} (A : VTy Eff Mult) (v₁ v₂ : Val) : Prop :=
  match A with
  | .unit => v₁ = Val.vunit ∧ v₂ = Val.vunit
  | .int  => ∃ n : Int, v₁ = Val.vint n ∧ v₂ = Val.vint n
  | _     => False

/-- Base-type stack relation (Biernacki Krel `K⟦τ/ε⟧` at base answer types, popl18 §5.1
Fig 7). Two stacks relate at index `n` and a base RETURNER type `F q A` when, plugged
with `BaseRel`-related values, they co-converge within the step budget — the
biorthogonal "observe through related values" clause specialized to base answers. At
non-returner answer types it is `False` (the base case for `Krel`, Unit 2). The index
threads Biernacki's `▷` (later) budget. -/
def BaseStackRel {Eff Mult : Type} [Lattice Eff] [OrderBot Eff]
    (_n : Nat) (C : CTy Eff Mult) (K₁ K₂ : Stack) : Prop :=
  match C with
  | .F _ A =>
      ∀ v₁ v₂, BaseRel A v₁ v₂ →
        CoApprox (Stack.plug K₁ (Comp.ret v₁)) (Stack.plug K₂ (Comp.ret v₂))
  | .arr _ _ _ => False

/-- CBPV thunk destructor (Biernacki §5.1 coercion: read a suspended computation type
out of a value type). `U φ B` is the thunk of a `φ`-effectful `B`; everything else is
not a thunk. The LR uses this to know when a value is a thunk it must relate at `B`. -/
def asThunk {Eff Mult : Type} : VTy Eff Mult → Option (Eff × CTy Eff Mult)
  | .U φ B => some (φ, B)
  | _      => none

/-- CBPV returner destructor (Biernacki §5.1 coercion: read the produced value type out
of a computation type). `F q A` returns an `A` at multiplicity `q`; an `arr` does not
return, so `none`. The LR uses this to know when a computation produces a value to
relate at `A`. -/
def asReturner {Eff Mult : Type} : CTy Eff Mult → Option (Mult × VTy Eff Mult)
  | .F q A => some (q, A)
  | _      => none

/-- Embed an operation as a computation that raises effect `ℓ` with payload `v`
(Biernacki §5.1 `op_l v`; our zero-shot `throws` operation, ADR-0022/0023). FORK from
the frozen axiom: the old signature `raise : Eff → Val → Comp` took an opaque lattice
`Eff` element, from which NO concrete `Label` can be extracted to feed `up` — it could
not have been inhabited faithfully. The faithful type is `Label → Val → Comp`
(`Label = Nat`, the concrete operation channel `up` consumes). -/
def raise (ℓ : Label) (v : Val) : Comp := Comp.up ℓ "raise" v
-- operation arg/result types: superseded by `EffSig.opArg`/`opRes` (ADR-0022 D1),
-- which are per-`(Label, OpId)` (the old per-`Eff` axioms could not type `get` vs `put`).


/-! ## 5.2a Semantic closedness (`Val.Closed`)

The substitution-descent lemma `closeC_subst_comm` (Compat.lean) needs the `EnvRel` fillers — and the
values quantified in `Krel`/`Srel` — to be SHIFT-INVARIANT, so the `Val.shift` that
`Comp.substFrom (k+1)` introduces under a binder vanishes. We carry this SEMANTICALLY (not via the
typing judgement `HasVTy`): a value is `Closed` when no `shiftFrom` cutoff alters it. This mirrors
`Metatheory.lean`'s `HasVTy.shift_closed` (typed-closed ⇒ shift-invariant) but stays inside the LR's
value language, so the carrier composes with the relations below without dragging the typing context in.

The faithfulness anchor (why this is a real invariant, not an artifact): the CK machine's focus is
always a CLOSED term, and every value it RETURNS or PLUGS is closed (ADR-0025/0030 — the same
closed-cell invariant `Handler.shiftFrom`/`substFrom` exploit on heap cells). So enforcing closedness
on the values quantified in `Krel`'s return-half / `Srel`'s resume-half is exactly the machine's
behaviour, and `EnvRel`-filler-closedness is then maintained by construction when the fundamental
induction extends δ under a binder. -/

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


/-! ## 5.2 LR — Vrel / Srel / Krel / Crel

The four step-indexed logical relations, transcribed clause-by-clause from
Biernacki popl18 Figs 6–9 (`references/papers/3-lr/`) onto OUR kernel
(`Comp`/`Val`/`CTy`/`VTy`/`EvalCtx`), specialized to set-rows.

shape: §5.2 / Figs 6–9 —
```
  Vrel n A v₁ v₂            ⟺  ⟦A⟧η          (Fig 6 value interpretation)
  Crel n C ε c₁ c₂          ⟺  E⟦C/ε⟧η       (Fig 7 biorthogonal computation closure)
  Krel n C ε K₁ K₂          ⟺  K⟦C/ε⟧η       (Fig 7 evaluation-context relation)
  Srel n C ε K₁ K₂ c₁ c₂    ⟺  S⟦C/ε⟧η       (Fig 7 control-stuck / "simple expr" relation)
```
`Obs` is our `CoApprox` (fuel-bounded co-convergence; no extra index — `Converges`
already iterates fuel). η (the row-variable interpretation) is absent: our rows are
CLOSED `Finset Label`, not polymorphic (ADR-0027, no row variables).

FROZEN-SIGNATURE FIX (Option C, lead-authorized STATEMENT_CHANGE): Biernacki indexes
every COMPUTATION-level relation by `τ/ε` (type AND row). Our kernel keeps the row
SEPARATE from `CTy` (`HasCTy γ Γ c e B` synthesizes `e : Eff` independently — `letC`
joins `φ₁⊔φ₂`, `up` produces `φ`; `e` is NOT a function of `(c,B)`), and the row is
load-bearing in `Srel` (the `labelEff ℓ ≤ ε` clause). So the Phase-A 2-arg `Crel`/`Krel`
(and ε-only `Srel`) stubs were UNDER-SPECIFIED — the faithful relations gain the `Eff`
row argument. `Vrel` stays 4-arg: value types carry their rows internally at `U φ B`.
(Mirror of U1's `raise` fix: a frozen stub that couldn't be inhabited faithfully.) The
ambient `[EffSig Eff Mult]` is needed to type op args/results (`opArg`/`opRes`) and the
label's singleton row (`labelEff`); `Spec.lean` already carries it in scope.

SET-ROW SPECIALIZATION (Biernacki §5.4): with disjoint set-rows the ρ-maps of the
effect-row interpretation VANISH and `ρᵢ-free(Eᵢ)` collapses to "`Eᵢ` does not handle ℓ"
— here `splitAt K ℓ op = none`. (ADR-0001 rows-as-sets is exactly the Hillerström–Lindley
regime §5.4 shows licenses this.)

WELL-FOUNDEDNESS: the mutual block terminates by a lex measure `(n, sizeOf type, role)`
(Ahmed-style step index; ahmed-esop06 / proving-correctness-step-indexed). The `role`
(Vrel 3 > Crel 2 > Krel 1 > Srel 0) orders the four relations WITHIN one `(n, type)`, so
the biorthogonal `Crel → Krel → Srel` cycle (all at the same `(n,C)`) strictly decreases.
`n` drops (Biernacki's `▷` later modality) on the only two index-decreasing edges: `Vrel`
at `mu` (guarded recursion on the unrolled type) and `Srel`'s output clause back into
`Crel`. `Vrel` at `U φ B` descends to `Crel B` on the strictly smaller type. No iris-lean
`▷` encoding needed — the plain lex order goes through (`decreasing_by` auto-discharged). -/

mutual
/-- Value relation `⟦A⟧η` (Biernacki Fig 6), our `VTy`. Base types bottom out in
`BaseRel` (syntactic identity). `U φ B` (the CBPV thunk, our analogue of the arrow
`τ₁ →ε τ₂` value) relates two thunks iff their forced computations are `Crel`-related at
`B` under the thunk's row `φ`. ADT formers relate structurally (`sum`/`prod` at the
sub-types). `mu` is GUARDED: at `n+1` two `fold`s relate iff their payloads relate at the
unrolled type `A[μX.A/X]` at index `n` (the `▷` step that makes the recursion well-founded;
`Vrel 0 (mu _)` is vacuously `True`). `tvar` is `False` (closed types: a bare recursion
var is never reached — `unrollMu` substitutes it away at each `mu` step). -/
def Vrel {Eff Mult : Type} [Lattice Eff] [OrderBot Eff] [CommSemiring Mult] [DecidableEq Mult]
    [EffSig Eff Mult] : Nat → VTy Eff Mult → Val → Val → Prop
  | _,     .unit,    v₁, v₂ => BaseRel (Eff := Eff) (Mult := Mult) VTy.unit v₁ v₂
  | _,     .int,     v₁, v₂ => BaseRel (Eff := Eff) (Mult := Mult) VTy.int v₁ v₂
  | n,     .U φ B,   v₁, v₂ =>
      -- ◊4.5 STATEMENT_CHANGE_OK="◊4.5 Vrel U-clause ∀j≤n". DOWNWARD-CLOSED thunk relation: the forced
      -- computations are `Crel j`-related at EVERY `j ≤ n`, not just at `n`. This makes `Vrel`-down
      -- STRUCTURAL (quantifier-restriction `{j≤m} ⊆ {j≤n}`), sidestepping the `Vrel (U φ B)` → `Crel`-down
      -- → `Krel`-up (false under the `∀j≤n` Krel) route that blocked `krel_appF_intro`'s arrow half. The
      -- Kripke continuation IHs (`∀j≤n, Vrel j → Crel j`) consume this at the matching index.
      ∃ c₁ c₂, v₁ = Val.vthunk c₁ ∧ v₂ = Val.vthunk c₂ ∧ ∀ j, j ≤ n → Crel j B φ c₁ c₂
  | n,     .sum A B, v₁, v₂ =>
      (∃ w₁ w₂, v₁ = Val.inl w₁ ∧ v₂ = Val.inl w₂ ∧ Vrel n A w₁ w₂) ∨
      (∃ w₁ w₂, v₁ = Val.inr w₁ ∧ v₂ = Val.inr w₂ ∧ Vrel n B w₁ w₂)
  | n,     .prod A B, v₁, v₂ =>
      ∃ a₁ a₂ b₁ b₂, v₁ = Val.pair a₁ b₁ ∧ v₂ = Val.pair a₂ b₂ ∧
        Vrel n A a₁ a₂ ∧ Vrel n B b₁ b₂
  | n,     .mu A,    v₁, v₂ =>
      -- ◊4.5 ROUTE 1 (ke): UNIFIED strict-`<` μ-clause. The fold SHAPE holds at EVERY index (incl. the
      -- `n=0` floor — there `∀ j < 0` is vacuous, so the floor still pins `v₁=fold w₁ ∧ v₂=fold w₂`); the
      -- unrolled PAYLOAD relation is `▷`-guarded as `∀ j < n` (Biernacki's later modality). Well-founded by
      -- `Prod.Lex.left` on the strict `j < n` — NO `sizeOf` decrease needed on the type, so `unrollMu A`
      -- being structurally larger is irrelevant (this is why the old `(n, sizeOf)`-only worry dissolves).
      -- The floor now carries fold-shape (vs the old `Vrel 0 (mu) := True`), so the `crel_fund` unfold/vvar
      -- case gets the scrutinee shape at `n=0`; the floor return-obligation is degenerated in `Krel` below.
      ∃ w₁ w₂, v₁ = Val.fold w₁ ∧ v₂ = Val.fold w₂ ∧ ∀ j, j < n → Vrel j (VTy.unrollMu A) w₁ w₂
  | _,     .tvar _,  _,  _  => False
termination_by n A _ _ => (n, sizeOf A, 3)
decreasing_by
  -- ◊4.5: the U-clause edge is `Crel j B φ` at `j ≤ n` (measure `(j, sizeOf B, 2)` vs Vrel's
  -- `(n, sizeOf (U φ B), 3)`). `j < n` drops the index; `j = n` drops on `sizeOf B < sizeOf (U φ B)`.
  -- ROUTE 1: the new μ-clause edge is `Vrel j (unrollMu A)` at STRICT `j < n` — pure `Prod.Lex.left`
  -- (index drop), no type-size obligation. The structural sub-type edges (sum/prod) auto-discharge.
  -- Try auto first, then the strict-`<` edge, then the `≤`-split (U-clause).
  all_goals
    first
      | decreasing_tactic
      | (simp_wf; exact Prod.Lex.left _ _ ‹_ < _›)
      | (rcases Nat.lt_or_eq_of_le ‹_ ≤ _› with hlt | rfl <;>
          first | (simp_wf; exact Prod.Lex.left _ _ hlt) | (simp_wf; decreasing_tactic))

/-- Computation relation `E⟦C/ε⟧η` (Biernacki Fig 7), the BIORTHOGONAL closure: two
computations relate iff they co-behave (`CoApprox = Obs`) under every `Krel`-related pair
of stacks. This is the relation `lr_sound`/`lr_fundamental` are stated over. -/
def Crel {Eff Mult : Type} [Lattice Eff] [OrderBot Eff] [CommSemiring Mult] [DecidableEq Mult]
    [EffSig Eff Mult] : Nat → CTy Eff Mult → Eff → Comp → Comp → Prop
  | n, C, ε, c₁, c₂ =>
      -- ◊4.5b: METERED config-level observation (`CoApproxC_le`, §5.0a‴) — left term metered within
      -- `n` machine steps, right unbounded. Observes the FOCUSED config `(Kᵢ, cᵢ)`, never `plug Kᵢ cᵢ`,
      -- so the `+K.length` `run_plug` refocus offset (lr45's wall) never enters. This is the `▷` carrier:
      -- at `n=0` the premise `ConvergesC_le 0` is `False` (`run 0 = oom`), so `Crel 0` is VACUOUS — the
      -- μ-floor discharge. Head-expansion drops one budget (`Crel_head_step`, Compat.lean §B.0).
      ∀ K₁ K₂ : Stack, Krel n C ε K₁ K₂ →
        CoApproxC_le n (K₁, c₁) (K₂, c₂)
termination_by n C _ _ _ => (n, sizeOf C, 2)

/-- Continuation/stack relation `K⟦C/ε⟧η` (Biernacki Fig 7). A computation can finish two
ways — RETURN a value or RAISE an effect — so two stacks relate iff they co-behave when
plugged with EITHER (a) `Vrel`-related returned values (at `C`'s returner type `F q A`), or
(b) `Srel`-related control-stuck computations. The two halves of the biorthogonal "observe
through related values OR related stuck terms" clause. -/
def Krel {Eff Mult : Type} [Lattice Eff] [OrderBot Eff] [CommSemiring Mult] [DecidableEq Mult]
    [EffSig Eff Mult] : Nat → CTy Eff Mult → Eff → Stack → Stack → Prop
  | n, C, ε, K₁, K₂ =>
      -- ◊4.5 (ADR-0039): DOWNWARD-CLOSED `∀ j ≤ n` (IxFree/COFE monotone reading — Biernacki §line-555:
      -- `A ⇒ B` valid at n iff `∀k≤n. Aₖ→Bₖ`; ahmed-esop06 Fig 3 `Rel τ` is `∀i≤j`-closed). Makes
      -- `Krel`-monotonicity FREE (subset of the `∀ j ≤ n`) — what the μ/resume `▷`-anti-reduction needs
      -- (`Crel m → Crel (m+1)` via `Krel (m+1) → Krel m`). The `∀ j ≤ n` over the implications dissolves
      -- the Srel-resume contravariance (a relation-as-PREMISE checked at every `j ≤ n` is monotone). The
      -- arrow clause (ADR-0038 PEELING) routes `Krel j (arr q A B) → Krel j B` (`sizeOf B < sizeOf (arr)`).
      ∀ j, j ≤ n →
      (∀ q A, C = CTy.F q A → ∀ v₁ v₂, Val.Closed v₁ → Val.Closed v₂ → Vrel j A v₁ v₂ →
        CoApproxC_le j (K₁, Comp.ret v₁) (K₂, Comp.ret v₂))
      ∧ (∀ c₁ c₂, Srel j C ε K₁ K₂ c₁ c₂ →
        CoApproxC_le j (K₁, c₁) (K₂, c₂))
      ∧ (∀ q A B, C = CTy.arr q A B →
          ∃ w₁ w₂ K₁' K₂', K₁ = Frame.appF w₁ :: K₁' ∧ K₂ = Frame.appF w₂ :: K₂' ∧
            Val.Closed w₁ ∧ Val.Closed w₂ ∧ Vrel j A w₁ w₂ ∧ Krel j B ε K₁' K₂')
termination_by n C _ _ _ => (n, sizeOf C, 1)
decreasing_by
  -- Each recursive edge is at index `j ≤ n` with a strictly-smaller TYPE (Vrel/Krel: A/B ⊏ C) or the
  -- same type but a smaller ROLE (Srel: role 0 < Krel's 1). Lex `(index, sizeOf, role)`: `j < n` drops
  -- the first component; `j = n` reduces to the SAME goal the pre-◊4.5 auto-discharge handled
  -- (index unchanged, sizeOf/role tie-break) — so delegate it to `decreasing_tactic`.
  -- ◊4.5 ROUTE 1: the degenerate return-half puts the `Vrel j A` edge under a `0 < j` hyp, so a bare
  -- `‹_ ≤ _›` can grab the wrong bound. Discharge each edge robustly: `simp_wf` then either a strict
  -- index drop (`Prod.Lex.left`, `j < n` by omega) or a same-index type/role drop (`decreasing_tactic`).
  all_goals
    (rcases Nat.lt_or_eq_of_le ‹_ ≤ _› with hlt | rfl)
    <;> first
      | (simp_wf; exact Prod.Lex.left _ _ hlt)
      | decreasing_tactic

/-- Control-stuck / "simple expression" relation `S⟦C/ε⟧η` (Biernacki Fig 7),
SET-ROW-specialized (§5.4: ρ-maps dropped). Carries the contexts `K₁,K₂` and the bare
operations `c₁,c₂` (Biernacki's `(E₁[e₁], E₂[e₂])` with `eᵢ = opₗ vᵢ`). Two terms are
`Srel`-related when both are the SAME operation `up ℓ op _` on an effect `ℓ` IN the row
(`labelEff ℓ ≤ ε`), with `Vrel`-related arguments (at `opArg ℓ op`), under stacks that do
NOT handle `ℓ` (`splitAt = none`, the set-row form of `ρ-free`), AND — the OUTPUT clause
(`▷E⟦C/ε⟧`) — resuming with any `Vrel`-related result values (at `opRes ℓ op`) leaves the
two stacks `Crel`-related at the NEXT index. The `n+1 ↦ n` drop is Biernacki's `▷` later
modality on the output. `Srel 0` is vacuously `True` (index exhausted). -/
def Srel {Eff Mult : Type} [Lattice Eff] [OrderBot Eff] [CommSemiring Mult] [DecidableEq Mult]
    [EffSig Eff Mult] : Nat → CTy Eff Mult → Eff → Stack → Stack → Comp → Comp → Prop
  -- ◊4.5 STATEMENT_CHANGE_OK="◊4.5 Srel 0 := False (IxFree premise-position index-0 convention)".
  -- The index-0 case is EMPTY, not trivially-true: `Srel` sits in `Krel`'s stuck-half PREMISE, and the
  -- downward-closed `Krel n := ∀ j ≤ n, …` exposes `j = 0`. With `Srel 0 = True`, the j=0 stuck half
  -- demands `CoApprox c₁ c₂` for ARBITRARY c (no `up`-shape) ⇒ `Krel (n+1) [] []` FALSE ⇒ `krel_nil_succ`
  -- (hence `lr_sound`'s witness) gutted — vacuity. `Srel 0 := False` makes the j=0 stuck half
  -- (`False → CoApprox`) vacuously true (the degenerate-at-0 = EMPTY convention for a premise-position
  -- relation). `crel_zero` re-derives under the new downward-closed `Krel` (see its proof).
  | 0,   _, _, _,  _,  _,  _  => False
  | n+1, C, ε, K₁, K₂, c₁, c₂ =>
      ∃ (ℓ : Label) (op : OpId) (v₁ v₂ : Val) (Aarg Ares : VTy Eff Mult),
        c₁ = Comp.up ℓ op v₁ ∧ c₂ = Comp.up ℓ op v₂ ∧
        EffSig.labelEff (Mult := Mult) ℓ ≤ ε ∧
        EffSig.opArg (Mult := Mult) ℓ op = some Aarg ∧
        EffSig.opRes (Mult := Mult) ℓ op = some Ares ∧
        Vrel n Aarg v₁ v₂ ∧
        (Bang.splitAt K₁ ℓ op = none) ∧ (Bang.splitAt K₂ ℓ op = none) ∧
        (∀ u₁ u₂, Val.Closed u₁ → Val.Closed u₂ → Vrel n Ares u₁ u₂ →
          Crel n C ε (Stack.plug K₁ (Comp.ret u₁)) (Stack.plug K₂ (Comp.ret u₂)))
termination_by n C _ _ _ _ _ => (n, sizeOf C, 0)
end


/-! ## 5.2′ ◊4.5b KrelS REBUILD — the answer-typed biorthogonal LR core (ADR-0041, PATH-cap45-rebuild)

The ◊4.5b core re-architecture (sub-block a, ADDITIVE landing). The flat `Crel`/`Krel`/`Srel` above
ERASED Biernacki's answer type — the producer-`up` resume needs `Krel⊸Crel` biorthogonal COMPOSITION
(Lemma 2), which a focus-typed relation cannot express. The fix: the standard **answer-typed** stack
relation `KrelS n C D` (`C` = hole type, `D` = answer type at the bottom), with `CrelK` the
biorthogonal closure over it. Built UNDER TEMP NAMES (`VrelK`/`CrelK`/`KrelS`) ALONGSIDE the old
relations — the frozen `Crel` stays wired to the OLD def until sub-block (g) re-points it (body swap,
signature byte-identical, `D` quantified internally). Sub-blocks (b)–(f) migrate Compat onto `KrelS`.

  shape: biernacki-popl18 §5.1 Figs 6–9 (answer-typed `K⟦τ/ε⟧` + `C⟦τ₁/ε₁⟧{τ₂/ε₂⟧` partial contexts).

TERMINATION (build-verified, the discovery + this IC): lex **`(n, role, stackLen, sizeOf)`**, roles
`VrelK = 0 < KrelS = 1 < CrelK = 2`. `KrelS` recurses STACK-STRUCTURALLY (`KrelS n (fr::K) → KrelS n K`,
frames peel — `stackLen` drops); the answer-type `D` is INERT (threaded, NOT in the measure). The
type-DRIVEN form FAILS (the type grows under `plug` at the same index — ADR-0041). Every cross-function
edge drops: `n` (VrelK→CrelK via the ▷-guarded thunk `∀ j < n`; KrelS→CrelK frame-body `m < n`; VrelK-μ),
`role` (CrelK→KrelS, KrelS→VrelK-cap), `stackLen` (KrelS tail), or `sizeOf` (VrelK sum/prod internal —
the 4th tiebreaker, needed once VrelK joins the SCC via its U-clause → CrelK).

THUNK GUARD `∀ j < n` (Biernacki guarded-thunk, lead-APPROVED — STATEMENT_CHANGE_OK as at the old Vrel
U-clause, in-envelope): the old `∀ j ≤ n` FAILS termination at the VrelK→CrelK `j = n` edge
(build-confirmed both directions); `∀ j < n` passes AND is exactly what the sole consumer (`force`'s
head-expansion) needs (reducts at `m < n`). This is a SEPARATE edge from the letF frame-body index
(`m < n`), which is the independent ▷ at the resume seam. -/

-- ◊4.5b: the `KrelS` handleF RESUME CONJUNCT references `opArg` (the op-arg type the resume value
-- inhabits), so the whole mutual block now needs the `EffSig` instance in scope.
variable [EffSig Eff Mult]

mutual
/-- ◊4.5b value relation (temp name `VrelK`; → frozen `Vrel` at sub-block g). The ▷-guarded thunk
U-clause is `∀ j < n` (vs the old `∀ j ≤ n`) — required for the 3-way termination, exactly sufficient
for `force`'s head-expansion. -/
def VrelK : Nat → VTy Eff Mult → Val → Val → Prop
  | _,     .unit,    v₁, v₂ => BaseRel (Eff := Eff) (Mult := Mult) VTy.unit v₁ v₂
  | _,     .int,     v₁, v₂ => BaseRel (Eff := Eff) (Mult := Mult) VTy.int v₁ v₂
  | n,     .U φ B,   v₁, v₂ =>
      ∃ c₁ c₂, v₁ = Val.vthunk c₁ ∧ v₂ = Val.vthunk c₂ ∧ ∀ j, j < n → CrelK j B φ c₁ c₂
  | n,     .sum A B, v₁, v₂ =>
      (∃ w₁ w₂, v₁ = Val.inl w₁ ∧ v₂ = Val.inl w₂ ∧ VrelK n A w₁ w₂) ∨
      (∃ w₁ w₂, v₁ = Val.inr w₁ ∧ v₂ = Val.inr w₂ ∧ VrelK n B w₁ w₂)
  | n,     .prod A B, v₁, v₂ =>
      ∃ a₁ a₂ b₁ b₂, v₁ = Val.pair a₁ b₁ ∧ v₂ = Val.pair a₂ b₂ ∧
        VrelK n A a₁ a₂ ∧ VrelK n B b₁ b₂
  | n,     .mu A,    v₁, v₂ =>
      ∃ w₁ w₂, v₁ = Val.fold w₁ ∧ v₂ = Val.fold w₂ ∧ ∀ j, j < n → VrelK j (VTy.unrollMu A) w₁ w₂
  | _,     .tvar _,  _,  _  => False
  termination_by n A _ _ => (n, 0, 0, sizeOf A)
/-- ◊4.5b biorthogonal closure (temp name `CrelK`; → frozen `Crel` at sub-block g). The answer type
`D` is QUANTIFIED here (internal to `KrelS`), so the eventual `Crel` signature is byte-identical. -/
def CrelK : Nat → CTy Eff Mult → Eff → Comp → Comp → Prop
  | n, C, ε, c₁, c₂ =>
      ∀ (D : CTy Eff Mult) (K₁ K₂ : Stack), KrelS n C D ε K₁ K₂ →
        CoApproxC_le n (K₁, c₁) (K₂, c₂)
  termination_by n C _ _ _ => (n, 2, 0, sizeOf C)
/-- ◊4.5b answer-typed stack relation, STACK-STRUCTURAL. `C` = hole type, `D` = answer type (inert).
DISCOVERY-IC FORM: SINGLE-BODY def + internal `match K₁, K₂` (the multi-clause form fights the
unfolder); per-case `@[simp]` eq lemmas (`krelS_nil`/`letF`/`appF`/`handleF`) generated below. -/
def KrelS : Nat → CTy Eff Mult → CTy Eff Mult → Eff → Stack → Stack → Prop
  | n, C, D, ε, K₁, K₂ =>
      match K₁, K₂ with
      -- nil: hole type = answer type; observe related RETURNS (the biorthogonal base / return-half).
      | [], [] =>
          C = D ∧ (∀ q A, C = CTy.F q A → ∀ v₁ v₂, Val.Closed v₁ → Val.Closed v₂ → VrelK n A v₁ v₂ →
            CoApproxC_le n ([], Comp.ret v₁) ([], Comp.ret v₂))
      -- letF: hole is a returner `F q A`; frame body ▷-guarded at `m < n`, tail at continuation B.
      -- The continuation's row `φ` is bound existentially, AND the TAIL is at `φ` (not the ambient ε):
      -- after a letF frame the tail observes the CONTINUATION's execution, so the row threading through
      -- the eval context carries the continuation row `φ` downward. (This is what makes `crelK_ret`'s
      -- letF case close with NO row conversion — body and tail both at `φ`. Build-proven; the wrong
      -- "tail at ε" shape created a spurious antitone/monotone polarity clash.)
      | (Frame.letF N₁ :: K₁'), (Frame.letF N₂ :: K₂') =>
          ∃ q A B φ, C = CTy.F q A ∧
            (∀ m, m < n → ∀ v₁ v₂, Val.Closed v₁ → Val.Closed v₂ → VrelK m A v₁ v₂ →
              CrelK m B φ (Comp.subst v₁ N₁) (Comp.subst v₂ N₂))
            ∧ KrelS n B D φ K₁' K₂'
      -- appF: hole is an arrow `arr q A B`; cap is the appF arg, tail at codomain B.
      | (Frame.appF w₁ :: K₁'), (Frame.appF w₂ :: K₂') =>
          ∃ q A B, C = CTy.arr q A B ∧
            Val.Closed w₁ ∧ Val.Closed w₂ ∧ VrelK n A w₁ w₂ ∧ KrelS n B D ε K₁' K₂'
      -- handleF: tail recurses at the same hole type (handler return = identity, ADR-0023 Q6, so the
      -- block's returner type = the body's = the tail's hole type — `C` is preserved across the frame).
      -- ◊4.5b sub-block (f): the handlers MUST be EQUAL (`h₁ = h₂`). The producer's `up` some-half
      -- (`splitAt = some`) dispatches at the nearest catching frame; without `h₁ = h₂` the two stacks
      -- could catch `(ℓ,op)` at DIFFERENT positions (or one catch, one walk past) ⇒ the dispatched
      -- configs would be unrelated ⇒ co-equivalence FALSE (the build-traced gap, Compat:2003). Equal
      -- handlers make `splitAt` fire at the SAME position with the SAME handler + the SAME reinstalled
      -- state (state/txn store lives IN the handler, so `h₁=h₂` ⇒ identical resume), so the dispatched
      -- inner/outer segments stay `KrelS`-related (`krelS_splitAt_decomp`). The 6 CONSUMER cases all
      -- build EQUAL-handler stacks (`krelS_handleF_intro`), so they supply `h₁=h₂` for free.
      | (Frame.handleF h₁ :: K₁'), (Frame.handleF h₂ :: K₂') =>
          h₁ = h₂ ∧ KrelS n C D ε K₁' K₂'
            -- ◊4.5b RESUME CONJUNCT (config-level answer-typed re-expression of old `Srel` LR:554). The
            -- producer (`crelK_fund` up some-half) has NO `HasStack` on the stacks (only this `KrelS`), so
            -- the typed dispatched-config relation is NOT reconstructible from `h₁=h₂` + the tail alone —
            -- it must be CARRIED here. For every op + arg-values `w₁,w₂` related at SOME type `Aarg` (the
            -- producer instantiates `Aarg :=` the op's arg type), the two configs `dispatchOn` produces at
            -- the immediate split (`Kᵢ=[]`) co-converge at the dropped index `m < n` (the `▷`). The producer
            -- EXTRACTS this via `krelS_splitAt_decomp` at the catching frame; the CONSUMERS supply it
            -- (throws via `crelK_ret` on the tail — zero-shot, no append; state/txn via `krelS_append` — the
            -- one research crux). No op-interface needed in the def — the producer supplies `Aarg`.
            ∧ (∀ m, m < n → ∀ (op : OpId) (w₁ w₂ : Val) (cfg₁ cfg₂ : Config),
                Bang.handlesOp h₁ h₁.label op = true →
                Val.Closed w₁ → Val.Closed w₂ →
                (∀ Aop, EffSig.opArg (Eff := Eff) (Mult := Mult) h₁.label op = some Aop → VrelK m Aop w₁ w₂) →
                Bang.dispatchOn op w₁ ([], h₁, K₁') = some cfg₁ →
                Bang.dispatchOn op w₂ ([], h₁, K₂') = some cfg₂ →
                CoApproxC_le m cfg₁ cfg₂)
      | _, _ => False
termination_by n _ _ _ K _ => (n, 1, K.length, 0)
decreasing_by
  -- Lex `(n, role, stackLen, sizeOf)`: every edge drops `n` (▷-thunk j<n / frame-body m<n / μ),
  -- `role` (CrelK→KrelS, KrelS→VrelK-cap), `stackLen` (tail), or `sizeOf` (VrelK sum/prod).
  all_goals
    first
      | (simp_wf; exact Prod.Lex.left _ _ ‹_ < _›)
      | decreasing_tactic
end

-- DISCOVERY-IC per-case `@[simp]` equation lemmas (so downstream proofs unfold cleanly).
@[simp] theorem krelS_nil {n : Nat} {C D : CTy Eff Mult} {ε : Eff} :
    KrelS n C D ε [] [] ↔
      (C = D ∧ ∀ q A, C = CTy.F q A → ∀ v₁ v₂, Val.Closed v₁ → Val.Closed v₂ → VrelK n A v₁ v₂ →
        CoApproxC_le n ([], Comp.ret v₁) ([], Comp.ret v₂)) := by
  rw [KrelS]

@[simp] theorem krelS_letF {n : Nat} {C D : CTy Eff Mult} {ε : Eff} {N₁ N₂ : Comp} {K₁ K₂ : Stack} :
    KrelS n C D ε (Frame.letF N₁ :: K₁) (Frame.letF N₂ :: K₂) ↔
      ∃ q A B φ, C = CTy.F q A ∧
        (∀ m, m < n → ∀ v₁ v₂, Val.Closed v₁ → Val.Closed v₂ → VrelK m A v₁ v₂ →
          CrelK m B φ (Comp.subst v₁ N₁) (Comp.subst v₂ N₂))
        ∧ KrelS n B D φ K₁ K₂ := by
  rw [KrelS]

@[simp] theorem krelS_appF {n : Nat} {C D : CTy Eff Mult} {ε : Eff} {w₁ w₂ : Val} {K₁ K₂ : Stack} :
    KrelS n C D ε (Frame.appF w₁ :: K₁) (Frame.appF w₂ :: K₂) ↔
      ∃ q A B, C = CTy.arr q A B ∧
        Val.Closed w₁ ∧ Val.Closed w₂ ∧ VrelK n A w₁ w₂ ∧ KrelS n B D ε K₁ K₂ := by
  rw [KrelS]

@[simp] theorem krelS_handleF {n : Nat} {C D : CTy Eff Mult} {ε : Eff} {h h' : Handler}
    {K₁ K₂ : Stack} :
    KrelS n C D ε (Frame.handleF h :: K₁) (Frame.handleF h' :: K₂) ↔
      (h = h' ∧ KrelS n C D ε K₁ K₂
        ∧ (∀ m, m < n → ∀ (op : OpId) (w₁ w₂ : Val) (cfg₁ cfg₂ : Config),
            Bang.handlesOp h h.label op = true →
            Val.Closed w₁ → Val.Closed w₂ →
            (∀ Aop, EffSig.opArg (Eff := Eff) (Mult := Mult) h.label op = some Aop → VrelK m Aop w₁ w₂) →
            Bang.dispatchOn op w₁ ([], h, K₁) = some cfg₁ →
            Bang.dispatchOn op w₂ ([], h, K₂) = some cfg₂ →
            CoApproxC_le m cfg₁ cfg₂)) := by
  rw [KrelS]

/-- ◊4.5b μ-floor: `CrelK 0` is VACUOUS (the metered obs at 0 — `ConvergesC_le 0` is `False`). -/
theorem crelK_zero {C : CTy Eff Mult} {ε : Eff} {c₁ c₂ : Comp} : CrelK 0 C ε c₁ c₂ := by
  rw [CrelK]; intro D K₁ K₂ _ hconv; exact absurd hconv (not_convergesC_le_zero _)

/-- ◊4.5b adequacy grounding: `CrelK n (F q A)` at the IDENTITY (nil) stack gives the whole-program
return observation. The `D = C, K = []` instance (Biernacki Lemma 2 identity). The capstone of
sub-block (a): it is the bridge `CrelK → ⊑` that the eventual `lr_sound` consumes. -/
theorem crelK_adequacy_nil {n : Nat} {q : Mult} {A : VTy Eff Mult} {ε : Eff} {c₁ c₂ : Comp}
    (h : CrelK n (CTy.F q A) ε c₁ c₂) : CoApproxC_le n ([], c₁) ([], c₂) := by
  rw [CrelK] at h
  apply h (CTy.F q A) [] []
  rw [krelS_nil]
  refine ⟨rfl, fun q' A' _ v₁ v₂ _ _ _ _ => ?_⟩
  exact ⟨1, v₂, rfl⟩


/-! ## 5.2′b ◊4.5b sub-block (b) — `KrelS`/`VrelK` DOWNWARD-CLOSURE (monotonicity)

The metered `KrelS` is NOT `∀ j ≤ n`-wrapped (unlike the old `Krel`), so monotonicity is a genuine
INDUCTION, not free sub-quantification. But it HOLDS:
- nil return-half: monotone TRIVIALLY — the goal `CoApproxC_le m ([], ret v₁) ([], ret v₂)` is
  dischargeable at ANY index (`([], ret v₂)` converges in one step), independent of the value relation.
  (The metered-observation monotonicity wall ADR-0041 hit on the OLD flat `Krel` does NOT recur here:
  the answer-typed nil case observes a RETURN, which always converges on the right.)
- letF: the frame-body `∀ m < n` restricts to `∀ m < m'` (`m' ≤ n`, sub-quantification); tail recurses.
- appF: the cap `VrelK n A` weakens DOWN to `VrelK m A` (`VrelK_mono`); tail recurses.
- handleF: tail recurses (the hole type is unchanged).
This is the `KrelF_mono` the discovery IC validated, now over the full return-half. -/

/-- ◊4.5b `VrelK` DOWNWARD-CLOSURE. Mirrors the old `Vrel_mono`, but the U-clause is `∀ j < n` (the
▷-guarded thunk): restrict `∀ j < n` to `∀ j < m` (`m ≤ n ⇒ j < m → j < n`) — structural, no Crel-down. -/
theorem VrelK_mono {n m : Nat} {A : VTy Eff Mult} {v₁ v₂ : Val}
    (hmn : m ≤ n) (hv : VrelK n A v₁ v₂) : VrelK m A v₁ v₂ := by
  match A with
  | .unit => rw [VrelK] at hv ⊢; exact hv
  | .int => rw [VrelK] at hv ⊢; exact hv
  | .U φ B =>
      rw [VrelK] at hv ⊢
      obtain ⟨c₁, c₂, rfl, rfl, hc⟩ := hv
      exact ⟨c₁, c₂, rfl, rfl, fun j hjm => hc j (lt_of_lt_of_le hjm hmn)⟩
  | .sum A B =>
      rw [VrelK] at hv ⊢
      rcases hv with ⟨w₁, w₂, rfl, rfl, hw⟩ | ⟨w₁, w₂, rfl, rfl, hw⟩
      · exact Or.inl ⟨w₁, w₂, rfl, rfl, VrelK_mono hmn hw⟩
      · exact Or.inr ⟨w₁, w₂, rfl, rfl, VrelK_mono hmn hw⟩
  | .prod A B =>
      rw [VrelK] at hv ⊢
      obtain ⟨a₁, a₂, b₁, b₂, rfl, rfl, ha, hb⟩ := hv
      exact ⟨a₁, a₂, b₁, b₂, rfl, rfl, VrelK_mono hmn ha, VrelK_mono hmn hb⟩
  | .mu A =>
      rw [VrelK] at hv ⊢
      obtain ⟨w₁, w₂, rfl, rfl, hw⟩ := hv
      exact ⟨w₁, w₂, rfl, rfl, fun j hjm => hw j (lt_of_lt_of_le hjm hmn)⟩
  | .tvar i => rw [VrelK] at hv; exact absurd hv not_false
termination_by (n, sizeOf A)

/-- ◊4.5b `KrelS` DOWNWARD-CLOSURE — by induction on the stack. The metered nil return-half is monotone
trivially (a `ret` converges at any index); the recursive cases weaken caps DOWN (`VrelK_mono`) and
restrict the frame-body `∀ m <` and recurse on the (shorter) tail. -/
theorem KrelS_mono {n m : Nat} {C D : CTy Eff Mult} {ε : Eff} :
    ∀ {K₁ K₂ : Stack}, m ≤ n → KrelS n C D ε K₁ K₂ → KrelS m C D ε K₁ K₂
  | [], [], hmn, hK => by
      rw [krelS_nil] at hK ⊢
      exact ⟨hK.1, fun q A hC v₁ v₂ _ _ _ _ => ⟨1, v₂, rfl⟩⟩
  | (Frame.letF N₁ :: K₁'), (Frame.letF N₂ :: K₂'), hmn, hK => by
      rw [krelS_letF] at hK ⊢
      obtain ⟨q, A, B, φ, hC, hbody, htail⟩ := hK
      exact ⟨q, A, B, φ, hC,
        fun k hk v₁ v₂ hc₁ hc₂ hv => hbody k (lt_of_lt_of_le hk hmn) v₁ v₂ hc₁ hc₂ hv,
        KrelS_mono hmn htail⟩
  | (Frame.appF w₁ :: K₁'), (Frame.appF w₂ :: K₂'), hmn, hK => by
      rw [krelS_appF] at hK ⊢
      obtain ⟨q, A, B, hC, hcw₁, hcw₂, hw, htail⟩ := hK
      exact ⟨q, A, B, hC, hcw₁, hcw₂, VrelK_mono hmn hw, KrelS_mono hmn htail⟩
  | (Frame.handleF h :: K₁'), (Frame.handleF h' :: K₂'), hmn, hK => by
      rw [krelS_handleF] at hK ⊢
      obtain ⟨hh, htail, hres⟩ := hK
      -- the resume conjunct at `∀ m' < n` restricts to `∀ m' < m` (m ≤ n) — monotone sub-quantification.
      exact ⟨hh, KrelS_mono hmn htail,
        fun m' hm' => hres m' (lt_of_lt_of_le hm' hmn)⟩
  | [], (_ :: _), _, hK => by simp only [KrelS] at hK
  | (_ :: _), [], _, hK => by simp only [KrelS] at hK
  | (Frame.letF _ :: _), (Frame.appF _ :: _), _, hK => by simp only [KrelS] at hK
  | (Frame.letF _ :: _), (Frame.handleF _ :: _), _, hK => by simp only [KrelS] at hK
  | (Frame.appF _ :: _), (Frame.letF _ :: _), _, hK => by simp only [KrelS] at hK
  | (Frame.appF _ :: _), (Frame.handleF _ :: _), _, hK => by simp only [KrelS] at hK
  | (Frame.handleF _ :: _), (Frame.letF _ :: _), _, hK => by simp only [KrelS] at hK
  | (Frame.handleF _ :: _), (Frame.appF _ :: _), _, hK => by simp only [KrelS] at hK
termination_by K₁ _ => K₁.length

/-! ◊4.5b sub-block (b) — effect-row subsumption for the `KrelS`/`CrelK` core. With the tail-at-`φ`
threading, the ambient `ε` appears ONLY at the `appF`/`handleF` tails (frames that don't bind a
continuation row); the `letF` clause replaces `ε` by the continuation row `φ` at the tail, and the
`nil` clause is ε-free. So `KrelS` is ε-ANTITONE by a structural pass-through that recurses on the
ε-bearing tails (appF/handleF) and leaves the letF tail (at `φ`, ε-independent) unchanged. `CrelK`
is then ε-MONOTONE (its `KrelS … ε'` premise weakens to `KrelS … ε`). -/
/-- `KrelS` ANTITONE in ε. The `letF` tail is at the continuation row `φ` (ε-independent) so it passes
through unchanged; the appF/handleF tails carry the ambient `ε` and recurse. -/
theorem KrelS_eff_anti {n : Nat} {C D : CTy Eff Mult} {ε ε' : Eff} :
    ∀ {K₁ K₂ : Stack}, ε ≤ ε' → KrelS n C D ε' K₁ K₂ → KrelS n C D ε K₁ K₂
  | [], [], _, hK => by rw [krelS_nil] at hK ⊢; exact hK
  | (Frame.letF N₁ :: K₁'), (Frame.letF N₂ :: K₂'), _, hK => by
      -- the letF tail is at `φ` (ε-independent); the whole clause is ε-free ⇒ passes through unchanged.
      rw [krelS_letF] at hK ⊢; exact hK
  | (Frame.appF w₁ :: K₁'), (Frame.appF w₂ :: K₂'), hεε', hK => by
      rw [krelS_appF] at hK ⊢
      obtain ⟨q, A, B, hC, hcw₁, hcw₂, hw, htail⟩ := hK
      exact ⟨q, A, B, hC, hcw₁, hcw₂, hw, KrelS_eff_anti hεε' htail⟩
  | (Frame.handleF h :: K₁'), (Frame.handleF h' :: K₂'), hεε', hK => by
      rw [krelS_handleF] at hK ⊢
      -- the resume conjunct is ε-free (dispatch + VrelK don't gate on ε) ⇒ passes through unchanged.
      exact ⟨hK.1, KrelS_eff_anti hεε' hK.2.1, hK.2.2⟩
  | [], (_ :: _), _, hK => by simp only [KrelS] at hK
  | (_ :: _), [], _, hK => by simp only [KrelS] at hK
  | (Frame.letF _ :: _), (Frame.appF _ :: _), _, hK => by simp only [KrelS] at hK
  | (Frame.letF _ :: _), (Frame.handleF _ :: _), _, hK => by simp only [KrelS] at hK
  | (Frame.appF _ :: _), (Frame.letF _ :: _), _, hK => by simp only [KrelS] at hK
  | (Frame.appF _ :: _), (Frame.handleF _ :: _), _, hK => by simp only [KrelS] at hK
  | (Frame.handleF _ :: _), (Frame.letF _ :: _), _, hK => by simp only [KrelS] at hK
  | (Frame.handleF _ :: _), (Frame.appF _ :: _), _, hK => by simp only [KrelS] at hK
  termination_by K₁ _ => K₁.length

/-- `KrelS` is ε-MONOTONE too (in fact ε-INVARIANT): the new answer-typed `KrelS` has NO stuck-half /
`Srel` clause (unlike the old `Krel`) — no clause GATES on `ε` (nil observes returns; letF tail is at
the continuation row `φ`; appF/handleF tails merely carry `ε` through, never check `· ≤ ε`). So `ε` is
vestigial threading and the SAME structural pass-through that proves `KrelS_eff_anti` proves the mono
direction. This is what discharges the handler ROW-CHANGE (`KrelS …φ → KrelS …e`, `e` possibly ⊋ `φ`)
in `krelS_refl`'s handleF/state/transaction arms — the SINGLE-ROW `KrelS` suffices (no two-row Biernacki
`C⟦τ₁/ε₁{τ₂/ε₂⟧` needed), because the row carried past a handleF frame is inert at the relation level.
shape: biernacki-popl18 §5.4 — set-row ρ-free collapse; the row only gates `Srel`, which this core drops. -/
theorem KrelS_eff_mono {n : Nat} {C D : CTy Eff Mult} {ε ε' : Eff} :
    ∀ {K₁ K₂ : Stack}, ε ≤ ε' → KrelS n C D ε K₁ K₂ → KrelS n C D ε' K₁ K₂
  | [], [], _, hK => by rw [krelS_nil] at hK ⊢; exact hK
  | (Frame.letF N₁ :: K₁'), (Frame.letF N₂ :: K₂'), _, hK => by
      -- the letF tail is at `φ` (ε-independent); the whole clause is ε-free ⇒ passes through unchanged.
      rw [krelS_letF] at hK ⊢; exact hK
  | (Frame.appF w₁ :: K₁'), (Frame.appF w₂ :: K₂'), hεε', hK => by
      rw [krelS_appF] at hK ⊢
      obtain ⟨q, A, B, hC, hcw₁, hcw₂, hw, htail⟩ := hK
      exact ⟨q, A, B, hC, hcw₁, hcw₂, hw, KrelS_eff_mono hεε' htail⟩
  | (Frame.handleF h :: K₁'), (Frame.handleF h' :: K₂'), hεε', hK => by
      rw [krelS_handleF] at hK ⊢
      exact ⟨hK.1, KrelS_eff_mono hεε' hK.2.1, hK.2.2⟩
  | [], (_ :: _), _, hK => by simp only [KrelS] at hK
  | (_ :: _), [], _, hK => by simp only [KrelS] at hK
  | (Frame.letF _ :: _), (Frame.appF _ :: _), _, hK => by simp only [KrelS] at hK
  | (Frame.letF _ :: _), (Frame.handleF _ :: _), _, hK => by simp only [KrelS] at hK
  | (Frame.appF _ :: _), (Frame.letF _ :: _), _, hK => by simp only [KrelS] at hK
  | (Frame.appF _ :: _), (Frame.handleF _ :: _), _, hK => by simp only [KrelS] at hK
  | (Frame.handleF _ :: _), (Frame.letF _ :: _), _, hK => by simp only [KrelS] at hK
  | (Frame.handleF _ :: _), (Frame.appF _ :: _), _, hK => by simp only [KrelS] at hK
  termination_by K₁ _ => K₁.length

/-- `KrelS` is ε-INVARIANT: the row can be replaced by ANY other row (no ordering). Corollary of
anti+mono via the bottom row (`⊥ ≤ ε`, `⊥ ≤ ε'`). This is the lemma the handler ROW-DISCHARGE consumes
in `krelS_refl`: the tail self-relates at the discharged row `φ` (IH), and the handleF frame demands it
at the body row `e` (possibly `e ⊋ φ`) — invariance bridges them with no `φ`/`e` ordering hypothesis. -/
theorem KrelS_eff_cast {n : Nat} {C D : CTy Eff Mult} {ε ε' : Eff} {K₁ K₂ : Stack}
    (hK : KrelS n C D ε K₁ K₂) : KrelS n C D ε' K₁ K₂ :=
  KrelS_eff_mono (bot_le : (⊥ : Eff) ≤ ε') (KrelS_eff_anti (bot_le : (⊥ : Eff) ≤ ε) hK)

/-- `CrelK` MONOTONE in ε: a `KrelS … ε'` stack is (by `KrelS_eff_anti`) a `KrelS … ε` stack, so the
ε-`CrelK` applies. -/
theorem CrelK_eff_mono {n : Nat} {C : CTy Eff Mult} {ε ε' : Eff} {c₁ c₂ : Comp}
    (hεε' : ε ≤ ε') (hC : CrelK n C ε c₁ c₂) : CrelK n C ε' c₁ c₂ := by
  rw [CrelK] at hC ⊢
  intro D K₁ K₂ hK
  exact hC D K₁ K₂ (KrelS_eff_anti hεε' hK)


/-! ## 5.2′c ◊4.5b sub-block (c) — `CrelK` value/head-step lemmas

`crelK_ret`: a `VrelK`-related RETURN co-behaves under EVERY `KrelS`-related stack — the answer-typed
analogue of the old `crel_ret`. Proven by induction on the stack, consuming the matching `KrelS` clause
at each frame. The tail-at-`φ` threading (the def's letF clause) is what makes the letF case close with
NO row conversion: `hbody : CrelK m B φ` meets `htail : KrelS m B D φ` — rows MATCH. Machine `ret`
behaviour per frame (`Source.step`): nil = done; `letF N::K ↦ (K, N.subst v)`; `appF v::K` = STUCK
(observation vacuous); `handleF h::K ↦ (K, ret v)` (pass-through). -/

/-- A STUCK config (`step = none`, not a nil-return) never converges within any budget. -/
theorem not_convergesC_le_of_stuck {n : Nat} {cfg : Config}
    (hstep : Source.step cfg = none) (hne : ∀ v, cfg ≠ ([], Comp.ret v)) :
    ¬ ConvergesC_le n cfg := by
  rintro ⟨v, hrun⟩
  cases n with
  | zero => rw [show Config.run 0 cfg = Result.oom from rfl] at hrun; exact absurd hrun (by simp)
  | succ k => rw [Config.run_step k cfg hne, hstep] at hrun; exact absurd hrun (by simp)

/-- ◊4.5b `crelK_ret`: a `VrelK`-related RETURN at returner type `F q A` is `CrelK`-related. -/
theorem crelK_ret {n : Nat} {q : Mult} {A : VTy Eff Mult} {e : Eff} {v₁ v₂ : Val}
    (hc₁ : Val.Closed v₁) (hc₂ : Val.Closed v₂) (hv : VrelK n A v₁ v₂) :
    CrelK n (CTy.F q A) e (Comp.ret v₁) (Comp.ret v₂) := by
  rw [CrelK]
  intro D K₁ K₂ hK
  induction K₁ generalizing K₂ A v₁ v₂ e with
  | nil =>
      cases K₂ with
      | nil => rw [krelS_nil] at hK; exact hK.2 q A rfl v₁ v₂ hc₁ hc₂ hv
      | cons fr K₂' => simp only [KrelS] at hK
  | cons fr K₁' ih =>
      cases fr with
      | letF N₁ =>
          cases K₂ with
          | cons fr₂ K₂' =>
              cases fr₂ with
              | letF N₂ =>
                  rw [krelS_letF] at hK
                  obtain ⟨q', A', B, φ, hC, hbody, htail⟩ := hK
                  rw [CTy.F.injEq] at hC; obtain ⟨rfl, rfl⟩ := hC
                  cases n with
                  | zero => intro hconv; exact absurd hconv (not_convergesC_le_zero _)
                  | succ k =>
                      refine coApproxC_le_anti_step
                        (cfg₁' := (K₁', Comp.subst v₁ N₁)) (cfg₂' := (K₂', Comp.subst v₂ N₂))
                        rfl (by intro u; simp) rfl (by intro u; simp) ?_
                      have hCrel := hbody k (Nat.lt_succ_self k) v₁ v₂ hc₁ hc₂ (VrelK_mono (Nat.le_succ k) hv)
                      rw [CrelK] at hCrel
                      exact hCrel D K₁' K₂' (KrelS_mono (Nat.le_succ k) htail)
              | _ => simp only [KrelS] at hK
          | nil => simp only [KrelS] at hK
      | appF w₁ =>
          intro hconv
          exact absurd hconv (not_convergesC_le_of_stuck rfl (by intro u; simp))
      | handleF h₁ =>
          cases K₂ with
          | cons fr₂ K₂' =>
              cases fr₂ with
              | handleF h₂ =>
                  rw [krelS_handleF] at hK
                  refine coApproxC_le_reduce
                    (cfg₁' := (K₁', Comp.ret v₁)) (cfg₂' := (K₂', Comp.ret v₂))
                    rfl (by intro u; simp) rfl (by intro u; simp) ?_
                  exact ih (K₂ := K₂') hc₁ hc₂ hv hK.2.1
              | _ => simp only [KrelS] at hK
          | nil => simp only [KrelS] at hK


/-! ## 5.2a‴ Step-index DOWNWARD-CLOSURE (`Krel_mono`) — the ◊4.5 payoff

With `Krel n := ∀ j ≤ n, (body j)` (◊4.5 downward-closed shape), `Krel`-monotonicity is FREE: a stack
related at `n` is related at every `m ≤ n` (the `∀ j ≤ m` is a sub-quantification of `∀ j ≤ n`). This
is the both-ways-monotone property the plain-Nat phrasing lacked — it enables the μ/resume `▷`-anti-
reduction (`Crel m → Crel (m+1)` via `Krel (m+1) → Krel m`). No index arithmetic, no contravariance
problem — the `∀ j ≤ n` dissolves it (IxFree/COFE, Biernacki §line-555). -/
theorem Krel_mono {Eff Mult : Type} [Lattice Eff] [OrderBot Eff] [CommSemiring Mult]
    [DecidableEq Mult] [EffSig Eff Mult] {n m : Nat} {C : CTy Eff Mult} {ε : Eff} {K₁ K₂ : Stack}
    (hmn : m ≤ n) (hK : Krel n C ε K₁ K₂) : Krel m C ε K₁ K₂ := by
  rw [Krel] at hK ⊢
  intro j hjm
  exact hK j (le_trans hjm hmn)

-- ◊4.5b: the old `Crel_mono` (blanket UPWARD `Crel m → Crel n`) is GONE — it is FALSE under the metered
-- observation. `Crel n := ∀ K, Krel n K → CoApproxC_le n` carries the index in the observation premise
-- (`ConvergesC_le n`, monotone-INCREASING in n), so a comp related at `m` is NOT blanket-related at `n ≥ m`
-- (a `≤n`-step convergence need not be a `≤m`-step one). The index-RAISING the μ-unfold / resume seams need
-- is now done by the `▷`-guarded head-expansion `Crel_head_step` (Compat.lean §B.0a) — it raises `m<n` to
-- `n` by SPENDING the machine step that the metered observation meters. That is the whole point of the ▷:
-- the lift is tied to a real reduction, not a free monotonicity. (`Krel_mono` survives — `Krel` is
-- downward-closed `∀ j ≤ n`, untouched.)

/-- ◊4.5: `Vrel` DOWNWARD-CLOSURE. With the U-clause wrapped `∀ j ≤ n, Crel j` (◊4.5), Vrel-down is
STRUCTURAL — the `U` case is quantifier-restriction (`{j ≤ m} ⊆ {j ≤ n}`), NOT a route through Crel-down
(which would need the false Krel-up). Recursion is on the TYPE (`sizeOf A`): unit/int are index-free,
sum/prod/mu recurse at strictly-smaller types, U restricts the inner `∀ j`. This is the lemma
`krel_appF_intro`'s arrow half + `EnvRel_mono` consume. -/
theorem Vrel_mono {Eff Mult : Type} [Lattice Eff] [OrderBot Eff] [CommSemiring Mult]
    [DecidableEq Mult] [EffSig Eff Mult] {n m : Nat} {A : VTy Eff Mult} {v₁ v₂ : Val}
    (hmn : m ≤ n) (hv : Vrel n A v₁ v₂) : Vrel m A v₁ v₂ := by
  -- WF on `(n, sizeOf A)` lex (mirrors Vrel's measure): sum/prod recurse at smaller TYPE same index;
  -- mu recurses at smaller INDEX. `VTy` is mutually inductive, so match on `A` (not `induction`).
  match A with
  | .unit => rw [Vrel] at hv ⊢; exact hv
  | .int => rw [Vrel] at hv ⊢; exact hv
  | .U φ B =>
      rw [Vrel] at hv ⊢
      obtain ⟨c₁, c₂, rfl, rfl, hc⟩ := hv
      -- U-clause is `∀ j ≤ n, Crel j`; restrict to `∀ j ≤ m` (m ≤ n). STRUCTURAL — no Crel-down.
      exact ⟨c₁, c₂, rfl, rfl, fun j hjm => hc j (le_trans hjm hmn)⟩
  | .sum A B =>
      rw [Vrel] at hv ⊢
      rcases hv with ⟨w₁, w₂, rfl, rfl, hw⟩ | ⟨w₁, w₂, rfl, rfl, hw⟩
      · exact Or.inl ⟨w₁, w₂, rfl, rfl, Vrel_mono hmn hw⟩
      · exact Or.inr ⟨w₁, w₂, rfl, rfl, Vrel_mono hmn hw⟩
  | .prod A B =>
      rw [Vrel] at hv ⊢
      obtain ⟨a₁, a₂, b₁, b₂, rfl, rfl, ha, hb⟩ := hv
      exact ⟨a₁, a₂, b₁, b₂, rfl, rfl, Vrel_mono hmn ha, Vrel_mono hmn hb⟩
  | .mu A =>
      -- ◊4.5 ROUTE 1: the μ-clause is `∃ fold w₁ w₂, ∀ j < n, Vrel j (unrollMu A) w₁ w₂`. Down on `mu`
      -- is STRUCTURAL — restrict the `∀ j < n` to `∀ j < m` (`m ≤ n` ⇒ `j < m → j < n`). No recursive
      -- `Vrel_mono` call (the payload already quantifies `∀ j <`); same shape as the U-clause down-step.
      rw [Vrel] at hv ⊢
      obtain ⟨w₁, w₂, rfl, rfl, hw⟩ := hv
      exact ⟨w₁, w₂, rfl, rfl, fun j hjm => hw j (lt_of_lt_of_le hjm hmn)⟩
  | .tvar i => rw [Vrel] at hv; exact absurd hv not_false
termination_by (n, sizeOf A)


/-! ## 5.2a′ Effect-row subsumption (monotonicity in ε)

The `letC` rule joins effects (`φ₁ ⊔ φ₂`): the IH relates `M` at `φ₁` and `N` at `φ₂`, but the block is
observed at `φ₁ ⊔ φ₂`. To reconcile, the relations subsume UP the row order: a relation that holds at a
SMALLER row holds at a LARGER one (more operations are "in scope", but the existing co-behaviour is
preserved). Directions (proved mutually, plain index — the ε-step needs no `▷`):
  • `Srel` MONOTONE:  `ε ≤ ε' → Srel n C ε … → Srel n C ε' …`  (the `labelEff ℓ ≤ ε ≤ ε'` membership
    still holds; the output `Crel n C ε` lifts to `Crel n C ε'` by the Crel-mono IH at the lower index).
  • `Krel` ANTITONE:  `ε ≤ ε' → Krel n C ε' … → Krel n C ε …`   (return-half is ε-free; the stuck-half
    lifts its `Srel n C ε` premise to `Srel n C ε'` via Srel-mono, then fires the ε'-Krel stuck half).
  • `Crel` MONOTONE:  `ε ≤ ε' → Crel n C ε … → Crel n C ε' …`   (a `Krel n C ε'` stack pair is, by
    Krel-antitone, also `Krel n C ε`, so the ε-Crel applies).

  shape: standard effect-subsumption for biorthogonal LRs (Biernacki popl18 §5; the row order is our
         set-row `≤`). The three move together; their lex measure is `(n, role)` with the only
         index-decreasing edge `Srel (n+1)`'s output → `Crel n`. -/
mutual
theorem Srel_eff_mono {Eff Mult : Type} [Lattice Eff] [OrderBot Eff] [CommSemiring Mult]
    [DecidableEq Mult] [EffSig Eff Mult]
    (n : Nat) (C : CTy Eff Mult) (ε ε' : Eff) (K₁ K₂ : Stack) (c₁ c₂ : Comp)
    (hεε' : ε ≤ ε') (hS : Srel n C ε K₁ K₂ c₁ c₂) : Srel n C ε' K₁ K₂ c₁ c₂ := by
  cases n with
  | zero => exact absurd hS (by simp only [Srel]; exact not_false)  -- ◊4.5: `Srel 0 = False`, vacuous.
  | succ m =>
      rw [Srel] at hS ⊢
      obtain ⟨ℓ, op, v₁, v₂, Aarg, Ares, hc₁, hc₂, hℓ, hArg, hRes, hv, hsp₁, hsp₂, hout⟩ := hS
      refine ⟨ℓ, op, v₁, v₂, Aarg, Ares, hc₁, hc₂, le_trans hℓ hεε', hArg, hRes, hv, hsp₁, hsp₂, ?_⟩
      intro u₁ u₂ hcu₁ hcu₂ hu
      exact Crel_eff_mono m C ε ε' _ _ hεε' (hout u₁ u₂ hcu₁ hcu₂ hu)
  termination_by (n, sizeOf C, 0)

theorem Krel_eff_anti {Eff Mult : Type} [Lattice Eff] [OrderBot Eff] [CommSemiring Mult]
    [DecidableEq Mult] [EffSig Eff Mult]
    (n : Nat) (C : CTy Eff Mult) (ε ε' : Eff) (K₁ K₂ : Stack)
    (hεε' : ε ≤ ε') (hK : Krel n C ε' K₁ K₂) : Krel n C ε K₁ K₂ := by
  rw [Krel] at hK ⊢
  -- ◊4.5: Krel is `∀ j ≤ n, …`; antitone-in-ε at each index `j`.
  intro j hjn
  refine ⟨(hK j hjn).1, ?_, ?_⟩
  · intro c₁ c₂ hS
    exact (hK j hjn).2.1 c₁ c₂ (Srel_eff_mono j C ε ε' K₁ K₂ c₁ c₂ hεε' hS)
  · -- arrow half (peeling): the ε' clause exposes the appF cap + `Krel j B ε'` remainder; weaken the
    -- remainder to ε (recursive antitone at the SMALLER codomain B — sizeOf B < sizeOf (arr q A B)).
    intro q A B hC
    obtain ⟨w₁, w₂, K₁', K₂', hK₁, hK₂, hcw₁, hcw₂, hw, hKrem⟩ := (hK j hjn).2.2 q A B hC
    exact ⟨w₁, w₂, K₁', K₂', hK₁, hK₂, hcw₁, hcw₂, hw,
      Krel_eff_anti j B ε ε' K₁' K₂' hεε' hKrem⟩
  termination_by (n, sizeOf C, 1)
decreasing_by
  -- ◊4.5: the antitone recursions fire at `j ≤ n` (from `Krel`'s `∀ j ≤ n` body): `Srel_eff_mono j`
  -- (role 0 < 1) and `Krel_eff_anti j B` (codomain, `sizeOf B < sizeOf (arr…)`). `j < n` drops the
  -- index; `j = n` falls to the sizeOf/role tie-break. Mirrors the `Krel`-def `decreasing_by`.
  all_goals
    first
      | (rcases Nat.lt_or_eq_of_le ‹_ ≤ _› with hlt | rfl <;>
          first | (simp_wf; exact Prod.Lex.left _ _ hlt) | decreasing_tactic)
      | decreasing_tactic

theorem Crel_eff_mono {Eff Mult : Type} [Lattice Eff] [OrderBot Eff] [CommSemiring Mult]
    [DecidableEq Mult] [EffSig Eff Mult]
    (n : Nat) (C : CTy Eff Mult) (ε ε' : Eff) (c₁ c₂ : Comp)
    (hεε' : ε ≤ ε') (hC : Crel n C ε c₁ c₂) : Crel n C ε' c₁ c₂ := by
  rw [Crel] at hC ⊢
  intro K₁ K₂ hK
  exact hC K₁ K₂ (Krel_eff_anti n C ε ε' K₁ K₂ hεε' hK)
  termination_by (n, sizeOf C, 2)
decreasing_by
  -- ◊4.5: the `Krel`-antitone recursions fire at an index `j ≤ n` (from the `∀ j ≤ n` body), so the
  -- first lex component can TIE (`j = n`). Split: `j < n` drops the index; `j = n` falls to the
  -- sizeOf/role tie-break (Srel role 0 < Krel 1; Krel at codomain B with `sizeOf B < sizeOf (arr…)`).
  -- Mirrors the Krel-def `decreasing_by`.
  all_goals
    first
      | (rcases Nat.lt_or_eq_of_le ‹_ ≤ _› with hlt | rfl <;>
          first | (simp_wf; exact Prod.Lex.left _ _ hlt) | decreasing_tactic)
      | decreasing_tactic
end


/-! ## 5.2b Closing substitutions + the environment relation `EnvRel` (ADR-0034)

The fundamental theorem `lr_fundamental` (ADR-0034 env-closed form) relates an OPEN computation to
itself under a pair of `Vrel`-RELATED substitution environments. The bare `c c` self-relation is
UNPROVABLE for an open `c`: a free `vvar i` is not `Vrel`-related to itself (`Vrel n unit (vvar 0)
(vvar 0)` demands `vvar 0 = vunit`), and the induction over `HasCTy` descends under binders into open
sub-terms. So the faithful invariant closes `c` over related environments δ₁,δ₂ (Biernacki/Ahmed
`G⟦Γ⟧`):

  shape: biernacki-popl18 §5.2 fundamental theorem (`G⟦Γ⟧η`); ahmed-esop06 closing substitution.

An environment is a `List Val` of CLOSED fillers (the CK focus is always closed). Applying it
(`closeC`) folds single `Comp.subst`s, innermost binder (index 0) first. These live HERE (not in
`Compat.lean`) because the FROZEN `lr_fundamental` statement (`Spec.lean`) references them, and
`Spec.lean` imports `LR` but not `Compat`. -/

/-- Apply a closing environment δ to a computation: substitute index 0 with `δ[0]` (renumbering),
then recurse on the tail (each `Comp.subst` removes the nearest binder). `closeC [] c = c`. -/
def closeC : List Val → Comp → Comp
  | [],      c => c
  | v :: δ,  c => closeC δ (Comp.subst v c)

/-- Apply a closing environment δ to a value (the value-level `closeC`). -/
def closeV : List Val → Val → Val
  | [],      v => v
  | u :: δ,  v => closeV δ (Val.subst u v)

/-- Pointwise `Vrel`-relatedness of two closing environments at the context `Γ`. Same length as `Γ`;
position `i` relates at type `Γ[i]`. The `▷`-free `Vrel n`: environments carry CLOSED values observed
at the current index. The `Val.Closed` conjuncts are the carrier `closeC_subst_comm` consumes (§5.2a):
they make every filler shift-invariant, so closing under a binder commutes with substitution. The
carrier is MAINTAINED by construction in the fundamental induction — the plug-values that extend δ
under a binder come from `Krel`'s return-half / `Srel`'s resume-half, both of which now quantify only
over CLOSED values (faithful to the CK machine, which plugs only closed values; ADR-0025/0030). -/
def EnvRel {Eff Mult : Type} [Lattice Eff] [OrderBot Eff] [CommSemiring Mult] [DecidableEq Mult]
    [EffSig Eff Mult] (n : Nat) : TyCtx Eff Mult → List Val → List Val → Prop
  | [],      [],        []        => True
  | A :: Γ', v₁ :: δ₁', v₂ :: δ₂' =>
      Val.Closed v₁ ∧ Val.Closed v₂ ∧ Vrel n A v₁ v₂ ∧ EnvRel n Γ' δ₁' δ₂'
  | _,       _,         _         => False

@[simp] theorem closeC_nil (c : Comp) : closeC [] c = c := rfl
@[simp] theorem closeV_nil (v : Val) : closeV [] v = v := rfl

@[simp] theorem EnvRel_nil_iff {Eff Mult : Type} [Lattice Eff] [OrderBot Eff] [CommSemiring Mult]
    [DecidableEq Mult] [EffSig Eff Mult] (n : Nat) (δ₁ δ₂ : List Val) :
    EnvRel n ([] : TyCtx Eff Mult) δ₁ δ₂ ↔ δ₁ = [] ∧ δ₂ = [] := by
  cases δ₁ <;> cases δ₂ <;> simp [EnvRel]

/-- ◊4.5: `EnvRel` DOWNWARD-CLOSURE — pointwise `Vrel_mono`. The Kripke fundamental theorem closes
`c` over environments at EVERY `j ≤ n` (the `vthunk`/binder-extension cases need the IH at the lower
index), and `EnvRel`-down lets `vrel_fund`/`crel_fund` supply the environment at any `j ≤ n` from the
ambient `EnvRel n`. Structural now that `Vrel`-down is (◊4.5 Vrel U-clause `∀j≤n`). -/
theorem EnvRel_mono {Eff Mult : Type} [Lattice Eff] [OrderBot Eff] [CommSemiring Mult]
    [DecidableEq Mult] [EffSig Eff Mult] {n m : Nat} :
    ∀ {Γ : TyCtx Eff Mult} {δ₁ δ₂ : List Val}, m ≤ n → EnvRel n Γ δ₁ δ₂ → EnvRel m Γ δ₁ δ₂
  | [],      [],        [],        _,   _  => trivial
  | _A :: _, _v₁ :: _,  _v₂ :: _,  hmn, h => by
      obtain ⟨hc₁, hc₂, hv, hrest⟩ := h
      exact ⟨hc₁, hc₂, Vrel_mono hmn hv, EnvRel_mono hmn hrest⟩
  | [],      _ :: _,    _,         _,   h => absurd h (by simp [EnvRel])
  | [],      [],        _ :: _,    _,   h => absurd h (by simp [EnvRel])
  | _ :: _,  [],        _,         _,   h => absurd h (by simp [EnvRel])
  | _ :: _,  _ :: _,    [],        _,   h => absurd h (by simp [EnvRel])


/-! ## 5.2′d ◊4.5b — `EnvRelK` (the env relation over `VrelK`, for the migrated fundamental theorem).
Structurally identical to `EnvRel` (Closed ∧ Closed ∧ rel ∧ rec); only the value relation is `VrelK`.
The `crelK_fund`/`vrelK_fund` migration closes open terms over `EnvRelK`-related environments. -/

def EnvRelK {Eff Mult : Type} [Lattice Eff] [OrderBot Eff] [CommSemiring Mult] [DecidableEq Mult]
    [EffSig Eff Mult] (n : Nat) : TyCtx Eff Mult → List Val → List Val → Prop
  | [],      [],        []        => True
  | A :: Γ', v₁ :: δ₁', v₂ :: δ₂' =>
      Val.Closed v₁ ∧ Val.Closed v₂ ∧ VrelK n A v₁ v₂ ∧ EnvRelK n Γ' δ₁' δ₂'
  | _,       _,         _         => False

@[simp] theorem EnvRelK_nil_iff {Eff Mult : Type} [Lattice Eff] [OrderBot Eff] [CommSemiring Mult]
    [DecidableEq Mult] [EffSig Eff Mult] (n : Nat) (δ₁ δ₂ : List Val) :
    EnvRelK n ([] : TyCtx Eff Mult) δ₁ δ₂ ↔ δ₁ = [] ∧ δ₂ = [] := by
  cases δ₁ <;> cases δ₂ <;> simp [EnvRelK]

/-- `EnvRelK` DOWNWARD-CLOSURE — pointwise `VrelK_mono`. -/
theorem EnvRelK_mono {Eff Mult : Type} [Lattice Eff] [OrderBot Eff] [CommSemiring Mult]
    [DecidableEq Mult] [EffSig Eff Mult] {n m : Nat} :
    ∀ {Γ : TyCtx Eff Mult} {δ₁ δ₂ : List Val}, m ≤ n → EnvRelK n Γ δ₁ δ₂ → EnvRelK m Γ δ₁ δ₂
  | [],      [],        [],        _,   _  => trivial
  | _A :: _, _v₁ :: _,  _v₂ :: _,  hmn, h => by
      obtain ⟨hc₁, hc₂, hv, hrest⟩ := h
      exact ⟨hc₁, hc₂, VrelK_mono hmn hv, EnvRelK_mono hmn hrest⟩
  | [],      _ :: _,    _,         _,   h => absurd h (by simp [EnvRelK])
  | [],      [],        _ :: _,    _,   h => absurd h (by simp [EnvRelK])
  | _ :: _,  [],        _,         _,   h => absurd h (by simp [EnvRelK])
  | _ :: _,  _ :: _,    [],        _,   h => absurd h (by simp [EnvRelK])


/-! ## 5.3 Adequacy building blocks toward `lr_sound`

`lr_sound : (∀ n, Crel n B e c₁ c₂) → c₁ ⊑ c₂`. Biorthogonal adequacy
(benton-hur-icfp09, pitts-step-indexed): `Crel` co-behaves against EVERY
`Krel`-related stack pair, so instantiating at a stack pair `(C, C)` known to be
`Krel`-self-related yields the `⊑`-clause for context `C`.

The CLOSED case (`C = []`) is provable from the relations ALONE — `krel_nil`
below — and gives `lr_sound_closed` (empty-context / whole-program adequacy). The
ARBITRARY-context case needs `Krel n B e C C` for every `C`, i.e. Krel-reflexivity
(the "identity extension" lemma), which is the FUNDAMENTAL-THEOREM direction — see
the dependency note on `lr_sound` in `Bang/Spec.lean`. -/

/-- A returned value always converges (one machine step: `([], ret v) ↦ done v`). -/
theorem converges_ret (v : Val) : Converges (Comp.ret v) :=
  ⟨1, v, rfl⟩

-- ◊4.5: `crel_zero` (the old universal `Crel 0` base) is REMOVED. Under `Srel 0 := False` it is no
-- longer true for arbitrary `c` (`Krel 0` is inhabited at `F q A` and does not force arbitrary
-- `CoApprox`). It is also no longer NEEDED: the `krel_*` frame-extension lemmas are now stated at general
-- `n` (their stuck halves are vacuous at every `j` via `Srel 0 := False`), so each compat core proves its
-- `n = 0` case by its ordinary main argument — no `cases n`/`crel_zero` base. Single source of truth: a
-- dead lemma carrying a `sorry` is worse than no lemma.

/-- An UNHANDLED operation never converges: under the empty stack `splitAt [] = none`,
so `step ([], up ℓ op v) = none` and the machine is immediately stuck. -/
theorem not_converges_up_nil (ℓ : Label) (op : OpId) (v : Val) :
    ¬ Converges (Comp.up ℓ op v) := by
  rintro ⟨fuel, w, hfuel⟩
  -- `Source.eval fuel (up …) = Config.run fuel ([], up …)`; the step is `none` (stuck), never `done`.
  cases fuel with
  | zero => simp [Source.eval, Config.run] at hfuel
  | succ k =>
      have hstuck : Config.run (k + 1) ([], Comp.up ℓ op v) = Result.stuck := by
        rw [Config.run_step k ([], Comp.up ℓ op v) (by intro u; simp)]
        rfl
      rw [show Source.eval (k+1) (Comp.up ℓ op v)
            = Config.run (k+1) ([], Comp.up ℓ op v) from rfl, hstuck] at hfuel
      simp at hfuel

/-- An UNHANDLED operation never converges UNDER ANY STACK: if no frame of `K` handles `(ℓ, op)`
(`splitAt K ℓ op = none`), then `plug K (up ℓ op v)` runs to a stuck config and never `done`s.
Generalizes `not_converges_up_nil` (the `K = []` case) to an arbitrary stack — the workhorse that
collapses the STUCK half of every frame-extension `Krel` lemma to vacuous truth (`CoApprox` is
`False → _`). The machine refocuses `([], plug K (up …))` to `(K, up …)` via `run_plug`, then
`dispatch K ℓ op v = (splitAt K …).bind _ = none` ⇒ `step = none` ⇒ stuck. -/
theorem not_converges_up_splitNone (K : Stack) (ℓ : Label) (op : OpId) (v : Val)
    (hsplit : Bang.splitAt K ℓ op = none) :
    ¬ Converges (Stack.plug K (Comp.up ℓ op v)) := by
  -- the focused config (K, up …) is stuck at every fuel: step = dispatch = none (splitAt = none).
  have hstuck : ∀ j w, Config.run j (K, Comp.up ℓ op v) ≠ Result.done w := by
    intro j w
    cases j with
    | zero => simp [Config.run]
    | succ k =>
        rw [Config.run_step k (K, Comp.up ℓ op v) (by intro u; simp)]
        have hdisp : Source.step (K, Comp.up ℓ op v) = none := by
          show dispatch K ℓ op v = none
          unfold dispatch; rw [hsplit]; rfl
        rw [hdisp]; simp
  rintro ⟨fuel, w, hfuel⟩
  rw [Stack.plug] at hfuel
  -- Source.eval fuel (plug K …) = run fuel ([], plug K …); bump to (fuel + K.length), refocus.
  have hev : Config.run fuel ([], Bang.plug K (Comp.up ℓ op v)) = Result.done w := hfuel
  have hbig : Config.run (fuel + K.length) ([], Bang.plug K (Comp.up ℓ op v)) = Result.done w :=
    Config.run_done_add K.length fuel _ w hev
  rw [run_plug K (Comp.up ℓ op v) fuel] at hbig
  exact hstuck fuel w hbig

/-- ◊4.5b CONFIG-LEVEL form: the focused config `(K, up ℓ op v)` with `splitAt K = none` is STUCK at
every fuel (`step = dispatch = none`), so it never converges within ANY step bound. This is what the
metered STUCK halves consume — `CoApproxC_le j (K, up…) _` is vacuous because `ConvergesC_le j (K, up…)`
is `False`. No `plug`/refocus (config level): the `+K.length` offset never enters. -/
theorem config_stuck_up_splitNone (K : Stack) (ℓ : Label) (op : OpId) (v : Val)
    (hsplit : Bang.splitAt K ℓ op = none) : ∀ j w, Config.run j (K, Comp.up ℓ op v) ≠ Result.done w := by
  intro j w
  cases j with
  | zero => simp [Config.run]
  | succ k =>
      rw [Config.run_step k (K, Comp.up ℓ op v) (by intro u; simp)]
      have hdisp : Source.step (K, Comp.up ℓ op v) = none := by
        show dispatch K ℓ op v = none
        unfold dispatch; rw [hsplit]; rfl
      rw [hdisp]; simp

/-- `ConvergesC_le j (K, up…)` is `False` when `K` does not handle `(ℓ,op)` — the metered stuck-half
discharge. -/
theorem not_convergesC_le_up_splitNone {j : Nat} (K : Stack) (ℓ : Label) (op : OpId) (v : Val)
    (hsplit : Bang.splitAt K ℓ op = none) : ¬ ConvergesC_le j (K, Comp.up ℓ op v) := by
  rintro ⟨w, hw⟩; exact config_stuck_up_splitNone K ℓ op v hsplit j w hw

/-- The empty stack is `Krel`-self-related at every SUCCESSOR index/type/row: the RETURN half
holds because `ret v` always converges (so `CoApprox` is `True → True`), and the STUCK half
holds because an `Srel (n+1)`-pair under `[]` is an unhandled `up`, which never converges (so
`CoApprox` is `False → _`). This is the closed-program observation context.

The `n+1` is necessary: at index 0, `Srel 0 = True` carries no operation shape, so the stuck
half would demand `CoApprox c₁ c₂` for ARBITRARY `c₁ c₂` — false. (This is the standard
step-indexed convention that a relation-as-PREMISE is only informative at successor indices;
the `∀ n` hypothesis of `lr_sound` lets the proof pick `n+1`.) -/
theorem krel_nil_succ {Eff Mult : Type} [Lattice Eff] [OrderBot Eff] [CommSemiring Mult]
    [DecidableEq Mult] [EffSig Eff Mult] (n : Nat) (q : Mult) (A : VTy Eff Mult) (e : Eff) :
    Krel (n + 1) (CTy.F q A) e ([] : Stack) ([] : Stack) := by
  unfold Krel
  -- ◊4.5 downward-closed shape: `∀ j ≤ n+1, (return ∧ stuck ∧ arrow)`.
  intro j _hj
  refine ⟨?_, ?_, ?_⟩
  · -- return half: config ([], ret v₂) always converges (`run 1 = done v₂`); metered premise unused.
    intro q A _ v₁ v₂ _ _ _
    exact fun _ => ⟨1, v₂, rfl⟩
  · -- stuck half: an `Srel j`-pair under [] is an unhandled `up`, which never converges (even unbounded);
    -- the metered premise `ConvergesC_le j ([], up …)` implies the unbounded `Converges`, contradiction.
    intro c₁ c₂ hS hconv
    -- ◊4.5 (Srel 0 := False): `j = 0` is VACUOUS (`Srel 0 = False`, `hS` is absurd). `j = k+1` is the REAL
    -- unhandled-op argument — `Srel (k+1)` forces `c₁ = up ℓ op v₁`, never convergent under `[]`.
    cases j with
    | succ k =>
        unfold Srel at hS
        obtain ⟨ℓ, op, v₁, v₂, Aarg, Ares, hc₁, _, _, _, _, _, _, _, _⟩ := hS
        obtain ⟨w, hw⟩ := hconv
        rw [hc₁] at hw
        exact absurd (⟨k + 1, w, hw⟩ : Converges (Comp.up ℓ op v₁)) (not_converges_up_nil ℓ op v₁)
    | zero => exact absurd hS (by unfold Srel; exact not_false)
  · -- ARROW half: VACUOUS — the whole-program answer context `[]` is a RETURNER type `F q A`, not an
    -- arrow (ADR-0038 peeling form: `[]` is not appF-capped; arrow-typed whole programs are bare lams,
    -- stuck at `[]`, so `⊑` is vacuous there — the empty stack only observes returners).
    intro q' A' B' hEq
    exact absurd hEq (by simp)

/-- ◊4.5b `KrelS` nil self-relation: the empty stack relates to itself at answer type = hole type
`F q A`. The return-half is index-free (`ret` always converges); `C = D` holds (both `F q A`). Works
at EVERY index (the metered nil return-half is monotone-trivial — no `n+1` needed, unlike the old
`krel_nil_succ` whose stuck-half needed `Srel (n+1)`; `KrelS`'s nil has no stuck-half). -/
theorem krelS_nil_succ {Eff Mult : Type} [Lattice Eff] [OrderBot Eff] [CommSemiring Mult]
    [DecidableEq Mult] [EffSig Eff Mult] (n : Nat) (q : Mult) (A : VTy Eff Mult) (e : Eff) :
    KrelS n (CTy.F q A) (CTy.F q A) e ([] : Stack) ([] : Stack) := by
  rw [krelS_nil]
  exact ⟨rfl, fun q' A' _ v₁ v₂ _ _ _ _ => ⟨1, v₂, rfl⟩⟩

/-- WHOLE-PROGRAM adequacy: `Crel` implies the closed (empty-context) observation
`Converges c₁ → Converges c₂`. The `⊑` restricted to `C = []`. Provable from `Crel` +
`krel_nil_succ` alone (no fundamental theorem). RETURNER type only (`F q A`): the empty-stack
observation is vacuous at non-returner types (ADR-0038).

◊4.5b ADEQUACY STRIP: the metered `Crel n` observes only `≤ n` left-steps, so instantiate at the
WITNESSING fuel — `Converges c₁` gives a fuel `f+1` with `run (f+1) ([],c₁) = done`, which IS
`ConvergesC_le (f+1) ([], c₁)`. `Crel (f+1)`'s metered `CoApproxC_le (f+1)` then discharges to the
unbounded right `Converges c₂`. The frozen `∀ n` statement is what makes the right fuel available. -/
theorem lr_sound_closed {Eff Mult : Type} [Lattice Eff] [OrderBot Eff] [CommSemiring Mult]
    [DecidableEq Mult] [EffSig Eff Mult] {c₁ c₂ : Comp} {e : Eff} {q : Mult} {A : VTy Eff Mult}
    (h : ∀ n, Crel n (CTy.F q A) e c₁ c₂) : Converges c₁ → Converges c₂ := by
  rintro ⟨fuel, v, hfuel⟩
  -- `Source.eval fuel c₁ = Config.run fuel ([], c₁) = done v` ⇒ fuel ≥ 1 (run 0 = oom).
  cases fuel with
  | zero => simp [Source.eval, Config.run] at hfuel
  | succ f =>
      have hC := h (f + 1)
      unfold Crel at hC
      -- the metered left premise: ConvergesC_le (f+1) ([], c₁), witnessed by hfuel.
      have hconv : ConvergesC_le (f + 1) ([], c₁) :=
        ⟨v, hfuel⟩
      have hright := hC [] [] (krel_nil_succ f q A e) hconv
      -- hright : ∃ m w, Config.run m ([], c₂) = done w  =  Converges c₂.
      obtain ⟨m, w, hm⟩ := hright
      exact ⟨m, w, hm⟩

end Bang
