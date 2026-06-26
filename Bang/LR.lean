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
-- ◊4.5b (g): `ctxApprox`/`⊑` is now typed by a `HasStack` premise (needs the `EffSig` instance to type
-- the observation context's operations). Auto-included only where referenced (Lean drops unused vars).
variable [EffSig Eff Mult]


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

/-- THE SPEC NOTION. Contextual approximation (`⊑`) and equivalence (`≈`).

◊4.5b (g): the observation context `C` is restricted to those WELL-TYPED at the focus `(e, B)` — the
STANDARD contextual-equivalence quantifier (a context observes terms at their type). The earlier UNTYPED
quantifier (`∀ C : Cxt`) was a DEFECT: `lr_sound` is FALSE over ill-typed-at-hole contexts (a `letF N::K'`
context with `B ≠ F q A` plugs a non-returner where the machine expects a returner — the `KrelS` letF
clause is FALSE, not vacuous), and an untyped context can distinguish `Crel`-related terms it has no right
to observe. The type `(e, B)` is carried as IMPLICIT params (inferred at every use site — `lr_sound`'s
`{e B}` supply them), so the `⊑`/`≈` NOTATION and every `_ ⊑ _` / `_ ≈ _` statement stay BYTE-IDENTICAL;
only this definition gains the typing premise. `HasStack C e B eo (F qo Ao)` (returner answer type `Co`,
ADR-0038: only returners are observed) is exactly what `krelS_refl` consumes to produce the self-relation. -/
def ctxApprox {e : Eff} {B : CTy Eff Mult} (c₁ c₂ : Comp) : Prop :=
  ∀ (C : Cxt) (eo : Eff) (qo : Mult) (Ao : VTy Eff Mult),
    HasStack C e B eo (CTy.F qo Ao) → Converges (Cxt.plug C c₁) → Converges (Cxt.plug C c₂)
def ctxEquiv {e : Eff} {B : CTy Eff Mult} (c₁ c₂ : Comp) : Prop :=
  ctxApprox (e := e) (B := B) c₁ c₂ ∧ ctxApprox (e := e) (B := B) c₂ c₁
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
    (hstep : Source.step cfg = some cfg') (hne : ∀ g v, cfg ≠ (g, [], Comp.ret v)) :
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
    (hne : ∀ g v, cfg₂ ≠ (g, [], Comp.ret v)) (h : ∃ m w, Config.run m cfg₂' = Result.done w) :
    ∃ m w, Config.run m cfg₂ = Result.done w := by
  obtain ⟨m, w, hm⟩ := h
  exact ⟨m + 1, w, by rw [Config.run_step m cfg₂ hne, hstep]; exact hm⟩

/-- THE generic `▷`-anti-reduction over the metered observation. Both sides take ONE config step
(left metered `−1`, right unbounded anti-reduce); the reducts related at the DROPPED index `n` give the
redexes related at `n+1`. Every frame-reduce return-half (`letF`/`appF`/`handleF`) and every `CIStep`
head-expansion routes through this ONE lemma — the factoring that localizes the metering (ADR-0041
alt-1 overturn). NO `K.length` offset: config level. -/
theorem coApproxC_le_anti_step {n : Nat} {cfg₁ cfg₁' cfg₂ cfg₂' : Config}
    (hstep₁ : Source.step cfg₁ = some cfg₁') (hne₁ : ∀ g v, cfg₁ ≠ (g, [], Comp.ret v))
    (hstep₂ : Source.step cfg₂ = some cfg₂') (hne₂ : ∀ g v, cfg₂ ≠ (g, [], Comp.ret v))
    (h : CoApproxC_le n cfg₁' cfg₂') : CoApproxC_le (n + 1) cfg₁ cfg₂ := by
  intro hconv
  rw [convergesC_le_step hstep₁ hne₁] at hconv
  exact converges_anti_step hstep₂ hne₂ (h hconv)

/-- NON-dropping frame anti-reduction (the β/return-bridge form). When the reduct is already related at
the SAME index `n` (not the dropped one), the left's lost step (`n → n-1` via the step) is re-padded by
monotonicity (`ConvergesC_le (n-1) ⊆ ConvergesC_le n`). Used by `appF`/`handleF` REDUCE bridges where the
reduct relation comes from a body IH at the full index `n`, not a `▷`-dropped one. -/
theorem coApproxC_le_reduce {n : Nat} {cfg₁ cfg₁' cfg₂ cfg₂' : Config}
    (hstep₁ : Source.step cfg₁ = some cfg₁') (hne₁ : ∀ g v, cfg₁ ≠ (g, [], Comp.ret v))
    (hstep₂ : Source.step cfg₂ = some cfg₂') (hne₂ : ∀ g v, cfg₂ ≠ (g, [], Comp.ret v))
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
-- ◊4.5b (g): `≈` now carries an implicit focus type `{e B}` (the typed-context restriction). The
-- substitution-irrelevance is QUANTIFIED over EVERY focus type — the two fillers give `≈`-equal terms at
-- whatever type the observation context demands. The implicit `{e B}` are bound here (def-level ∀).
def NotEvaluated (i : Nat) (c : Comp) : Prop :=
  ∀ (v₁ v₂ : Val) {e : Eff} {B : CTy Eff Mult}, ctxEquiv (e := e) (B := B) (Comp.substFrom i v₁ c) (Comp.substFrom i v₂ c)


/-! ### 5.0a Plug/run bridge + `seq_unit` (the left-unit head reduction)

`seq_unit` is purely OPERATIONAL — no LR machinery. `seqComp (ret v) c = letC (ret v) (shift c)`
head-reduces to `c` in TWO machine steps (`letC (ret v) N ↦ N[v]`, then `(shift c)[v] = c` by
`Comp.subst_shift`), and this holds in EVERY context. The bridge `run_plug` says loading a
`plug C x` term reaches the focused config `(C, x)` after `C.length` push steps, which lets the
context-quantified `ctxEquiv` reduce to a config-level co-convergence. -/

/-! ### 5.0a′ The `run_plug` reshape machinery (transcribed from `scratch/RunPlugReshapeProbe.lean`,
kernel-engineer `runplug`, proven axiom-clean ⊆ {propext, Quot.sound}).

Under ADR-0055 global-fresh minting, `plug` ERASES handler-frame ids and re-running a plugged context
RE-MINTS canonical ids (counter 0,1,2,… in outermost-push order) and SUBSTITUTES each minted capability
into everything it encloses. So running `plug C c` does NOT reach `(C, c)`; it reaches the CANONICAL
reached config `reshape 0 [] C c`. The main lemma:

  run_plug_reshape : Config.run (n + C.length) (0, [], plug C c)
                   = Config.run n (handlerCount C, canonStack C c, capSubstInto C c)

plus the renaming-invariance BRIDGE the inc-5 LR consumes (`plug`/`reshape`/`splitAtId` commute with an
injective id-renaming → the canonical-id config and the original-id config run to renamed-equal results).
SoT for this block is the probe; it is re-homed here verbatim because `Bang/LR.lean` may import
`Bang.Operational` directly (a scratch file could not import the §2/§3 renaming primitives). -/
namespace RunPlugReshape
open Bang.EffectRow (Label)

/-- The machine's PUSH/handle sub-step — `stepReshape`: the restriction of `Source.step` to the three
"descend into the focus" arms (PUSH `letC`/`app`, and the `handle` MINT). On those foci it agrees with
`Source.step` DEFINITIONALLY; on any other focus it is the identity. -/
def stepReshape : Config → Config
  | (g, K, .letC M N)   => (g, .letF N :: K, M)
  | (g, K, .app M v)    => (g, .appF v :: K, M)
  | (g, K, .handle h M) => (g + 1, .handleF g h :: K, Comp.subst (.vcap g h.label) M)
  | cfg                 => cfg

theorem step_eq_stepReshape_letC (g : Nat) (K : EvalCtx) (M N : Comp) :
    Source.step (g, K, .letC M N) = some (stepReshape (g, K, .letC M N)) := rfl
theorem step_eq_stepReshape_app (g : Nat) (K : EvalCtx) (M : Comp) (v : Val) :
    Source.step (g, K, .app M v) = some (stepReshape (g, K, .app M v)) := rfl
theorem step_eq_stepReshape_handle (g : Nat) (K : EvalCtx) (h : Handler) (M : Comp) :
    Source.step (g, K, .handle h M) = some (stepReshape (g, K, .handle h M)) := rfl

/-- The reached config — `reshape g K C c` is the config that `(g, K, plug C c)` runs to after exactly
`C.length` steps (the machine descends every frame of `plug C c`). Recursion is on `C` (innermost-first). -/
def reshape (g : Nat) (K : EvalCtx) : EvalCtx → Comp → Config
  | [], c      => (g, K, c)
  | fr :: C', c => stepReshape (reshape g K C' (fr.wrapStep c))

@[simp] theorem reshape_nil (g : Nat) (K : EvalCtx) (c : Comp) :
    reshape g K [] c = (g, K, c) := rfl
@[simp] theorem reshape_cons (g : Nat) (K : EvalCtx) (fr : Frame) (C' : EvalCtx) (c : Comp) :
    reshape g K (fr :: C') c = stepReshape (reshape g K C' (fr.wrapStep c)) := rfl

theorem stepReshape_letC (cfg : Config) (a b : Comp) (h : cfg.2.2 = .letC a b) :
    stepReshape cfg = (cfg.1, .letF b :: cfg.2.1, a) := by
  obtain ⟨g, K, φ⟩ := cfg; simp only at h; subst h; rfl
theorem stepReshape_app (cfg : Config) (a : Comp) (v : Val) (h : cfg.2.2 = .app a v) :
    stepReshape cfg = (cfg.1, .appF v :: cfg.2.1, a) := by
  obtain ⟨g, K, φ⟩ := cfg; simp only at h; subst h; rfl
theorem stepReshape_handle (cfg : Config) (hd : Handler) (a : Comp) (h : cfg.2.2 = .handle hd a) :
    stepReshape cfg = (cfg.1 + 1, .handleF cfg.1 hd :: cfg.2.1, Comp.subst (.vcap cfg.1 hd.label) a) := by
  obtain ⟨g, K, φ⟩ := cfg; simp only at h; subst h; rfl

theorem step_fires_letC (cfg : Config) (a b : Comp) (h : cfg.2.2 = .letC a b) :
    Source.step cfg = some (stepReshape cfg) := by obtain ⟨g, K, φ⟩ := cfg; simp only at h; subst h; rfl
theorem step_fires_app (cfg : Config) (a : Comp) (v : Val) (h : cfg.2.2 = .app a v) :
    Source.step cfg = some (stepReshape cfg) := by obtain ⟨g, K, φ⟩ := cfg; simp only at h; subst h; rfl
theorem step_fires_handle (cfg : Config) (hd : Handler) (a : Comp) (h : cfg.2.2 = .handle hd a) :
    Source.step cfg = some (stepReshape cfg) := by obtain ⟨g, K, φ⟩ := cfg; simp only at h; subst h; rfl

/-- `applyCaps` — the cumulative cap-substitution `reshape` applies to its focus. We do NOT need its
closed form — only that the focus is `applyCaps L c` for SOME list `L`, which preserves `c`'s head. -/
def applyCaps : List (Nat × Val) → Comp → Comp
  | [], c        => c
  | (k, v) :: L, c => applyCaps L (Comp.substFrom k v c)
def applyCapsV : List (Nat × Val) → Val → Val
  | [], v        => v
  | (k, u) :: L, v => applyCapsV L (Val.substFrom k u v)
def applyCapsH : List (Nat × Val) → Handler → Handler
  | [], h        => h
  | (k, u) :: L, h => applyCapsH L (Handler.substFrom k u h)
def bumpL (L : List (Nat × Val)) : List (Nat × Val) := L.map (fun p => (p.1 + 1, Val.shift p.2))

theorem applyCaps_snoc (L : List (Nat × Val)) (k : Nat) (v : Val) (c : Comp) :
    applyCaps (L ++ [(k, v)]) c = Comp.substFrom k v (applyCaps L c) := by
  induction L generalizing c with
  | nil => rfl
  | cons p L ih => obtain ⟨k', v'⟩ := p; simp only [applyCaps, List.cons_append, ih]

theorem applyCaps_letC (L : List (Nat × Val)) (a b : Comp) :
    applyCaps L (.letC a b) = .letC (applyCaps L a) (applyCaps (bumpL L) b) := by
  induction L generalizing a b with
  | nil => rfl
  | cons p L ih => obtain ⟨k, v⟩ := p; simp only [applyCaps, Comp.substFrom, bumpL, List.map_cons, ih]
theorem applyCaps_app (L : List (Nat × Val)) (a : Comp) (v : Val) :
    applyCaps L (.app a v) = .app (applyCaps L a) (applyCapsV L v) := by
  induction L generalizing a v with
  | nil => rfl
  | cons p L ih => obtain ⟨k, u⟩ := p; simp only [applyCaps, applyCapsV, Comp.substFrom, ih]
theorem applyCaps_handle (L : List (Nat × Val)) (hd : Handler) (a : Comp) :
    applyCaps L (.handle hd a) = .handle (applyCapsH L hd) (applyCaps (bumpL L) a) := by
  induction L generalizing hd a with
  | nil => rfl
  | cons p L ih =>
    obtain ⟨k, u⟩ := p; simp only [applyCaps, applyCapsH, Comp.substFrom, bumpL, List.map_cons, ih]

/-- **Focus characterization**: `reshape`'s focus is `applyCaps L c` for some `L` — it pins the head
constructor (each `substFrom` preserves it), so the next frame's `Source.step` fires. -/
theorem reshape_focus (C : EvalCtx) : ∀ (g : Nat) (K : EvalCtx) (c : Comp),
    ∃ L, (reshape g K C c).2.2 = applyCaps L c := by
  induction C with
  | nil => intro g K c; exact ⟨[], rfl⟩
  | cons fr C' ih =>
    intro g K c
    rw [reshape_cons]
    obtain ⟨L, hL⟩ := ih g K (fr.wrapStep c)
    cases fr with
    | letF N =>
      refine ⟨L, ?_⟩
      rw [stepReshape_letC _ (applyCaps L c) (applyCaps (bumpL L) N) (by rw [hL]; exact applyCaps_letC L c N)]
    | appF v =>
      refine ⟨L, ?_⟩
      rw [stepReshape_app _ (applyCaps L c) (applyCapsV L v) (by rw [hL]; exact applyCaps_app L c v)]
    | handleF m h =>
      refine ⟨bumpL L ++ [(0, .vcap (reshape g K C' (Comp.handle h c)).1 (applyCapsH L h).label)], ?_⟩
      rw [stepReshape_handle _ (applyCapsH L h) (applyCaps (bumpL L) c)
            (by rw [hL]; exact applyCaps_handle L h c)]
      simp only [Frame.wrapStep] at hL ⊢
      rw [applyCaps_snoc]

/-- A `reshape … (fr.wrapStep c)` config's focus head is `fr`'s constructor, so `Source.step` fires
and equals `stepReshape`. The single transition the run-equation consumes. -/
theorem reshape_step_fires (g : Nat) (K : EvalCtx) (C : EvalCtx) (fr : Frame) (c : Comp) :
    Source.step (reshape g K C (fr.wrapStep c))
      = some (stepReshape (reshape g K C (fr.wrapStep c))) := by
  obtain ⟨L, hL⟩ := reshape_focus C g K (fr.wrapStep c)
  cases fr with
  | letF N =>
      refine step_fires_letC _ (applyCaps L c) (applyCaps (bumpL L) N) ?_
      rw [hL]; simp only [Frame.wrapStep]; exact applyCaps_letC L c N
  | appF v =>
      refine step_fires_app _ (applyCaps L c) (applyCapsV L v) ?_
      rw [hL]; simp only [Frame.wrapStep]; exact applyCaps_app L c v
  | handleF m h =>
      refine step_fires_handle _ (applyCapsH L h) (applyCaps (bumpL L) c) ?_
      rw [hL]; simp only [Frame.wrapStep]; exact applyCaps_handle L h c

/-- The focus is never a `ret`, so a `reshape … (fr.wrapStep c)` config is never the terminal returning
config — the side condition `Config.run_step` needs. -/
theorem reshape_wrapStep_ne_ret (g : Nat) (K : EvalCtx) (C : EvalCtx) (fr : Frame) (c : Comp) :
    ∀ (g' : Nat) (v : Val), reshape g K C (fr.wrapStep c) ≠ (g', [], .ret v) := by
  intro g' v h
  obtain ⟨L, hL⟩ := reshape_focus C g K (fr.wrapStep c)
  have h2 : (reshape g K C (fr.wrapStep c)).2.2 = Comp.ret v := by rw [h]
  rw [hL] at h2
  cases fr with
  | letF N => rw [show Frame.wrapStep (Frame.letF N) c = Comp.letC c N from rfl, applyCaps_letC] at h2;
              exact absurd h2 (by simp)
  | appF w => rw [show Frame.wrapStep (Frame.appF w) c = Comp.app c w from rfl, applyCaps_app] at h2;
              exact absurd h2 (by simp)
  | handleF m hd => rw [show Frame.wrapStep (Frame.handleF m hd) c = Comp.handle hd c from rfl,
                      applyCaps_handle] at h2; exact absurd h2 (by simp)

/-- `reshape` advances the counter by `handlerCount C` (each handle frame mints one fresh id). -/
theorem reshape_counter (C : EvalCtx) : ∀ (g : Nat) (K : EvalCtx) (c : Comp),
    (reshape g K C c).1 = g + handlerCount C := by
  induction C with
  | nil => intro g K c; simp [handlerCount]
  | cons fr C' ih =>
    intro g K c
    rw [reshape_cons]
    obtain ⟨L, hL⟩ := reshape_focus C' g K (fr.wrapStep c)
    have hcnt : (reshape g K C' (fr.wrapStep c)).1 = g + handlerCount C' := ih g K (fr.wrapStep c)
    cases fr with
    | letF N =>
      rw [stepReshape_letC _ (applyCaps L c) (applyCaps (bumpL L) N)
            (by rw [hL]; simp only [Frame.wrapStep]; exact applyCaps_letC L c N)]
      simpa only [handlerCount] using hcnt
    | appF v =>
      rw [stepReshape_app _ (applyCaps L c) (applyCapsV L v)
            (by rw [hL]; simp only [Frame.wrapStep]; exact applyCaps_app L c v)]
      simpa only [handlerCount] using hcnt
    | handleF m h =>
      rw [stepReshape_handle _ (applyCapsH L h) (applyCaps (bumpL L) c)
            (by rw [hL]; simp only [Frame.wrapStep]; exact applyCaps_handle L h c)]
      simp only [handlerCount]; omega

/-- **THE MAIN LEMMA core** (generalized over starting counter `g`, stack `K`, fuel `n`): each frame
of `C` is one machine step (`reshape_step_fires`); the outer frames `C'` are consumed first by the IH. -/
theorem run_reshape_gen : ∀ (C : EvalCtx) (n g : Nat) (K : EvalCtx) (c : Comp),
    Config.run (n + C.length) (g, K, plug C c) = Config.run n (reshape g K C c) := by
  intro C
  induction C with
  | nil => intro n g K c; simp [plug]
  | cons fr C' ih =>
    intro n g K c
    rw [plug_cons, show (fr :: C').length = C'.length + 1 from rfl,
        show n + (C'.length + 1) = (n + 1) + C'.length by omega,
        ih (n + 1) g K (fr.wrapStep c), reshape_cons,
        Config.run_step n _ (reshape_wrapStep_ne_ret g K C' fr c),
        reshape_step_fires g K C' fr c]

/-- `canonStack`/`capSubstInto` — the stack and focus of the canonical reached config. -/
def canonStack (C : EvalCtx) (c : Comp) : EvalCtx := (reshape 0 [] C c).2.1
def capSubstInto (C : EvalCtx) (c : Comp) : Comp := (reshape 0 [] C c).2.2

/-- **`run_plug_reshape`** (the contract): running `plug C c` for `C.length + n` steps from the fresh
machine equals running the canonical reached config for `n` steps. -/
theorem run_plug_reshape (n : Nat) (C : EvalCtx) (c : Comp) :
    Config.run (n + C.length) (0, [], plug C c)
      = Config.run n (handlerCount C, canonStack C c, capSubstInto C c) := by
  rw [run_reshape_gen C n 0 [] c]
  have hc : (reshape 0 [] C c).1 = handlerCount C := by
    have := reshape_counter C 0 [] c; simpa using this
  show Config.run n (reshape 0 [] C c)
      = Config.run n (handlerCount C, canonStack C c, capSubstInto C c)
  unfold canonStack capSubstInto
  rw [← hc]

/-! #### The renaming bridge — id-agnosticism, for the inc-5 LR's `KrelS`. -/

/-- Relabel ONLY a handler frame's id (handlers/sub-terms fixed). `RenameInvarianceProbe §2`. -/
def reId (σ : Nat → Nat) : Frame → Frame
  | .letF N      => .letF N
  | .appF v      => .appF v
  | .handleF n h => .handleF (σ n) h

/-- **`plug` ignores handler-frame ids**: the reconstructed term `plug C c` does not depend on `C`'s
ids — `wrapStep` discards them. -/
theorem plug_reId (σ : Nat → Nat) (c : Comp) :
    ∀ K : EvalCtx, plug (K.map (reId σ)) c = plug K c := by
  intro K
  induction K generalizing c with
  | nil => rfl
  | cons fr K ih => cases fr <;> simp only [List.map_cons, reId, plug, ih]

/-- **`reshape` ignores handler-frame ids** (the bridge keystone): the canonical reached config — hence
`canonStack`/`capSubstInto` — is INVARIANT under any relabeling `reId σ` of `C`'s frames. -/
theorem reshape_reId (σ : Nat → Nat) (C : EvalCtx) : ∀ (g : Nat) (K : EvalCtx) (c : Comp),
    reshape g K (C.map (reId σ)) c = reshape g K C c := by
  induction C with
  | nil => intro g K c; rfl
  | cons fr C' ih =>
    intro g K c
    simp only [List.map_cons, reshape_cons]
    rw [show (reId σ fr).wrapStep c = fr.wrapStep c from by cases fr <;> rfl, ih]

/-! Renaming over the term language (`RenameInvarianceProbe §1/§3`) — for `splitAtId_rename`. -/

mutual
def renameV (σ : Nat → Nat) : Val → Val
  | .vcap n ℓ   => .vcap (σ n) ℓ
  | .vthunk c   => .vthunk (renameC σ c)
  | .inl v      => .inl (renameV σ v)
  | .inr v      => .inr (renameV σ v)
  | .pair a b   => .pair (renameV σ a) (renameV σ b)
  | .fold v     => .fold (renameV σ v)
  | v           => v
def renameC (σ : Nat → Nat) : Comp → Comp
  | .ret v        => .ret (renameV σ v)
  | .letC M N     => .letC (renameC σ M) (renameC σ N)
  | .force v      => .force (renameV σ v)
  | .lam M        => .lam (renameC σ M)
  | .app M v      => .app (renameC σ M) (renameV σ v)
  | .perform c op v => .perform (renameV σ c) op (renameV σ v)
  | .handle h M   => .handle (renameH σ h) (renameC σ M)
  | .case v N₁ N₂ => .case (renameV σ v) (renameC σ N₁) (renameC σ N₂)
  | .split v N    => .split (renameV σ v) (renameC σ N)
  | .unfold v     => .unfold (renameV σ v)
  | c             => c
def renameH (σ : Nat → Nat) : Handler → Handler
  | .state ℓ s  => .state ℓ (renameV σ s)
  | .throws ℓ   => .throws ℓ
  | .transaction ℓ Θ => .transaction ℓ (Θ.map (renameV σ))
end

def renameF (σ : Nat → Nat) : Frame → Frame
  | .letF N      => .letF (renameC σ N)
  | .appF v      => .appF (renameV σ v)
  | .handleF n h => .handleF (σ n) (renameH σ h)

def renameK (σ : Nat → Nat) : EvalCtx → EvalCtx := List.map (renameF σ)

@[simp] theorem renameK_cons (σ : Nat → Nat) (fr : Frame) (K : EvalCtx) :
    renameK σ (fr :: K) = renameF σ fr :: renameK σ K := rfl

/-- **DISPATCH commutes with an injective id-renaming**: the identity search `splitAtId` is stable
under `renameK σ` for injective `σ`. The inc-5 LR uses this to keep `KrelS`'s step-matching across the
canonical↔original relabeling at every later `perform`. -/
theorem splitAtId_rename (σ : Nat → Nat) (hσ : Function.Injective σ) (n : Nat) :
    ∀ K : EvalCtx,
      splitAtId (renameK σ K) (σ n)
        = (splitAtId K n).map (fun x => (renameK σ x.1, renameH σ x.2.1, renameK σ x.2.2)) := by
  intro K
  induction K with
  | nil => rfl
  | cons fr K ih =>
    cases fr with
    | handleF m h =>
      simp only [renameK_cons, renameF, splitAtId]
      by_cases hmn : m = n
      · subst hmn; rw [if_pos rfl, if_pos rfl]; rfl
      · rw [if_neg hmn, if_neg (fun h => hmn (hσ h)), ih]
        cases splitAtId K n <;> rfl
    | letF N =>
      simp only [renameK_cons, renameF, splitAtId, ih]
      cases splitAtId K n <;> rfl
    | appF v =>
      simp only [renameK_cons, renameF, splitAtId, ih]
      cases splitAtId K n <;> rfl

/-- **The bridge corollary**: running `plug C c` (for ANY id-relabeling of `C`) reaches the SAME
canonical config. -/
theorem run_plug_reId (n : Nat) (σ : Nat → Nat) (C : EvalCtx) (c : Comp) :
    Config.run (n + C.length) (0, [], plug (C.map (reId σ)) c)
      = Config.run n (handlerCount C, canonStack C c, capSubstInto C c) := by
  rw [plug_reId σ c C, run_plug_reshape n C c]

end RunPlugReshape

/-- Loading `plug C c` and running it reaches the CANONICAL machine-shaped config `reshape 0 [] C c`
after the `C.length` push steps that re-decompose `plug C c`. Under ADR-0055 minting the reached config
is NOT `(C, c)` — the machine mints CANONICAL ids for `C`'s handle frames (`canonStack C c`) and
substitutes the minted caps into the focus (`capSubstInto C c`). This is `run_plug_reshape`, proven
axiom-clean by kernel-engineer `runplug` (`scratch/RunPlugReshapeProbe.lean`, transcribed §5.0a′). -/
theorem run_plug (C : EvalCtx) (c : Comp) (n : Nat) :
    Config.run (n + C.length) (0, [], Bang.plug C c)
      = Config.run n (handlerCount C, RunPlugReshape.canonStack C c, RunPlugReshape.capSubstInto C c) :=
  RunPlugReshape.run_plug_reshape n C c

/-- `Converges (plug C x)` is config-level convergence of the MACHINE-SHAPED reached config
`(handlerCount C, canonStack C x, capSubstInto C x)`. ◊inc-5 STATEMENT FIX: the old RHS `(handlerCount
C, C, x)` was FALSE — a raw focus `x` with a handle-bound de Bruijn cap-var (`vvar 0`) is STUCK on
`perform (vvar 0) …` (the machine's `perform` only fires on `vcap`), whereas `plug C x` substitutes the
minted caps and converges. The faithful RHS is the canonical reached config the reshape delivers; the
bridge from it to `krelS_refl`'s raw-`C` self-observation is the id-agnosticism relational step (handled
at the consumer sites in `lr_sound`/Compat). Proof: `run_plug_reshape` + `Config.run_done_add`. -/
theorem converges_plug_iff (C : EvalCtx) (x : Comp) :
    Converges (Bang.plug C x) ↔
      ∃ n w, Config.run n (handlerCount C, RunPlugReshape.canonStack C x,
        RunPlugReshape.capSubstInto C x) = Result.done w := by
  constructor
  · rintro ⟨fuel, v, hv⟩
    -- `hv : Source.eval fuel (plug C x) = done v` = `Config.run fuel (0,[],plug C x) = done v` (defeq).
    refine ⟨fuel, v, ?_⟩
    have hpad : Config.run (fuel + C.length) (0, [], Bang.plug C x) = Result.done v :=
      Config.run_done_add C.length fuel _ v hv
    rwa [RunPlugReshape.run_plug_reshape fuel C x] at hpad
  · rintro ⟨n, w, hw⟩
    refine ⟨n + C.length, w, ?_⟩
    show Config.run (n + C.length) (0, [], Bang.plug C x) = Result.done w
    rw [RunPlugReshape.run_plug_reshape n C x]; exact hw

/-- The head reduction at config level: `(g, C, seqComp (ret v) c)` runs to `(g, C, c)` after 2 steps.
The two transitions (letC PUSH + let-bind) do NOT mint (no `handle`), so the counter `g` threads
unchanged — this re-keys cleanly (no reshape). NAMED sorry for step 1; proven in step 2 alongside the
metering spine. -/
theorem seqComp_ret_run (v : Val) (c : Comp) (C : EvalCtx) (n g : Nat) :
    Config.run (n + 2) (g, C, seqComp (Comp.ret v) c) = Config.run n (g, C, c) := by
  sorry  -- inc-5 step 2 (mechanical: letC steps thread `g`, no mint)

theorem seq_unit_proof (v : Val) {c : Comp} {e : Eff} {B : CTy Eff Mult} :
    ctxEquiv (e := e) (B := B) (seqComp (Comp.ret v) c) c := by
  -- inc-5 step 2 (metering spine): the proof bridges via `converges_plug_iff`/`seqComp_ret_run`
  -- (both machine-shaped-reshape dependent). NAMED sorry until the reshape lands.
  sorry


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
def raise (ℓ : Label) (v : Val) : Comp := Comp.perform (Val.vcap 0 ℓ) "raise" v
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

/-! ### 5.2a′ Cap-closedness — REMOVED (ADR-0054).

The `Val.CapClosed` block (the ADR-0045 cap-shift analogue of `Val.Closed`) is DELETED: ADR-0054
removed the cap-shift entirely (`Comp.substFrom`'s `handle` arm is now an ordinary de-Bruijn binder
descent, no `Val.shiftCap`), so `Val.shiftCapFrom`/`Val.shiftCap` no longer exist and the
shiftcap-invariance the `closeC_handle*` lemmas once consumed is the identity. Those lemmas re-key to
the plain-binder `Val.Closed` form (Compat, the `closeC_lam` shape). -/


/-! ## 5.2 LR — the answer-typed core (`VrelK`/`CrelK`/`KrelS`) IS the frozen `Vrel`/`Crel`/`EnvRel`

◊4.5b sub-block (g) MIGRATION (this commit): the flat `Crel`/`Krel`/`Srel` (the Phase-A focus-typed
relations) have been DELETED — they ERASED Biernacki's answer type, which the producer-`up` resume needs
for the `Krel⊸Crel` biorthogonal composition (Lemma 2). The answer-typed rebuild below (`VrelK`/`CrelK`/
`KrelS`, ADR-0041) is now the canonical LR. The FROZEN `Vrel`/`Crel`/`EnvRel` names (referenced by the
`lr_sound`/`lr_fundamental` statements in `Spec.lean`) are re-pointed to the K-relations via `abbrev`
(below `EnvRelK`), signature byte-identical — no frozen-statement change. -/

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
  -- cap (ADR-0054): a capability value relates by IDENTITY + label (machine-shaped — both sides name
  -- the SAME handler instance `m` for the SAME effect `ℓ`). Closed-value / stack-agnostic like the base
  -- types; the value→stack resolution linkage lives in the diagonal's `WellScoped`, not here.
  | _,     .cap ℓ,   v₁, v₂ => ∃ m, v₁ = Val.vcap m ℓ ∧ v₂ = Val.vcap m ℓ
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
        -- machine-shaped (ADR-0054/0055): the observed config carries the fresh-id counter. The
        -- canonical fresh counter for a stack `K` is `handlerCount K` (ids `0..hc-1` are live, `hc`
        -- is next-fresh). CrelK/KrelS signatures are frozen, so the counter is DERIVED, not a param.
        CoApproxC_le n (handlerCount K₁, K₁, c₁) (handlerCount K₂, K₂, c₂)
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
            CoApproxC_le n (0, [], Comp.ret v₁) (0, [], Comp.ret v₂))
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
      -- ◊4.5b-append: the handlers are RELATED (`HandlerRel n`), not necessarily EQUAL. `HandlerRel`
      -- fixes the LABEL + KIND (so `splitAt`/`handlesOp`/`Handler.label` fire IDENTICALLY — they ignore
      -- the stored state, Operational:230-242) and relates the STORED STATE via `VrelK` (state: one cell;
      -- transaction: pointwise heap). EQUAL handlers (`h₁=h₂`, the old sub-block-f form) were TOO STRONG:
      -- `put w` reinstalls `state ℓ w₁` vs `state ℓ w₂` with `w₁ ~ w₂` RELATED-not-equal, so `h₁=h₂` made
      -- the resume conjunct unprovable for state/txn (the append-crux wall, build-traced 2026-06-24). The
      -- relational form is WF-safe: `VrelK n` on the handler state is a role-1→role-0 drop (= the appF cap).
      -- throws relates by LABEL only (no state) so the zero-shot case recovers the old behaviour. The
      -- match is INLINED (can't forward-ref `HandlerRel`, defined post-block); `krelS_handleF` exposes it.
      | (Frame.handleF n₁ h₁ :: K₁'), (Frame.handleF n₂ h₂ :: K₂') =>
          -- machine-shaped (ADR-0055): the two frames carry their generative identity. Under canonical
          -- ids (both stacks reached by runs from a fresh counter) related frames share the id, so the
          -- relation REQUIRES `n₁ = n₂` (the diagonal has it by reflexivity; the resume dispatch keys on it).
          n₁ = n₂ ∧
          (match h₁, h₂ with
           | Handler.throws ℓ₁,         Handler.throws ℓ₂         => ℓ₁ = ℓ₂
           | Handler.state ℓ₁ s₁,       Handler.state ℓ₂ s₂       =>
               ℓ₁ = ℓ₂ ∧ ∃ S : VTy Eff Mult, VrelK n S s₁ s₂
           | Handler.transaction ℓ₁ Θ₁, Handler.transaction ℓ₂ Θ₂ =>
               ℓ₁ = ℓ₂ ∧ Θ₁.length = Θ₂.length ∧
                 ∀ i : Nat, i < Θ₁.length →
                   VrelK n (VTy.int : VTy Eff Mult) (Θ₁.getD i (Val.vint 0)) (Θ₂.getD i (Val.vint 0))
           | _, _ => False) ∧ KrelS n C D ε K₁' K₂'
            -- ◊4.5b-append RESUME CONJUNCT (config-level re-expression of old `Srel` LR:554), now threading
            -- the CAPTURED CONTINUATION `Kᵢ`. state/txn dispatch KEEPS `Kᵢ` (Operational:295): the dispatched
            -- config is `(Kᵢ ++ handleF(state ℓ s')::Kₒ, ret r)`. The conjunct quantifies over a related
            -- captured continuation `Kᵢ ~ Kᵢ'` (at SOME hole type/row), so the resume value `r` flows through
            -- it to reach the body type before hitting `Kₒ`. The producer EXTRACTS this via
            -- `krelS_splitAt_decomp` (now also returns the inner-prefix relation); throws supplies it with `Kᵢ`
            -- arbitrary (discarded zero-shot). No op-interface in the def — the producer supplies `Aarg`.
            -- the inner prefix relates at ANSWER type `C` (= the handler-frame hole; handleF preserves it).
            -- FIXED to `C`, not quantified — lets the state/txn consumer `krelS_append` onto the tail (hole
            -- `C`) with no extra `Dᵢ=C` obligation; the producer instantiates at the SPLIT-POINT hole that
            -- `krelS_splitAt_decomp` returns (threaded existentially as the conjunct's `C`).
            ∧ (∀ m, m < n → ∀ (op : OpId) (w₁ w₂ : Val) (Cᵢ : CTy Eff Mult) (εᵢ : Eff)
                  (Kᵢ Kᵢ' : Stack) (cfg₁ cfg₂ : EvalCtx × Comp),
                Bang.handlesOp h₁ h₁.label op = true →
                Val.Closed w₁ → Val.Closed w₂ →
                (∀ Aop, EffSig.opArg (Eff := Eff) (Mult := Mult) h₁.label op = some Aop → VrelK m Aop w₁ w₂) →
                KrelS m Cᵢ C εᵢ Kᵢ Kᵢ' →
                -- the captured continuation's hole `Cᵢ` is a RETURNER at the op-RESULT type (the resume
                -- value flows into `Kᵢ` there). state/txn need this for `crelK_ret` to bridge the resume
                -- through `Kᵢ`; the producer supplies it from the `up` typing (Cᵢ = F q (opRes)). throws
                -- discards `Kᵢ` so it never consults this.
                (∀ Aᵣ, EffSig.opRes (Eff := Eff) (Mult := Mult) h₁.label op = some Aᵣ →
                  ∃ qᵣ, Cᵢ = CTy.F qᵣ Aᵣ) →
                Bang.dispatchOn n₁ op w₁ (Kᵢ, h₁, K₁') = some cfg₁ →
                Bang.dispatchOn n₂ op w₂ (Kᵢ', h₂, K₂') = some cfg₂ →
                -- ◊4.5b-strengthen (path (a)): KREL-CARRYING resume conclusion. The opaque
                -- `CoApproxC_le m cfg₁ cfg₂` is too weak for a handler NESTED in a captured continuation:
                -- it cannot lift through an appended outer tail (convergence of the shorter stack ⊬
                -- convergence of the longer; carries no `r₁~r₂`/`S₁~S₂` to reconstruct via `crelK_ret`).
                -- Instead we EXPOSE the decomposition every resuming/aborting dispatch satisfies: the
                -- dispatched config is a RETURN config `(Sᵢ, ret rⱼ)` whose stacks are `KrelS`-related at
                -- a RETURNER hole `F qᵣ Aᵣ` and whose returned values are `VrelK`-related at `Aᵣ`. From
                -- THIS, `crelK_ret rⱼ` recovers the plain `CoApproxC_le m cfg₁ cfg₂` (T=[]) AND the
                -- appended-tail `CoApproxC_le m (Sᵢ++T₁,ret r₁)(Sᵢ'++T₂,ret r₂)` (the nested case, via
                -- `krelS_append` onto the related Sᵢ). shape: biernacki-popl18 §5.4 resumptive clause —
                -- the resume value + its captured continuation, made first-class. -/
                (∃ (qᵣ : Mult) (Aᵣ : VTy Eff Mult) (r₁ r₂ : Val) (Sᵢ Sᵢ' : Stack) (eₛ : Eff),
                    cfg₁ = (Sᵢ, Comp.ret r₁) ∧ cfg₂ = (Sᵢ', Comp.ret r₂) ∧
                    Val.Closed r₁ ∧ Val.Closed r₂ ∧ VrelK m Aᵣ r₁ r₂ ∧
                    KrelS m (CTy.F qᵣ Aᵣ) D eₛ Sᵢ Sᵢ'))
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
        CoApproxC_le n (0, [], Comp.ret v₁) (0, [], Comp.ret v₂)) := by
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

/-- ◊4.5b-append the RELATIONAL handler condition (state lives IN the handler, related-not-equal). Fixes
label+kind (so `splitAt`/`handlesOp` fire identically — they ignore stored state) + relates the stored
state via `VrelK` (state: one cell; transaction: pointwise heap). throws relates by label only. Defined
AFTER the mutual block (references `VrelK`); `rfl`-equal to the inlined match in `KrelS`'s handleF clause
so `krelS_handleF` exposes it. Explicit `Eff Mult` type params (Handler is monomorphic, so they can't be
inferred from the scrutinees). -/
def HandlerRel (Eff Mult : Type) [Lattice Eff] [OrderBot Eff] [CommSemiring Mult] [DecidableEq Mult]
    [EffSig Eff Mult] (n : Nat) : Handler → Handler → Prop
  | Handler.throws ℓ₁,         Handler.throws ℓ₂         => ℓ₁ = ℓ₂
  | Handler.state ℓ₁ s₁,       Handler.state ℓ₂ s₂       =>
      ℓ₁ = ℓ₂ ∧ ∃ S : VTy Eff Mult, VrelK (Eff := Eff) (Mult := Mult) n S s₁ s₂
  | Handler.transaction ℓ₁ Θ₁, Handler.transaction ℓ₂ Θ₂ =>
      ℓ₁ = ℓ₂ ∧ Θ₁.length = Θ₂.length ∧
        ∀ i : Nat, i < Θ₁.length →
          VrelK (Eff := Eff) (Mult := Mult) n VTy.int (Θ₁.getD i (Val.vint 0)) (Θ₂.getD i (Val.vint 0))
  | _, _ => False

@[simp] theorem krelS_handleF {n : Nat} {C D : CTy Eff Mult} {ε : Eff} {nh nh' : Nat} {h h' : Handler}
    {K₁ K₂ : Stack} :
    KrelS n C D ε (Frame.handleF nh h :: K₁) (Frame.handleF nh' h' :: K₂) ↔
      (nh = nh' ∧ HandlerRel Eff Mult n h h' ∧ KrelS n C D ε K₁ K₂
        ∧ (∀ m, m < n → ∀ (op : OpId) (w₁ w₂ : Val) (Cᵢ : CTy Eff Mult) (εᵢ : Eff)
              (Kᵢ Kᵢ' : Stack) (cfg₁ cfg₂ : EvalCtx × Comp),
            Bang.handlesOp h h.label op = true →
            Val.Closed w₁ → Val.Closed w₂ →
            (∀ Aop, EffSig.opArg (Eff := Eff) (Mult := Mult) h.label op = some Aop → VrelK m Aop w₁ w₂) →
            KrelS m Cᵢ C εᵢ Kᵢ Kᵢ' →
            (∀ Aᵣ, EffSig.opRes (Eff := Eff) (Mult := Mult) h.label op = some Aᵣ →
              ∃ qᵣ, Cᵢ = CTy.F qᵣ Aᵣ) →
            Bang.dispatchOn nh op w₁ (Kᵢ, h, K₁) = some cfg₁ →
            Bang.dispatchOn nh' op w₂ (Kᵢ', h', K₂) = some cfg₂ →
            (∃ (qᵣ : Mult) (Aᵣ : VTy Eff Mult) (r₁ r₂ : Val) (Sᵢ Sᵢ' : Stack) (eₛ : Eff),
                cfg₁ = (Sᵢ, Comp.ret r₁) ∧ cfg₂ = (Sᵢ', Comp.ret r₂) ∧
                Val.Closed r₁ ∧ Val.Closed r₂ ∧ VrelK m Aᵣ r₁ r₂ ∧
                KrelS m (CTy.F qᵣ Aᵣ) D eₛ Sᵢ Sᵢ'))) := by
  cases h <;> cases h' <;> simp only [KrelS, HandlerRel]

/-- ◊4.5b μ-floor: `CrelK 0` is VACUOUS (the metered obs at 0 — `ConvergesC_le 0` is `False`). -/
theorem crelK_zero {C : CTy Eff Mult} {ε : Eff} {c₁ c₂ : Comp} : CrelK 0 C ε c₁ c₂ := by
  rw [CrelK]; intro D K₁ K₂ _ hconv; exact absurd hconv (not_convergesC_le_zero _)

/-- ◊4.5b adequacy grounding: `CrelK n (F q A)` at the IDENTITY (nil) stack gives the whole-program
return observation. The `D = C, K = []` instance (Biernacki Lemma 2 identity). The capstone of
sub-block (a): it is the bridge `CrelK → ⊑` that the eventual `lr_sound` consumes. -/
theorem crelK_adequacy_nil {n : Nat} {q : Mult} {A : VTy Eff Mult} {ε : Eff} {c₁ c₂ : Comp}
    (h : CrelK n (CTy.F q A) ε c₁ c₂) : CoApproxC_le n (0, [], c₁) (0, [], c₂) := by
  rw [CrelK] at h
  have := h (CTy.F q A) [] []
  simp only [handlerCount] at this
  apply this
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
  | .cap ℓ => rw [VrelK] at hv ⊢; exact hv   -- cap relation is index-independent (id + label)
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
  | (Frame.handleF nh h :: K₁'), (Frame.handleF nh' h' :: K₂'), hmn, hK => by
      rw [krelS_handleF] at hK ⊢
      obtain ⟨hid, hh, htail, hres⟩ := hK
      -- ◊4.5b-append: the relational handler condition is downward-mono on its `VrelK` state; the resume
      -- conjunct at `∀ m' < n` restricts to `∀ m' < m` (m ≤ n) — monotone sub-quantification.
      refine ⟨hid, ?_, KrelS_mono hmn htail, fun m' hm' => hres m' (lt_of_lt_of_le hm' hmn)⟩
      cases h <;> cases h' <;> simp only [HandlerRel] at hh ⊢
      · -- state/state: relate the stored cell at the smaller index
        exact ⟨hh.1, hh.2.imp fun _ hv => VrelK_mono hmn hv⟩
      · -- throws/throws: label-only, index-independent
        exact hh
      · -- transaction/transaction: pointwise heap mono
        exact ⟨hh.1, hh.2.1, fun i hi => VrelK_mono hmn (hh.2.2 i hi)⟩
  | [], (_ :: _), _, hK => by simp only [KrelS] at hK
  | (_ :: _), [], _, hK => by simp only [KrelS] at hK
  | (Frame.letF _ :: _), (Frame.appF _ :: _), _, hK => by simp only [KrelS] at hK
  | (Frame.letF _ :: _), (Frame.handleF _ _ :: _), _, hK => by simp only [KrelS] at hK
  | (Frame.appF _ :: _), (Frame.letF _ :: _), _, hK => by simp only [KrelS] at hK
  | (Frame.appF _ :: _), (Frame.handleF _ _ :: _), _, hK => by simp only [KrelS] at hK
  | (Frame.handleF _ _ :: _), (Frame.letF _ :: _), _, hK => by simp only [KrelS] at hK
  | (Frame.handleF _ _ :: _), (Frame.appF _ :: _), _, hK => by simp only [KrelS] at hK
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
  | (Frame.handleF nh h :: K₁'), (Frame.handleF nh' h' :: K₂'), hεε', hK => by
      rw [krelS_handleF] at hK ⊢
      -- the resume conjunct is ε-free (dispatch + VrelK don't gate on ε) ⇒ passes through unchanged.
      exact ⟨hK.1, hK.2.1, KrelS_eff_anti hεε' hK.2.2.1, hK.2.2.2⟩
  | [], (_ :: _), _, hK => by simp only [KrelS] at hK
  | (_ :: _), [], _, hK => by simp only [KrelS] at hK
  | (Frame.letF _ :: _), (Frame.appF _ :: _), _, hK => by simp only [KrelS] at hK
  | (Frame.letF _ :: _), (Frame.handleF _ _ :: _), _, hK => by simp only [KrelS] at hK
  | (Frame.appF _ :: _), (Frame.letF _ :: _), _, hK => by simp only [KrelS] at hK
  | (Frame.appF _ :: _), (Frame.handleF _ _ :: _), _, hK => by simp only [KrelS] at hK
  | (Frame.handleF _ _ :: _), (Frame.letF _ :: _), _, hK => by simp only [KrelS] at hK
  | (Frame.handleF _ _ :: _), (Frame.appF _ :: _), _, hK => by simp only [KrelS] at hK
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
  | (Frame.handleF nh h :: K₁'), (Frame.handleF nh' h' :: K₂'), hεε', hK => by
      rw [krelS_handleF] at hK ⊢
      exact ⟨hK.1, hK.2.1, KrelS_eff_mono hεε' hK.2.2.1, hK.2.2.2⟩
  | [], (_ :: _), _, hK => by simp only [KrelS] at hK
  | (_ :: _), [], _, hK => by simp only [KrelS] at hK
  | (Frame.letF _ :: _), (Frame.appF _ :: _), _, hK => by simp only [KrelS] at hK
  | (Frame.letF _ :: _), (Frame.handleF _ _ :: _), _, hK => by simp only [KrelS] at hK
  | (Frame.appF _ :: _), (Frame.letF _ :: _), _, hK => by simp only [KrelS] at hK
  | (Frame.appF _ :: _), (Frame.handleF _ _ :: _), _, hK => by simp only [KrelS] at hK
  | (Frame.handleF _ _ :: _), (Frame.letF _ :: _), _, hK => by simp only [KrelS] at hK
  | (Frame.handleF _ _ :: _), (Frame.appF _ :: _), _, hK => by simp only [KrelS] at hK
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
    (hstep : Source.step cfg = none) (hne : ∀ g v, cfg ≠ (g, [], Comp.ret v)) :
    ¬ ConvergesC_le n cfg := by
  rintro ⟨v, hrun⟩
  cases n with
  | zero => rw [show Config.run 0 cfg = Result.oom from rfl] at hrun; exact absurd hrun (by simp)
  | succ k => rw [Config.run_step k cfg hne, hstep] at hrun; exact absurd hrun (by simp)

/-- ◊4.5b `crelK_ret`: a `VrelK`-related RETURN at returner type `F q A` is `CrelK`-related. -/
theorem crelK_ret {n : Nat} {q : Mult} {A : VTy Eff Mult} {e : Eff} {v₁ v₂ : Val}
    (hc₁ : Val.Closed v₁) (hc₂ : Val.Closed v₂)
    (hv : VrelK n A v₁ v₂) :
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
                      -- letF reduce: `step (g, letF N₁::K₁', ret v₁) = (g, K₁', subst v₁ N₁)`, counter
                      -- `g = handlerCount (letF N₁::K₁') = handlerCount K₁'` UNCHANGED (letF adds no
                      -- handler). So the landed config's counter matches the IH/`CrelK` observation —
                      -- the configs are inferred from `rfl`; no explicit tuple annotation needed.
                      refine coApproxC_le_anti_step rfl (by intro g u; simp) rfl (by intro g u; simp) ?_
                      have hCrel := hbody k (Nat.lt_succ_self k) v₁ v₂ hc₁ hc₂ (VrelK_mono (Nat.le_succ k) hv)
                      rw [CrelK] at hCrel
                      exact hCrel D K₁' K₂' (KrelS_mono (Nat.le_succ k) htail)
              | _ => simp only [KrelS] at hK
          | nil => simp only [KrelS] at hK
      | appF w₁ =>
          intro hconv
          exact absurd hconv (not_convergesC_le_of_stuck rfl (by intro g u; simp))
      | handleF nh₁ h₁ =>
          cases K₂ with
          | cons fr₂ K₂' =>
              cases fr₂ with
              | handleF nh₂ h₂ =>
                  -- ◊inc-5 COUNTER-AGNOSTICISM GAP (named sorry). handleF pass-through on a `ret`:
                  -- `step (g, handleF nh₁ h₁::K₁', ret v₁) = (g, K₁', ret v₁)` keeps the counter `g`, but
                  -- `handlerCount (handleF nh₁ h₁::K₁') = handlerCount K₁' + 1`, so the landed config is
                  -- `(handlerCount K₁' + 1, K₁', ret v₁)` while `ih`/`CrelK` observes `(handlerCount K₁',
                  -- K₁', ret v₁)`. The popped handler's id is now dead and the `+1` counter is still fresh
                  -- (> every live id of K₁'), so convergence is INVARIANT under it — but discharging it
                  -- needs the run-renaming lemma (`Config.run` commutes with an injective id-renaming),
                  -- the DYNAMIC half NOT yet transcribed (RunPlugReshape supplies only the static
                  -- `plug`/`splitAtId` halves). SAME gap as `crelK_fund`'s up/perform arm; reconnects when
                  -- the run-renaming / counter-shift bridge lands.
                  sorry
              | _ => simp only [KrelS] at hK
          | nil => simp only [KrelS] at hK



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

@[simp] theorem closeC_nil (c : Comp) : closeC [] c = c := rfl
@[simp] theorem closeV_nil (v : Val) : closeV [] v = v := rfl


/-! ## 5.2′d ◊4.5b — `EnvRelK` (the env relation over `VrelK`, for the migrated fundamental theorem).
Structurally identical to `EnvRel` (Closed ∧ Closed ∧ rel ∧ rec); only the value relation is `VrelK`.
The `crelK_fund`/`vrelK_fund` migration closes open terms over `EnvRelK`-related environments. -/

-- ADR-0045 (typed-LR re-key, Inc 0b): each filler also carries `Val.CapClosed` (the lexical-cap
-- analogue of `Val.Closed`). The `closeC` handler-distribution / substitution-commutation lemmas need
-- the closing-env fillers to be SHIFTCAP-invariant (so the `Val.shiftCap` a `handle` cap-binder
-- introduces vanishes — Compat.lean `closeC_handle*`/`*_swap_closed`). The machine's fillers ARE
-- cap-closed (every substituted `perform` names a stacked handler — the lexical-cap discipline), so this
-- is a faithful invariant, not a restriction; it is carried HERE so the fundamental theorem's binder
-- descent has it at every closing step.
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


/-! ## 5.2′g ◊4.5b sub-block (g) — the FROZEN names re-pointed to the answer-typed core.

The `lr_sound`/`lr_fundamental` statements in `Spec.lean` are stated over `Vrel`/`Crel`/`EnvRel`. Those
names now ABBREVIATE the answer-typed relations (`VrelK`/`CrelK`/`EnvRelK`) — signature byte-identical
(`D` is quantified internally inside `CrelK`/`KrelS`), so the frozen statements do not change shape. The
old flat relations were deleted above; this is the body-swap the (g) migration calls for. -/

abbrev Vrel {Eff Mult : Type} [Lattice Eff] [OrderBot Eff] [CommSemiring Mult] [DecidableEq Mult]
    [EffSig Eff Mult] : Nat → VTy Eff Mult → Val → Val → Prop := VrelK

abbrev Crel {Eff Mult : Type} [Lattice Eff] [OrderBot Eff] [CommSemiring Mult] [DecidableEq Mult]
    [EffSig Eff Mult] : Nat → CTy Eff Mult → Eff → Comp → Comp → Prop := CrelK

abbrev EnvRel {Eff Mult : Type} [Lattice Eff] [OrderBot Eff] [CommSemiring Mult] [DecidableEq Mult]
    [EffSig Eff Mult] (n : Nat) : TyCtx Eff Mult → List Val → List Val → Prop := EnvRelK n


/-! ## 5.3 Adequacy building blocks toward `lr_sound`

`lr_sound : (∀ n, Crel n B e c₁ c₂) → c₁ ⊑ c₂`. Biorthogonal adequacy
(benton-hur-icfp09, pitts-step-indexed): `Crel` (= `CrelK`) co-behaves against EVERY
`KrelS`-related stack pair, so instantiating at a stack pair `(C, C)` known to be
`KrelS`-self-related yields the `⊑`-clause for context `C`.

The CLOSED case (`C = []`) is provable from the relations ALONE — `krelS_nil_succ`
below — and gives `lr_sound_closed` (empty-context / whole-program adequacy). The
ARBITRARY-context case needs `KrelS n B Co e C C` for every well-typed `C`, i.e.
`KrelS`-reflexivity (the "identity extension" lemma `krelS_refl`, Compat §B.6′), which is the
FUNDAMENTAL-THEOREM direction — see the dependency note on `lr_sound` in `Bang/Spec.lean`. -/

/-- A returned value always converges (one machine step: `([], ret v) ↦ done v`). -/
theorem converges_ret (v : Val) : Converges (Comp.ret v) :=
  ⟨1, v, rfl⟩

-- ◊4.5: `crel_zero` (the old universal `Crel 0` base) is REMOVED. Under `Srel 0 := False` it is no
-- longer true for arbitrary `c` (`Krel 0` is inhabited at `F q A` and does not force arbitrary
-- `CoApprox`). It is also no longer NEEDED: the `krel_*` frame-extension lemmas are now stated at general
-- `n` (their stuck halves are vacuous at every `j` via `Srel 0 := False`), so each compat core proves its
-- `n = 0` case by its ordinary main argument — no `cases n`/`crel_zero` base. Single source of truth: a
-- dead lemma carrying a `sorry` is worse than no lemma.

-- (◊inc-5 re-key) The legacy `not_converges_up_nil`/`not_converges_up_splitNone` were UNUSED (doc-only
-- references) and their `Stack.plug`-refocus proof is subsumed by the reshaped `run_plug`; deleted (SSoT).
-- The two CONSUMED config-level stuck lemmas re-key from the deleted `absSplit`/4-arg `perform cap ℓ op v`
-- to the identity-dispatch shape: `splitAtId K cap = none` + `perform (vcap cap ℓ) op v` (ADR-0054/0055).

/-- ◊4.5b CONFIG-LEVEL stuck: the focused config `(g, K, perform (vcap cap ℓ) op v)` with the cap
UNRESOLVED (`splitAtId K cap = none`) is STUCK at every fuel — `Source.step` routes `perform` through
`idDispatch K cap ℓ op v = (splitAtId K cap).bind … = none`, so it never `done`s within ANY step bound.
This is what the metered STUCK halves consume (`CoApproxC_le j (…, perform…) _` is vacuous). Counter `g`
is INERT to stuckness. ◊inc-5 RE-KEY: identity dispatch (`splitAtId K cap`), not the deleted `absSplit`. -/
theorem config_stuck_up_splitNone (g : Nat) (K : Stack) (cap : Nat) (ℓ : Label) (op : OpId) (v : Val)
    (hsplit : Bang.splitAtId K cap = none) :
    ∀ j w, Config.run j (g, K, Comp.perform (Val.vcap cap ℓ) op v) ≠ Result.done w := by
  intro j w
  have hid : Bang.idDispatch K cap ℓ op v = none := by unfold Bang.idDispatch; rw [hsplit]; rfl
  cases j with
  | zero => simp [Config.run]
  | succ k =>
      rw [Config.run_step k (g, K, Comp.perform (Val.vcap cap ℓ) op v) (by intro g' u; simp)]
      have hdisp : Source.step (g, K, Comp.perform (Val.vcap cap ℓ) op v) = none := by
        show (Bang.idDispatch K cap ℓ op v).map (fun (p : EvalCtx × Comp) => (g, p.1, p.2)) = none
        rw [hid]; rfl
      rw [hdisp]; simp

/-- `ConvergesC_le j (g, K, perform (vcap cap ℓ) op v)` is `False` when the cap does not resolve
(`splitAtId K cap = none`) — the metered stuck-half discharge. ◊inc-5 RE-KEY: identity dispatch. -/
theorem not_convergesC_le_up_splitNone {j g : Nat} (K : Stack) (cap : Nat) (ℓ : Label) (op : OpId) (v : Val)
    (hsplit : Bang.splitAtId K cap = none) :
    ¬ ConvergesC_le j (g, K, Comp.perform (Val.vcap cap ℓ) op v) := by
  rintro ⟨w, hw⟩; exact config_stuck_up_splitNone g K cap ℓ op v hsplit j w hw


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
`Converges c₁ → Converges c₂`. The `⊑` restricted to `C = []`. Provable from `Crel` (= `CrelK`) +
`krelS_nil_succ` alone (no fundamental theorem). RETURNER type only (`F q A`): the empty-stack
observation is vacuous at non-returner types (ADR-0038).

◊4.5b ADEQUACY STRIP: the metered `Crel n` (= `CrelK n`) observes only `≤ n` left-steps, so instantiate
at the WITNESSING fuel — `Converges c₁` gives a fuel `f+1` with `run (f+1) ([],c₁) = done`, which IS
`ConvergesC_le (f+1) ([], c₁)`. The answer-typed `CrelK (f+1)` is instantiated at the IDENTITY observation
context (`D = F q A`, `K₁ = K₂ = []`, self-related by `krelS_nil_succ`); its metered `CoApproxC_le (f+1)`
then discharges to the unbounded right `Converges c₂`. The frozen `∀ n` makes the right fuel available. -/
theorem lr_sound_closed {Eff Mult : Type} [Lattice Eff] [OrderBot Eff] [CommSemiring Mult]
    [DecidableEq Mult] [EffSig Eff Mult] {c₁ c₂ : Comp} {e : Eff} {q : Mult} {A : VTy Eff Mult}
    (h : ∀ n, Crel n (CTy.F q A) e c₁ c₂) : Converges c₁ → Converges c₂ := by
  rintro ⟨fuel, v, hfuel⟩
  -- `Source.eval fuel c₁ = Config.run fuel ([], c₁) = done v` ⇒ fuel ≥ 1 (run 0 = oom).
  cases fuel with
  | zero => simp [Source.eval, Config.run] at hfuel
  | succ f =>
      have hC := h (f + 1)
      -- `Crel` is the abbrev for `CrelK`: `∀ D K₁ K₂, KrelS … → CoApproxC_le n (K₁,c₁) (K₂,c₂)`.
      rw [Crel, CrelK] at hC
      -- the metered left premise: ConvergesC_le (f+1) (0, [], c₁), witnessed by hfuel
      -- (`handlerCount [] = 0`, so the CrelK observation at the empty stack is the fresh config).
      have hconv : ConvergesC_le (f + 1) (0, [], c₁) :=
        ⟨v, hfuel⟩
      -- instantiate at the identity observation context: D = F q A, K₁ = K₂ = [] (krelS_nil_succ).
      have hright := hC (CTy.F q A) [] [] (krelS_nil_succ (f + 1) q A e) hconv
      -- hright : ∃ m w, Config.run m ([], c₂) = done w  =  Converges c₂.
      obtain ⟨m, w, hm⟩ := hright
      exact ⟨m, w, hm⟩

end Bang
