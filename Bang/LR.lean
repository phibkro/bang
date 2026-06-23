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
      ∃ c₁ c₂, v₁ = Val.vthunk c₁ ∧ v₂ = Val.vthunk c₂ ∧ Crel n B φ c₁ c₂
  | n,     .sum A B, v₁, v₂ =>
      (∃ w₁ w₂, v₁ = Val.inl w₁ ∧ v₂ = Val.inl w₂ ∧ Vrel n A w₁ w₂) ∨
      (∃ w₁ w₂, v₁ = Val.inr w₁ ∧ v₂ = Val.inr w₂ ∧ Vrel n B w₁ w₂)
  | n,     .prod A B, v₁, v₂ =>
      ∃ a₁ a₂ b₁ b₂, v₁ = Val.pair a₁ b₁ ∧ v₂ = Val.pair a₂ b₂ ∧
        Vrel n A a₁ a₂ ∧ Vrel n B b₁ b₂
  | 0,     .mu _,    _,  _  => True
  | n+1,   .mu A,    v₁, v₂ =>
      ∃ w₁ w₂, v₁ = Val.fold w₁ ∧ v₂ = Val.fold w₂ ∧ Vrel n (VTy.unrollMu A) w₁ w₂
  | _,     .tvar _,  _,  _  => False
termination_by n A _ _ => (n, sizeOf A, 3)

/-- Computation relation `E⟦C/ε⟧η` (Biernacki Fig 7), the BIORTHOGONAL closure: two
computations relate iff they co-behave (`CoApprox = Obs`) under every `Krel`-related pair
of stacks. This is the relation `lr_sound`/`lr_fundamental` are stated over. -/
def Crel {Eff Mult : Type} [Lattice Eff] [OrderBot Eff] [CommSemiring Mult] [DecidableEq Mult]
    [EffSig Eff Mult] : Nat → CTy Eff Mult → Eff → Comp → Comp → Prop
  | n, C, ε, c₁, c₂ =>
      ∀ K₁ K₂ : Stack, Krel n C ε K₁ K₂ →
        CoApprox (Stack.plug K₁ c₁) (Stack.plug K₂ c₂)
termination_by n C _ _ _ => (n, sizeOf C, 2)

/-- Continuation/stack relation `K⟦C/ε⟧η` (Biernacki Fig 7). A computation can finish two
ways — RETURN a value or RAISE an effect — so two stacks relate iff they co-behave when
plugged with EITHER (a) `Vrel`-related returned values (at `C`'s returner type `F q A`), or
(b) `Srel`-related control-stuck computations. The two halves of the biorthogonal "observe
through related values OR related stuck terms" clause. -/
def Krel {Eff Mult : Type} [Lattice Eff] [OrderBot Eff] [CommSemiring Mult] [DecidableEq Mult]
    [EffSig Eff Mult] : Nat → CTy Eff Mult → Eff → Stack → Stack → Prop
  | n, C, ε, K₁, K₂ =>
      (∀ q A, C = CTy.F q A → ∀ v₁ v₂, Val.Closed v₁ → Val.Closed v₂ → Vrel n A v₁ v₂ →
        CoApprox (Stack.plug K₁ (Comp.ret v₁)) (Stack.plug K₂ (Comp.ret v₂)))
      ∧ (∀ c₁ c₂, Srel n C ε K₁ K₂ c₁ c₂ →
        CoApprox (Stack.plug K₁ c₁) (Stack.plug K₂ c₂))
termination_by n C _ _ _ => (n, sizeOf C, 1)

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
  | 0,   _, _, _,  _,  _,  _  => True
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
  | zero => simp only [Srel]
  | succ m =>
      rw [Srel] at hS ⊢
      obtain ⟨ℓ, op, v₁, v₂, Aarg, Ares, hc₁, hc₂, hℓ, hArg, hRes, hv, hsp₁, hsp₂, hout⟩ := hS
      refine ⟨ℓ, op, v₁, v₂, Aarg, Ares, hc₁, hc₂, le_trans hℓ hεε', hArg, hRes, hv, hsp₁, hsp₂, ?_⟩
      intro u₁ u₂ hcu₁ hcu₂ hu
      exact Crel_eff_mono m C ε ε' _ _ hεε' (hout u₁ u₂ hcu₁ hcu₂ hu)

theorem Krel_eff_anti {Eff Mult : Type} [Lattice Eff] [OrderBot Eff] [CommSemiring Mult]
    [DecidableEq Mult] [EffSig Eff Mult]
    (n : Nat) (C : CTy Eff Mult) (ε ε' : Eff) (K₁ K₂ : Stack)
    (hεε' : ε ≤ ε') (hK : Krel n C ε' K₁ K₂) : Krel n C ε K₁ K₂ := by
  rw [Krel] at hK ⊢
  refine ⟨hK.1, ?_⟩
  intro c₁ c₂ hS
  exact hK.2 c₁ c₂ (Srel_eff_mono n C ε ε' K₁ K₂ c₁ c₂ hεε' hS)

theorem Crel_eff_mono {Eff Mult : Type} [Lattice Eff] [OrderBot Eff] [CommSemiring Mult]
    [DecidableEq Mult] [EffSig Eff Mult]
    (n : Nat) (C : CTy Eff Mult) (ε ε' : Eff) (c₁ c₂ : Comp)
    (hεε' : ε ≤ ε') (hC : Crel n C ε c₁ c₂) : Crel n C ε' c₁ c₂ := by
  rw [Crel] at hC ⊢
  intro K₁ K₂ hK
  exact hC K₁ K₂ (Krel_eff_anti n C ε ε' K₁ K₂ hεε' hK)
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
theorem not_converges_up_splitNone {Eff Mult : Type} [Lattice Eff] [OrderBot Eff] [CommSemiring Mult]
    [DecidableEq Mult] [EffSig Eff Mult] (K : Stack) (ℓ : Label) (op : OpId) (v : Val)
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

/-- The empty stack is `Krel`-self-related at every SUCCESSOR index/type/row: the RETURN half
holds because `ret v` always converges (so `CoApprox` is `True → True`), and the STUCK half
holds because an `Srel (n+1)`-pair under `[]` is an unhandled `up`, which never converges (so
`CoApprox` is `False → _`). This is the closed-program observation context.

The `n+1` is necessary: at index 0, `Srel 0 = True` carries no operation shape, so the stuck
half would demand `CoApprox c₁ c₂` for ARBITRARY `c₁ c₂` — false. (This is the standard
step-indexed convention that a relation-as-PREMISE is only informative at successor indices;
the `∀ n` hypothesis of `lr_sound` lets the proof pick `n+1`.) -/
theorem krel_nil_succ {Eff Mult : Type} [Lattice Eff] [OrderBot Eff] [CommSemiring Mult]
    [DecidableEq Mult] [EffSig Eff Mult] (n : Nat) (B : CTy Eff Mult) (e : Eff) :
    Krel (n + 1) B e ([] : Stack) ([] : Stack) := by
  unfold Krel
  refine ⟨?_, ?_⟩
  · -- return half: plug [] (ret vᵢ) = ret vᵢ, which always converges.
    intro q A _ v₁ v₂ _ _ _ _
    exact converges_ret v₂
  · -- stuck half: an Srel (n+1)-pair under [] is an unhandled `up`, which never converges.
    intro c₁ c₂ hS hconv
    unfold Srel at hS
    obtain ⟨ℓ, op, v₁, v₂, Aarg, Ares, hc₁, _, _, _, _, _, _, _, _⟩ := hS
    rw [Stack.plug, Bang.plug, hc₁] at hconv
    exact absurd hconv (not_converges_up_nil ℓ op v₁)

/-- WHOLE-PROGRAM adequacy: `Crel` implies the closed (empty-context) observation
`Converges c₁ → Converges c₂`. The `⊑` restricted to `C = []`. Provable from `Crel` +
`krel_nil_succ` alone (no fundamental theorem). -/
theorem lr_sound_closed {Eff Mult : Type} [Lattice Eff] [OrderBot Eff] [CommSemiring Mult]
    [DecidableEq Mult] [EffSig Eff Mult] {c₁ c₂ : Comp} {e : Eff} {B : CTy Eff Mult}
    (h : ∀ n, Crel n B e c₁ c₂) : Converges c₁ → Converges c₂ := by
  have hC := h 1
  unfold Crel at hC
  have := hC [] [] (krel_nil_succ 0 B e)
  simpa [Stack.plug, Bang.plug] using this

end Bang
