/-
  Bang/Operational/Eval.lean — the CK machine (ADR-0023/0055).
  ─────────────────────────────────────────────────────────────────────────
    §2   Result · Source.step · StepStar · NonEscape(') · HasConfig(')
         plug · Config.run · Source.eval · IsDefinedEscape (ADR-0063)
         Config.run_step / run_done_add · isReturn · Trace (axiom)
         lexical-cap regression demos (ADR-0045, build-gated)

  The small-step + fuel-iterated kernel of the operational hub. Imports
  Dispatch (Source.step routes through idDispatch). Theorem STATEMENTS
  (preservation, progress, type_safety, effect_sound, zero_usage_erasable)
  live in Bang/Spec.lean. Split out of Bang/Operational.lean per
  core-overview.md §6; behavior-preserving MOVE.
-/

module

-- The lexical-cap regression `#guard`s (capMigrate*) run `Source.eval` (compiled
-- code) at the META phase, so the modules providing the compiled call-chain —
-- Subst (Comp.substFrom) and Dispatch (idDispatch/dispatchOn) — must be `meta
-- import`ed in addition to the runtime `public import` (the Phase-1a escape for
-- the cross-module #guard codegen wall; same shape as Bang/LWRegress.lean).
meta import Bang.Operational.Subst
meta import Bang.Operational.Dispatch
public import Bang.Operational.Dispatch

namespace Bang

open Bang.EffectRow (Label)

variable {Eff  : Type} [Lattice Eff] [OrderBot Eff]
variable {Mult : Type} [CommSemiring Mult] [DecidableEq Mult]

@[expose] public section

/-! ## 2. Operational semantics (small-step + fuel-iterated) -/

inductive Result (α : Type) where
  | done : α → Result α
  | oom : Result α
  -- ADR-0063: a capability that escapes its handler (forced after the handler pops ⇒ `idDispatch`
  -- finds no frame) is a DEFINED fail-loud terminal, DISTINCT from `.stuck` — the kernel already
  -- produces it (global-fresh minting), we name it. A well-typed `⊥` program never reaches `.stuck`;
  -- it returns, diverges (`.oom`), or hits this defined capability-escape (OCaml-effects `Unhandled`).
  | escapedCap : Result α
  | stuck : Result α

/-! ### CK machine (ADR-0023) — deep handlers over `EvalCtx × Comp`.

The substitution step (pre-ADR-0023, preserved in git) was a *shallow* handler: it caught an
operation only when it sat DIRECTLY under a `handle`. A well-typed body can nest an operation under
`letC`/`app` frames, and a deep handler must reach past them — and, for a zero-shot exception,
DISCARD the intervening continuation. A substitution step cannot express that; a stack can.

State = `Config := EvalCtx × Comp` (focus + frame stack, innermost frame first). Binding stays
substitution-based (this is a CK machine, not a CEK machine), so the focus is always closed.

```
PUSH      ⟨K, letC M N⟩          ↦ ⟨letF N :: K, M⟩          (focus the bound computation)
          ⟨K, app M v⟩           ↦ ⟨appF v :: K, M⟩
          ⟨K, handle h M⟩        ↦ ⟨handleF h :: K, M⟩
          ⟨K, force (vthunk M)⟩  ↦ ⟨K, M⟩
REDUCE    ⟨letF N :: K, ret v⟩   ↦ ⟨K, N[v]⟩                 (let bind)
          ⟨appF v :: K, lam M⟩   ↦ ⟨K, M[v]⟩                 (β)
          ⟨handleF h :: K, ret v⟩↦ ⟨K, ret v⟩                (handler return = identity, Q6 simpl.)
DISPATCH  ⟨K, up ℓ op v⟩         ↦ scan K for the nearest handling frame:
            throws ℓ ⊳ raise:    ↦ ⟨Kₒ, ret v⟩  (ABORT: discard the captured continuation Kᵢ)
            no handler in K:     ↦ stuck
```

`dispatchOn` (below) implements both resumptive kinds — `state` (get/put, ADR-0025) and `transaction`
(newTVar/read/write, ADR-0030): each KEEPS `Kᵢ` and reinstalls the handler frame; only `throws`
discards `Kᵢ`. The search is identical across kinds. -/

/-- One machine transition. `none` = stuck (terminal `⟨g, [], ret v⟩`, or genuinely wrong).
ADR-0055: the leading `g` is the next-fresh capability identity. Only the `handle` arm consumes it
(mints `g`, increments to `g+1`); every other arm threads it unchanged (dispatch reuses an existing
id, never mints). -/
def Source.step : Config → Option Config
  -- PUSH
  | (g, K, .letC M N)          => some (g, .letF N :: K, M)
  | (g, K, .app M v)           => some (g, .appF v :: K, M)
  | (g, K, .handle h M)        =>
      -- ADR-0055: MINT the GLOBAL-FRESH identity `g` (a monotone counter, never reused — reverses
      -- ADR-0054 Fork-ii's depth-minting, which admitted a build-verified cross-extent collision).
      -- Push `handleF g h`, substitute the capability `vcap g h.label` for the handle-bound var 0 (the
      -- SAME `g` both places), and advance the counter to `g+1`. `WellCounted` (every live id `< g`)
      -- makes `g` fresh — `splitAtId K g = none` — so an escaped cap fails loud, never collides.
      some (g + 1, .handleF g h :: K, Comp.subst (.vcap g h.label) M)
  | (g, K, .force (.vthunk M)) => some (g, K, M)
  -- REDUCE
  | (g, .letF N :: K, .ret v)  => some (g, K, Comp.subst v N)
  | (g, .appF v :: K, .lam M)  => some (g, K, Comp.subst v M)
  | (g, .handleF _ _ :: K, .ret v) => some (g, K, .ret v)
  -- ADT eliminators (ADR-0029): scrutinees are values, so these reduce in place.
  | (g, K, .case (.inl v) N₁ _)  => some (g, K, Comp.subst v N₁)   -- sum: left branch
  | (g, K, .case (.inr v) _ N₂)  => some (g, K, Comp.subst v N₂)   -- sum: right branch
  | (g, K, .split (.pair v w) N) => some (g, K, Comp.subst v (Comp.subst (Val.shift w) N))  -- product
  | (g, K, .unfold (.fold v))    => some (g, K, .ret v)            -- μ: fold/unfold erase
  -- DISPATCH (ADR-0054): IDENTITY — the capability `vcap n _` names handler `n`; match it, route by the
  -- resolved handler (`dispatchOn` reinstalls `handleF n` on a resumptive resume). The counter `g` is
  -- threaded UNCHANGED — a resume reuses the matched id, it never mints a fresh one.
  | (g, K, .perform (.vcap n ℓ) op v) => (idDispatch K n ℓ op v).map (fun (K', c') => (g, K', c'))
  -- stuck
  | _                       => none

/-- Reflexive-transitive closure of `Source.step` (snoc form) — the reachability relation `NonEscape`
quantifies over. No prior closure of `Source.step` existed (only the fuel-based `Config.run`), so this
is its single source. shape: scratch/NonEscapeProbe.lean §3. -/
inductive StepStar : Config → Config → Prop where
  | refl : StepStar cfg cfg
  | tail : StepStar cfg cfg' → Source.step cfg' = some cfg'' → StepStar cfg cfg''

/-- Prepend a step — the cons lemma preservation-of-`NonEscape` rides on (forward-closure is
structural, not earned). -/
theorem StepStar.head {cfg cfg₁ cfg' : Config}
    (h0 : Source.step cfg = some cfg₁) (h : StepStar cfg₁ cfg') : StepStar cfg cfg' := by
  induction h with
  | refl => exact StepStar.tail StepStar.refl h0
  | tail _ hstep ih => exact StepStar.tail ih hstep

/-- **The non-escape invariant** (ADR-0054 COLLAPSE, inc 4). Under capability-passing, cap-resolution is
a TYPING property (`c : Cap ℓ` + lexical scope ⟹ the binding `handle` encloses the `perform` ⟹ its
handler is on the stack), so the positional `WellCapped`/`LWConfig` invariant DISSOLVES into the type
system. The SOLE remaining structural obligation is NON-ESCAPE: a capability does not outlive its
handler's dynamic extent — expressed as the forward closure of `FocusResolves` over every reachable
config (Shape B: the unary projection of the typed LR config relation, so non-escape is not a
hand-maintained parallel invariant — preservation is then BY CONSTRUCTION; the one carried obligation is
the initial-config direction `well-typed ([],c) → NonEscape ([],c)`, supplied by the ported LR at inc 5).
See ADR-0054 amendment + scratch/NonEscapeProbe.lean §3. -/
def NonEscape (cfg : Config) : Prop :=
  ∀ cfg', StepStar cfg cfg' → FocusResolves cfg'

/-- **ADR-0063 — the defined-escape-tolerant focus obligation.** A `perform (vcap …)` focus either
RESOLVES (`CapResolves`, the dispatch step fires) OR is a DEFINED capability-escape (`idDispatch = none`,
routed to `.escapedCap`, NOT genuine stuck). Since these are EXHAUSTIVE for a `vcap` perform
(`idDispatch = some ⟹ CapResolves`), `FocusResolves'` holds at EVERY config — the non-escape obligation
DISSOLVES once the escape is a defined terminal (the `liveCapsResolveC_returnEscape` POP-preservation, and
the whole `WScfg` carrier it needed, are no longer required to derive non-escape). -/
def FocusResolves' : Config → Prop
  | (_, K, .perform (.vcap n ℓ) op v) => CapResolves K n ℓ op ∨ idDispatch K n ℓ op v = none
  | _                                 => True

/-- `idDispatch = some` extracts `CapResolves` (the `bind` succeeded ⟹ `splitAtId = some` ∧ `handlesOp`). -/
theorem capResolves_of_idDispatch {K : EvalCtx} {n : Nat} {ℓ : Label} {op : OpId} {v : Val}
    (h : idDispatch K n ℓ op v ≠ none) : CapResolves K n ℓ op := by
  unfold idDispatch at h
  cases hsplit : splitAtId K n with
  | none => rw [hsplit] at h; simp at h
  | some triple =>
    obtain ⟨Kᵢ, hh, Kₒ⟩ := triple
    rw [hsplit] at h
    by_cases hho : handlesOp hh ℓ op = true
    · exact ⟨Kᵢ, hh, Kₒ, hsplit, hho⟩
    · simp only [Option.bind_some, Bool.not_eq_true] at h
      rw [Bool.not_eq_true] at hho; rw [hho] at h; simp at h

/-- `FocusResolves'` is a TAUTOLOGY — every config resolves or is a defined escape. -/
theorem focusResolves'_all (cfg : Config) : FocusResolves' cfg := by
  obtain ⟨g, K, c⟩ := cfg
  match c with
  | .perform (.vcap n ℓ) op v =>
      by_cases hd : idDispatch K n ℓ op v = none
      · exact Or.inr hd
      · exact Or.inl (capResolves_of_idDispatch hd)
  | .ret _ | .letC _ _ | .force _ | .lam _ | .app _ _ | .handle _ _ | .case _ _ _ | .split _ _
  | .unfold _ | .oom | .wrong _ | .perform (.vunit) _ _ | .perform (.vint _) _ _
  | .perform (.vvar _) _ _ | .perform (.vthunk _) _ _ | .perform (.inl _) _ _ | .perform (.inr _) _ _
  | .perform (.pair _ _) _ _ | .perform (.fold _) _ _ => trivial

/-- **ADR-0063 — the defined-escape-tolerant non-escape invariant.** Derivable from NOTHING (it's the
forward closure of the tautology `FocusResolves'`): every reachable config resolves or is a defined
capability-escape. This is what the inc-5 diagonal `HasConfigTy ⟹ NonEscape'` now reduces to. -/
def NonEscape' (cfg : Config) : Prop :=
  ∀ cfg', StepStar cfg cfg' → FocusResolves' cfg'

theorem nonEscape'_all (cfg : Config) : NonEscape' cfg := fun cfg' _ => focusResolves'_all cfg'

/-- **Configuration typing** (ADR-0054 COLLAPSE): the typing CORE (`HasConfigTy`) PLUS the `NonEscape`
invariant (replacing the positional `LWConfig`, which is now subsumed by typing — the capability's `Cap ℓ`
type carries the resolution). Folding it in HERE keeps the frozen `preservation`/`progress` statements —
stated over `HasConfig` — BYTE-IDENTICAL. -/
def HasConfig [EffSig Eff Mult] (cfg : Config) (eo : Eff) (Co : CTy Eff Mult) : Prop :=
  HasConfigTy cfg eo Co ∧ NonEscape cfg

/-- **ADR-0063 — the reclassified configuration typing.** Identical to `HasConfig` but pairing the typing
CORE with the defined-escape-tolerant `NonEscape'` instead of `NonEscape`. Since `NonEscape'` is a
TAUTOLOGY (`nonEscape'_all`), this is operationally just `HasConfigTy` — the structural non-escape burden
is gone, absorbed into the `.escapedCap` defined terminal. `progress'`/`type_safety'` are stated over it;
inc-6 swaps the frozen `Spec.lean` premises onto this. The OLD `HasConfig` stays parked (the binary-LR
route still references its `NonEscape`). -/
def HasConfig' [EffSig Eff Mult] (cfg : Config) (eo : Eff) (Co : CTy Eff Mult) : Prop :=
  HasConfigTy cfg eo Co ∧ NonEscape' cfg

/-- Fill a single frame's hole with a focus — the one-step node a `plug` builds for a frame, and
the redex a PUSH step undoes (`step (K, fr.wrapStep c) = (fr :: K, c)`). -/
def Frame.wrapStep : Frame → Comp → Comp
  | .letF N,    c => .letC c N
  | .appF v,    c => .app c v
  | .handleF _ h, c => .handle h c

/-- Plug a focus back into its evaluation context (the inverse of decomposition). -/
def plug : EvalCtx → Comp → Comp
  | [], c            => c
  | .letF N :: K, c  => plug K (.letC c N)
  | .appF v :: K, c  => plug K (.app c v)
  | .handleF _ h :: K, c => plug K (.handle h c)

/-- `plug` peels its head frame via `wrapStep` (the structural identity `run_plug` inducts on). -/
theorem plug_cons (fr : Frame) (K : EvalCtx) (c : Comp) :
    plug (fr :: K) c = plug K (fr.wrapStep c) := by cases fr <;> rfl

/-- Run a config to a returned value. `⟨g, [], ret v⟩` = done; `step = none` on a non-terminal classifies:
a focus `perform (vcap n ℓ) op v` whose `idDispatch` finds NO frame is the DEFINED capability-escape
(ADR-0063) ⟹ `.escapedCap`; every other `step = none` is genuine `.stuck`. (For that focus,
`Source.step = (idDispatch …).map …`, so `step = none ⟺ idDispatch = none ⟺ the cap escaped.) -/
def Config.run : Nat → Config → Result Val
  | 0, _              => .oom
  | _ + 1, (_, [], .ret v) => .done v
  | n + 1, cfg        =>
      match Source.step cfg with
      | some cfg' => Config.run n cfg'
      | none      =>
          match cfg.2.2 with
          | .perform (.vcap _ _) _ _ => .escapedCap
          | _                        => .stuck

/-- Source.eval: load the closed program into `⟨0, [], c⟩` (a FRESH machine: counter at 0, empty
stack) and run. Signature unchanged (ADR-0023 D3); ADR-0055 only seeds the fresh-id counter at 0. -/
def Source.eval (fuel : Nat) (c : Comp) : Result Val := Config.run fuel (0, [], c)

/-- **ADR-0063 — the defined-escape configuration shape.** A config whose focus is a `perform (vcap n ℓ)`
op whose `idDispatch` finds no handling frame (`= none`). Exactly the `Source.step = none` shape that
`Config.run` routes to `.escapedCap` (a DEFINED terminal, not genuine stuck). This is the third outcome
of `progress'` — the relocation of the old (false) `returnEscape` non-escape obligation into a defined
result. -/
def IsDefinedEscape : Config → Prop
  | (_, K, .perform (.vcap n ℓ) op v) => idDispatch K n ℓ op v = none
  | _                                 => False

/-- A defined-escape config has no `Source.step` (its `idDispatch` is `none`, and `step` on a
`perform (vcap …)` focus is exactly `(idDispatch …).map …`). -/
private theorem step_none_of_definedEscape {cfg : Config} (h : IsDefinedEscape cfg) :
    Source.step cfg = none := by
  obtain ⟨g, K, M⟩ := cfg
  match M, h with
  | .perform (.vcap n ℓ) op v, hd =>
      show (idDispatch K n ℓ op v).map (fun (Kc : EvalCtx × Comp) => (g, Kc.1, Kc.2)) = none
      rw [show idDispatch K n ℓ op v = none from hd]; rfl

/-- A defined-escape config runs (at any positive fuel) to the `.escapedCap` defined terminal — NOT
`.stuck`. The `Config.run` `none` arm classifies a `perform (vcap …)` focus as `.escapedCap`. -/
theorem run_escapedCap_of_definedEscape {n : Nat} {cfg : Config} (h : IsDefinedEscape cfg) :
    Config.run (n + 1) cfg = Result.escapedCap := by
  obtain ⟨g, K, M⟩ := cfg
  match M, h with
  | .perform (.vcap nn ℓ) op v, hd =>
      have hstep : Source.step (g, K, Comp.perform (Val.vcap nn ℓ) op v) = none :=
        step_none_of_definedEscape (cfg := (g, K, Comp.perform (Val.vcap nn ℓ) op v)) hd
      show Config.run (n + 1) (g, K, Comp.perform (Val.vcap nn ℓ) op v) = Result.escapedCap
      simp only [Config.run, hstep]

/-- **The non-escape preservation obligation (ADR-0054).** `NonEscape` is preserved by every
`Source.step` transition. With `NonEscape` now the forward closure of `FocusResolves` over reachable
configs (inc 4), preservation is BY CONSTRUCTION: any config reachable from the successor `cfg'` is
reachable from `cfg` by prepending the step (`StepStar.head`), so `cfg`'s closure covers it. No typing,
no LR — the type-directed escape discrimination lives in `FocusResolves`, the cap-resolution obligation.
The one remaining LR-carried direction is the INITIAL config (`well-typed ([],c) → NonEscape ([],c)`),
not this preservation step. See ADR-0054 amendment + scratch/NonEscapeProbe.lean §3. -/
theorem preservation_returnEscape_TODO
    {cfg cfg' : Config} (hne : NonEscape cfg) (hstep : Source.step cfg = some cfg') :
    NonEscape cfg' :=
  fun cfg'' hreach => hne cfg'' (StepStar.head hstep hreach)

/-! ### Lexical-cap regression demos (ADR-0045 amendment) — REAL artifacts, build-gated.

These `#guard`s are the migration-is-correct evidence (ADR-0054). The `get`-thunk's capability is a
`vvar` bound by its target `handle`; forced under unrelated `throws` handlers, identity dispatch reaches
the right handler by MATCH (no re-count → migration-invariant). `handle` BINDS a capability at index 0,
so de-Bruijn indices count it. Labels are `Nat` (`EffectRow.Label`). -/

/-- `Source.eval` yields exactly `done (vint n)` (Bool; `Result`/`Val` derive only `Inhabited`). -/
private def yieldsInt (fuel : Nat) (c : Comp) (n : Int) : Bool :=
  match Source.eval fuel c with | .done (.vint m) => m == n | _ => false

/-- 1-deep migration: a `{get}` thunk targeting the OUTER state (its cap = `vvar 0` in the state's body),
forced under one fresh `throws`; identity dispatch reaches the outer state = 5. -/
private def capMigrate1 : Comp :=
  .handle (.state 1 (.vint 5))
    (.letC (.ret (.vthunk (.perform (.vvar 0) "get" .vunit)))
      (.handle (.throws 2) (.force (.vvar 1))))
#guard yieldsInt 200 capMigrate1 5

/-- 2-deep migration: the thunk crosses TWO fresh `throws` handlers; identity dispatch still reaches the
outer state = 9 (a match never shifts, however deep the migration). -/
private def capMigrate2 : Comp :=
  .handle (.state 1 (.vint 9))
    (.letC (.ret (.vthunk (.perform (.vvar 0) "get" .vunit)))
      (.handle (.throws 2) (.handle (.throws 3) (.force (.vvar 2)))))
#guard yieldsInt 300 capMigrate2 9

/-- ★ THE INSERT-BELOW-TARGET WITNESS (the program that broke ABSOLUTE caps, ADR-0053): a thunk that
handles its OWN `state` and reads it, forced under an unrelated outer `throws`. Identity dispatch reaches
the thunk's OWN state = 7 (absolute caps mis-resolved this to the throws). The fix, in the kernel. -/
private def capMigrateInternal : Comp :=
  .app (.lam (.handle (.throws 2) (.force (.vvar 1))))
    (.vthunk (.handle (.state 1 (.vint 7)) (.perform (.vvar 0) "get" .vunit)))
#guard yieldsInt 200 capMigrateInternal 7

/-- `Config.run` unfolds one step on a NON-returning config: when `cfg` is not `(g, [], ret v)` the
machine takes a `Source.step`. Bridges the equation compiler's overlapping `(_, [], ret v)` /
catch-all arms so callers can reason about a single transition. ADR-0055: the returned config now
carries the fresh-id counter `g`, so the non-returning hypothesis quantifies over it. -/
theorem Config.run_step (n : Nat) (cfg : Config)
    (hne : ∀ g v, cfg ≠ (g, [], Comp.ret v)) :
    Config.run (n + 1) cfg =
      (match Source.step cfg with
       | some cfg' => Config.run n cfg'
       | none => match cfg.2.2 with | .perform (.vcap _ _) _ _ => .escapedCap | _ => .stuck) := by
  obtain ⟨g, K, c⟩ := cfg
  match K, c with
  | [], .ret v => exact absurd rfl (hne g v)
  | [], .letC _ _ | [], .app _ _ | [], .handle _ _ | [], .force _ | [], .perform _ _ _
  | [], .lam _ | [], .case _ _ _ | [], .split _ _ | [], .unfold _ | [], .oom | [], .wrong _
  | _ :: _, _ => rfl

/-- Fuel monotonicity: a config that runs to `done w` keeps running to `done w` with MORE fuel.
Standard "more fuel never hurts a terminating run" — induct on `n`, threading the single transition
through `Config.run_step`. -/
theorem Config.run_done_add (k : Nat) :
    ∀ (n : Nat) (cfg : Config) (w : Val),
      Config.run n cfg = Result.done w → Config.run (n + k) cfg = Result.done w := by
  intro n
  induction n with
  | zero => intro cfg w h; rw [show Config.run 0 cfg = Result.oom from rfl] at h; exact absurd h (by simp)
  | succ m ih =>
    intro cfg w h
    by_cases hret : ∃ g v, cfg = (g, [], Comp.ret v)
    · obtain ⟨g, v, rfl⟩ := hret
      -- (g, [], ret v): both runs hit the `done` arm; (m+1)+k = (m+k)+1 still returns v.
      have hwv : Result.done w = Result.done v := by
        rw [← h]; rfl
      rw [show m + 1 + k = (m + k) + 1 by omega]
      show Result.done v = Result.done w
      exact hwv.symm
    · push_neg at hret
      rw [Config.run_step m cfg hret] at h
      rw [show m + 1 + k = (m + k) + 1 by omega, Config.run_step (m + k) cfg hret]
      cases hstep : Source.step cfg with
      | none => rw [hstep] at h; exact h
      | some cfg' =>
          rw [hstep] at h
          show Config.run (m + k) cfg' = Result.done w
          exact ih cfg' w h

-- Trace / evalTrace: still axiom; need concrete Eff to express
-- "label in row" (see `docs/notes/OPEN_QUESTIONS.md` Q1).
axiom Trace            : Type
axiom Source.evalTrace : Nat → Comp → Result (Val × Trace)
axiom traceWithin      {Eff : Type} : Trace → Eff → Prop

/-- isReturn: a Comp is "returned" iff it's `ret v` for some v. -/
def isReturn : Comp → Prop
  | .ret _ => True
  | _      => False

-- `NotEvaluated` (the coeffect-erasure notion: de Bruijn index `i`'s binder is never *evaluated*)
-- is DEFINED in `Bang/LR.lean` (§5.0b), where the observational equivalence `≈` it is phrased over
-- lives. A 0-graded var is still SUBSTITUTED syntactically (and type-checks — QTT permits 0-graded
-- occurrences); only its *evaluation* is absent, so the faithful notion is semantic, not structural.

end -- public section

end Bang
