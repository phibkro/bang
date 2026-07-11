module

-- The lexical-cap regression `#guard`s (capMigrate*) run `Source.eval` (compiled
-- code) at the META phase, so the modules providing the compiled call-chain —
-- Subst (Comp.substFrom) and Dispatch (idDispatch/dispatchOn) — must be `meta
-- import`ed in addition to the runtime `public import` (the Phase-1a escape for
-- the cross-module #guard codegen wall; same shape as Bang/LWRegress.lean).
meta import Bang.Core.Semantics.Subst
meta import Bang.Core.Semantics.Dispatch
public import Bang.Core.Semantics.Dispatch

/-!
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

namespace Bang

open Bang.EffectRow (Label)

variable {Eff  : Type} [Lattice Eff] [OrderBot Eff]
variable {Mult : Type} [CommSemiring Mult] [DecidableEq Mult]

@[expose] public section

/-! ## 2. Operational semantics (small-step + fuel-iterated) -/

/-- The outcome of a fuel-bounded evaluation: a completed value (`done`), fuel
exhaustion (`oom`), a capability escaping its handler (`escapedCap`, ADR-0063),
or a stuck configuration (`stuck`, never reached by a well-typed program). -/
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
  | (g, K, .binop op (.vint a) (.vint b)) => some (g, K, .ret (op.eval a b))  -- δ-rule (ADR-0065)
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
  | .unfold _ | .binop _ _ _ | .oom | .wrong _ | .perform (.vunit) _ _ | .perform (.vint _) _ _
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
theorem preservation_returnEscape
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

/-! ### ADR-0085 #44 STAGE 2 (ADR-0087 finite rep) — user-defined-effect (`Handler.custom`) dispatch +
one-shot resume demos.

KERNEL-LEVEL `#guard`s (the surface is stage 7): a `Handler.custom` value is hand-built with a finite
CLAUSE LIST, installed with `handle`, and run via `Source.eval` — the UNTYPED kernel interpreter needs no
typing rule (custom stays untyped until stage 3). These are the stage-2 gate: they show the general
handler is LIVE at the kernel over the finite rep. `Source.eval` is `Config.run` over `Source.step`,
INDEPENDENT of the route-A cap metatheory — so the DISPATCH + RESUME semantics are demonstrable here
regardless of the metatheory. -/

/-- The `{Reader}`-style clause list: `read x` resumes with `x + p` (arg@0 + param@1). A one-shot
tail-resumptive clause carrying a config param `p` — reader / `{Net}`-config / logging, the v1 sweet spot
(read-only param). Other ops are unserviced (`find?` returns `none`). -/
private def readerClauses : List (OpId × Comp) :=
  [("read", .binop .add (.vvar 0) (.vvar 1))]   -- resume with arg@0 + param@1

/-- **(a) DISPATCH + ONE-SHOT RESUME.** A custom handler (label 1, param `100`) services `read 5` by
running the clause `arg + param = 5 + 100 = 105`, RESUMING the `letC` continuation with `105`; the
continuation `105 + 1 = 106` then runs AFTER the clause (the one-shot resume — the continuation IS
reached). Mirrors `state`'s `get`, with USER clause logic in place of the hardcoded read. -/
private def customResume : Comp :=
  .handle (.custom 1 (.vint 100) readerClauses)
    (.letC (.perform (.vvar 0) "read" (.vint 5))     -- custom cap = var0; read 5 ⤳ resume 105
      (.binop .add (.vvar 0) (.vint 1)))             -- continuation runs on 105 ⤳ 106
#guard yieldsInt 200 customResume 106

/-- **(b) ZERO-SHOT ABORT, coexisting with `throws` (ADR-0085 "throws generalized").** A v1 custom clause
resumes at tail and (being closed) cannot itself discard the continuation, so abort is the `throws`
built-in COEXISTING: a custom handler frame (label 1) sits BETWEEN the `raise` and its `throws` handler
(label 2). The `raise 42` aborts PAST the custom frame to the throws handler — the read continuation
never runs — yielding `42`. Shows real custom dispatch does NOT break the zero-shot abort of a coexisting
built-in (the coexist payoff). -/
private def customAbortCoexist : Comp :=
  .handle (.throws 2)                                          -- throws cap = var0
    (.handle (.custom 1 (.vint 100) readerClauses)             -- custom cap = var0, throws cap ⤳ var1
      (.letC (.perform (.vvar 1) "raise" (.vint 42))           -- raise 42 ⤳ ABORT past the custom frame
        (.perform (.vvar 0) "read" (.vint 5))))                -- never reached (aborted)
#guard yieldsInt 200 customAbortCoexist 42

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
  | [], .lam _ | [], .case _ _ _ | [], .split _ _ | [], .unfold _ | [], .binop _ _ _ | [], .oom | [], .wrong _
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

/-! ### Effect trace (Q14 re-foundation) — concrete images of the three parked axioms.

The three symbols `Trace`/`Source.evalTrace`/`traceWithin` were bare `axiom`s parked on Q1 (a
concrete `Eff`). Q1 is now RESOLVED (`[Lattice Eff] [OrderBot Eff]`, ADR-0018), so they become
concrete DEFINITIONS — the obvious images of the machine.

The DESIGN choice is the trace SEMANTICS (Q14): a program's dispatched labels are NOT all `≤ e`,
because a label handled by an in-program `handle` frame is DISCHARGED from the residual row
`e` (the `handleThrows`/`handleState` typing rules remove `ℓ` from `φ`). So `trace ⊆ e` (naive) is
FALSE (`handle (throws ℓ)(raise ℓ)` at `e = ⊥`), and "only-escaping labels ⊆ e" is VACUOUS (an
escaping op runs to `escapedCap`, not `done`, so its trace is empty).

We take Q14 option (1) — the INFORMATIVE per-dispatch bound — realized WITHOUT preservation-threading
via the **runtime bound**: the live effect row at a config is `e ⊔ ⨆{labelEff(h.label) | handleF h ∈ K}`
— the top-level row JOINED with the labels of the currently-installed handler frames. Handler frames
carry their labels at runtime (dispatch needs them: `handleF n h`, `h.label`), so this bound is
COMPUTED config-side by the passenger — no typing fact, no preservation. Entering a `handle` pushes
its label into the bound (structurally: `handleF` is on `K`), popping removes it. At each DISPATCH we
record `(ℓ, liveBound K e)`; `traceWithin` checks each `labelEff ℓ ≤` its recorded bound. The
resulting theorem: "every dispatched op was performed under a LIVE handler for its label, or its
label is in the top-level row `e`" — provable by induction on the machine (a dispatched `ℓ` resolves
to a `handleF` frame on `K` whose label is `ℓ`, so `labelEff ℓ ≤ liveBound K e`). -/

/-- The effect trace: the labels dispatched during a run, each paired with the RUNTIME live bound
`e ⊔ ⨆ live-handler-labels` in force at the point it was performed. -/
abbrev Trace (Eff : Type) := List (Label × Eff)

/-- The runtime live-effect bound at a config: the top-level row `e` joined with the singleton rows
of every `handleF` frame's label on the stack `K`. Computed purely config-side (handler frames carry
their labels — dispatch reads them), so no typing fact is needed. -/
def liveBound {Mult : Type} [CommSemiring Mult] [DecidableEq Mult] [EffSig Eff Mult] :
    EvalCtx → Eff → Eff
  | [], e                    => e
  | .handleF _ h :: K, e     =>
      EffSig.labelEff (Eff := Eff) (Mult := Mult) h.label ⊔ liveBound (Mult := Mult) K e
  | .letF _ :: K, e          => liveBound (Mult := Mult) K e
  | .appF _ :: K, e          => liveBound (Mult := Mult) K e

/-- Instrumented `Config.run`: identical control flow to `Config.run`, but accumulates the dispatched
`(label, liveBound)` pairs. The VALUE component agrees with `Config.run` byte-for-byte (same step,
same terminals) — the accumulator is a passenger. The bound is recomputed from the stack `K` at each
DISPATCH (runtime-present handler labels), so `e` is the fixed top-level row (never re-threaded). -/
def Config.runTrace {Mult : Type} [CommSemiring Mult] [DecidableEq Mult] [EffSig Eff Mult] :
    Nat → Config → Eff → Trace Eff → Result (Val × Trace Eff)
  | 0, _, _, _                    => .oom
  | _ + 1, (_, [], .ret v), _, t  => .done (v, t)
  | n + 1, cfg, e, t              =>
      match cfg.2.2 with
      -- DISPATCH: record `(ℓ, liveBound K e)` before stepping. Other arms thread `t` unchanged.
      | .perform (.vcap _ ℓ) _ _ =>
          match Source.step cfg with
          | some cfg' => Config.runTrace (Mult := Mult) n cfg' e (t ++ [(ℓ, liveBound (Mult := Mult) cfg.2.1 e)])
          | none      => .escapedCap
      | _ =>
          match Source.step cfg with
          | some cfg' => Config.runTrace (Mult := Mult) n cfg' e t
          | none      =>
              match cfg.2.2 with
              | .perform (.vcap _ _) _ _ => .escapedCap
              | _                        => .stuck

/-- Fuel-bounded evaluation returning both the value and the effect `Trace`. Load into a fresh
machine (`⟨0, [], c⟩`), run under the whole-program residual `e`, empty trace. -/
def Source.evalTrace {Mult : Type} [CommSemiring Mult] [DecidableEq Mult] [EffSig Eff Mult]
    (fuel : Nat) (c : Comp) (e : Eff) : Result (Val × Trace Eff) :=
  Config.runTrace (Mult := Mult) fuel (0, [], c) e []

/-- The trace stays within its recorded bounds (INFORMATIVE, Q14 option 1): every dispatched label
is `≤` the runtime live bound in force when it was performed. Internally-handled labels are checked
against their handler's live bound (which contains their label), NOT the discharged top-level `e`. -/
def traceWithin {Mult : Type} [CommSemiring Mult] [DecidableEq Mult] [EffSig Eff Mult]
    (t : Trace Eff) : Prop :=
  ∀ p ∈ t, EffSig.labelEff (Eff := Eff) (Mult := Mult) p.1 ≤ p.2

/-! ### Effect-soundness discharge (Q14, ADR-0105) — `traceWithin` holds for every `evalTrace` run.

The runtime-bound design makes the discharge a MACHINE induction, no preservation / no LR: a dispatched
label resolves to a `handleF` frame on the stack whose label IS the label (`handlesOp_label`), and a
frame's label-row is `≤ liveBound` (`liveBound_splitAtId`). So each recorded `(ℓ, liveBound K e)` is
`traceWithin`-good, and the accumulator invariant threads through `Config.runTrace.induct`. -/

/-- `traceWithin` of the empty trace is vacuous. -/
theorem traceWithin_nil {Mult : Type} [CommSemiring Mult] [DecidableEq Mult] [EffSig Eff Mult] :
    traceWithin (Eff := Eff) (Mult := Mult) [] := by intro p hp; simp at hp

/-- The matched handler's label-row is `≤ liveBound K e`: a `splitAtId` frame contributes its label to
the `liveBound` fold. -/
theorem liveBound_splitAtId {Mult : Type} [CommSemiring Mult] [DecidableEq Mult] [EffSig Eff Mult]
    {n : Nat} {e : Eff} :
    ∀ {K Kᵢ Kₒ : EvalCtx} {h : Handler},
    splitAtId K n = some (Kᵢ, h, Kₒ) →
    EffSig.labelEff (Eff := Eff) (Mult := Mult) h.label ≤ liveBound (Mult := Mult) K e := by
  intro K
  induction K with
  | nil => intro Kᵢ Kₒ h hsp; simp [splitAtId] at hsp
  | cons fr K ih =>
    intro Kᵢ Kₒ h hsp
    cases fr with
    | handleF m hh =>
      simp only [splitAtId] at hsp
      by_cases hm : m = n
      · simp only [hm, if_pos] at hsp
        obtain ⟨-, rfl, -⟩ := Prod.mk.injEq .. ▸ (Option.some.injEq _ _ ▸ hsp)
        simp only [liveBound]; exact le_sup_left
      · simp only [if_neg hm, Option.map_eq_some_iff] at hsp
        obtain ⟨⟨Kᵢ', hh', Kₒ'⟩, hsp', heq⟩ := hsp
        obtain ⟨-, rfl, -⟩ := Prod.mk.injEq .. ▸ heq
        simp only [liveBound]; exact le_sup_of_le_right (ih hsp')
    | letF N => simp only [splitAtId, Option.map_eq_some_iff] at hsp
                obtain ⟨⟨Kᵢ', hh', Kₒ'⟩, hsp', heq⟩ := hsp
                obtain ⟨-, rfl, -⟩ := Prod.mk.injEq .. ▸ heq
                simp only [liveBound]; exact ih hsp'
    | appF v => simp only [splitAtId, Option.map_eq_some_iff] at hsp
                obtain ⟨⟨Kᵢ', hh', Kₒ'⟩, hsp', heq⟩ := hsp
                obtain ⟨-, rfl, -⟩ := Prod.mk.injEq .. ▸ heq
                simp only [liveBound]; exact ih hsp'

/-- At a RECORDING dispatch (the `perform (vcap n ℓ)` step succeeds), `labelEff ℓ ≤ liveBound K e` —
the dispatched label's row is within the runtime bound. Combines `capResolves_of_idDispatch` (step
success ⟹ a matching frame), `handlesOp_label` (its label is `ℓ`), and `liveBound_splitAtId`. -/
theorem labelEff_le_liveBound_of_step {Mult : Type} [CommSemiring Mult] [DecidableEq Mult]
    [EffSig Eff Mult] {g n : Nat} {ℓ : Label} {op : OpId} {vv : Val}
    {K : EvalCtx} {cfg' : Config} {e : Eff}
    (hstep : Source.step (g, K, Comp.perform (Val.vcap n ℓ) op vv) = some cfg') :
    EffSig.labelEff (Eff := Eff) (Mult := Mult) ℓ ≤ liveBound (Mult := Mult) K e := by
  simp only [Source.step] at hstep
  have hid : idDispatch K n ℓ op vv ≠ none := by intro h; rw [h] at hstep; simp at hstep
  obtain ⟨Kᵢ, h, Kₒ, hsplit, hho⟩ := capResolves_of_idDispatch hid
  have hlbl : h.label = ℓ := handlesOp_label hho
  have hle := liveBound_splitAtId (Eff := Eff) (Mult := Mult) (e := e) hsplit
  rw [hlbl] at hle; exact hle

/-- `traceWithin` is preserved by appending a `traceWithin`-good entry. -/
theorem traceWithin_append {Mult : Type} [CommSemiring Mult] [DecidableEq Mult] [EffSig Eff Mult]
    {t : Trace Eff} {p : Label × Eff}
    (ht : traceWithin (Eff := Eff) (Mult := Mult) t)
    (hp : EffSig.labelEff (Eff := Eff) (Mult := Mult) p.1 ≤ p.2) :
    traceWithin (Eff := Eff) (Mult := Mult) (t ++ [p]) := by
  intro q hq; rw [List.mem_append] at hq
  cases hq with
  | inl h => exact ht q h
  | inr h => simp only [List.mem_singleton] at h; subst h; exact hp

/-- **The soundness core**: `Config.runTrace` preserves `traceWithin` from its accumulator to its
result. Every recorded `(ℓ, liveBound K e)` is `traceWithin`-good (`labelEff_le_liveBound_of_step`),
so the invariant threads through the machine induction. NO preservation, NO LR. -/
theorem runTrace_traceWithin {Mult : Type} [CommSemiring Mult] [DecidableEq Mult] [EffSig Eff Mult]
    (n : Nat) (cfg : Config) (e : Eff) (t : Trace Eff) (v : Val) (t' : Trace Eff)
    (hrun : Config.runTrace (Mult := Mult) n cfg e t = Result.done (v, t'))
    (ht : traceWithin (Eff := Eff) (Mult := Mult) t) :
    traceWithin (Eff := Eff) (Mult := Mult) t' := by
  induction n, cfg, e, t using Config.runTrace.induct (Eff := Eff) (Mult := Mult) generalizing v t' with
  | case1 cfg e t => simp only [Config.runTrace] at hrun; exact absurd hrun (by simp)
  | case2 n g w e t =>
      simp only [Config.runTrace, Result.done.injEq, Prod.mk.injEq] at hrun
      obtain ⟨-, rfl⟩ := hrun; exact ht
  | case3 n cfg e t hnd a ℓ op arg hperf cfg' hstep ih =>
      obtain ⟨g, K, M⟩ := cfg
      simp only at hperf; subst hperf
      simp only [Config.runTrace, hstep] at hrun
      exact ih v t' hrun (traceWithin_append ht (labelEff_le_liveBound_of_step hstep))
  | case4 n cfg e t hnd a ℓ op arg hperf hstep =>
      simp only [Config.runTrace, hperf, hstep] at hrun; exact absurd hrun (by simp)
  | case5 n cfg e t hnd cfg' hstep hnp ih =>
      simp only [Config.runTrace, hstep] at hrun; exact ih v t' hrun ht
  | case6 n cfg e t hnd hstep hperf hnp =>
      simp only [Config.runTrace, hstep] at hrun; exact absurd hrun (by simp)
  | case7 n cfg e t hnd hstep hperf hnp =>
      simp only [Config.runTrace, hstep] at hrun; exact absurd hrun (by simp)

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
