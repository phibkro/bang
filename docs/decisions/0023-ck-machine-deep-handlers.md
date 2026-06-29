# ADR-0023 · The CK machine: deep handlers, and why `progress` needs a stack

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: CK machine for deep handlers — `Source.step` becomes config-level (`EvalCtx × Comp`); throws discards the captured continuation.
- **Resolves**: Q4, Q5, Q6, Q13
- **Depends-on**: 0020, 0021, 0022

- **Status:** Accepted (design lock for the operational-semantics rewrite; implementation staged below)
- **Date:** 2026-06-22
- **Layer:** K (kernel — operational semantics + the STD-block metatheory over it)
- **Supersedes:** ADR-0022 **D3** (the claim that stating `progress`/`type_safety` at effect `⊥`
  restores them under the substitution-step). D1/D2/D4/D5 (EffSig, the `up` rule, label-discharging
  `handle`, handler typing) **stand**, with the D5 correction in §"Corrections exposed" below.
- **Resolves:** OPEN_QUESTIONS Q6 (deep-handler resumption — moves to the CK machine, throws case).
  Q13 (op-granularity) is **co-resolved**: the machine fixes the deep-nesting facet, but the
  wrong-op-same-label facet is independent and still needs op-partial signatures (D6 below).
- **Builds on:** ADR-0019/0020 (graded de Bruijn context), ADR-0021 (the STD block + the
  effect-on-judgment discipline), ADR-0022 (operations + handlers). The `Frame`/`EvalCtx` ADT it
  needs already exists (`Bang/Core/IR.lean` §1.3, built for exactly this).
- **Reference:** Felleisen–Friedman CK/CEK; CBPV stack machine (Levy, *Call-by-Push-Value* ch. 3 —
  CBPV's stacks *are* evaluation contexts); Hillerström–Lindley handler dispatch (deep handlers
  search the frame stack for the nearest matching handler).

## Context — `progress` is false under the substitution step

ADR-0022 D3 asserted that stating `progress` at effect `⊥` (a fully-handled program) makes the
unhandled-`up` normal form untypable, so `progress` collapses to `isReturn ∨ steps`. **This is false.**
A machine-checked counterexample (reproduced in `/tmp/cex_check.lean`; the EffSig instance is trivial,
all-unit):

```lean
cex := handle (throws 0) (letC (up 0 "raise" vunit) (ret (vvar 0)))

✓ Source.step cex = none           -- STUCK (shallow step matches `up` only DIRECTLY under handle)
✓ ¬ isReturn cex                   -- not a value
✓ HasCTy [] [] cex ⊥ (F one unit)  -- well-typed at the runnable precondition (effect ⊥, closed)
```

The triple contradicts `progress : HasCTy [] [] c ⊥ (F q A) → isReturn c ∨ ∃ c', step c = some c'`.

The root is **not** Q13 op-granularity (that was diagnosed from a *shallow-body* mental model). The
counterexample uses the **right label and the right op** (`raise` under `throws 0`) and is still
stuck — because the operation is nested under a `letC`. The simplified `Source.step` is a **shallow**
handler: its head pattern `handle (throws ℓ) (up ℓ' "raise" v)` only fires when the operation is
*directly* under the handle. A well-typed body can place the operation under any number of
`letC`/`app` frames, and a real (deep) handler must reach past them, catch the operation, and —
for a zero-shot exception — **discard the intervening continuation**. Substitution-style stepping
structurally cannot express "find the operation under an evaluation context and discard the context":
that is what a stack is for.

So the operational semantics must become a **CK machine**. This is OPEN_QUESTIONS Q6's "option 2",
forced now rather than deferred, because `progress`/`type_safety` are ◊2 headline theorems and they
are currently held up by a `sorry` over a *false* statement — the precise anti-pattern the proof
discipline forbids ("a green build that lies"). Naming the right answer (SOUL): the CK machine is the
correct semantics for an effect-handler language; the substitution step was a scaffold that served
the pure STD block and breaks the moment operations cross a binder.

## Decision

### D1 — The machine state is a focus + a stack of frames

`Config := EvalCtx × Comp`, where `EvalCtx := List Frame` (innermost frame first, already defined)
and `Frame := letF Comp | appF Val | handleF Handler` (already defined). **Binding stays
substitution-based** — this is a CK machine, *not* a CEK machine: no closures, no environments. The
consequence is load-bearing for the metatheory: **the focus computation is always closed** (`Γ = []`,
hence `γ = []`), because every binder is resolved by `Comp.subst` (a closed value) at reduction time.
Grades therefore never thread across the stack; they live only inside stored `letF` continuations and
are discharged by the existing closed-`v` `subst_value` (`γ_Δ = 0`).

### D2 — Transitions

Write `⟨K, M⟩` for a config. `■` = the discharged/finished marks.

```
PUSH (decompose — focus the evaluated sub-term):
  ⟨K, letC M N⟩          ↦ ⟨letF N   :: K, M⟩
  ⟨K, app M v⟩           ↦ ⟨appF v   :: K, M⟩
  ⟨K, handle h M⟩        ↦ ⟨handleF h :: K, M⟩
  ⟨K, force (vthunk M)⟩  ↦ ⟨K, M⟩

REDUCE (focus is terminal; interact with the top frame):
  ⟨letF N   :: K, ret v⟩ ↦ ⟨K, N[v]⟩            -- let: bind, then continue
  ⟨appF v   :: K, lam M⟩ ↦ ⟨K, M[v]⟩            -- β
  ⟨handleF h :: K, ret v⟩↦ ⟨K, ret v⟩           -- handler return clause = identity (Q6 simpl.)

DISPATCH (focus performs an operation — DEEP handler search):
  ⟨K, up ℓ op v⟩ with K = Kᵢ ++ [handleF h] ++ Kₒ,
       h handles (ℓ, op), no frame in Kᵢ handles (ℓ, op):
    throws:  ↦ ⟨Kₒ, ret v⟩                       -- ABORT: discard Kᵢ (the captured continuation)
                                                  --        and the handler frame
  ⟨K, up ℓ op v⟩ with no handling frame in K     ↦ stuck (unhandled operation)
```

`state` dispatch (resume, threading the stored state) is **deferred** with Q12/Q6 — the same reason
Unit 2 scoped to `throws`: graded state threading needs the reified continuation, which the machine
now *has*, but its grade metatheory is a separate piece (Q12). The machine's dispatch rule is written
to admit `state` later (the search + split is identical; only the post-dispatch config differs).

### D3 — `Source.eval` is unchanged in signature; `Source.step` becomes config-level

```lean
Source.eval : Nat → Comp → Result Val      -- UNCHANGED signature: load ⟨[], c⟩, run, unload at ⟨[], ret v⟩
Source.step : Config → Option Config        -- WAS Comp → Option Comp
```

`type_safety`'s frozen statement (`Source.eval fuel c ≠ stuck`) is therefore **unchanged** — `eval`
stays whole-program. Only `preservation` and `progress` mention `Source.step` and move to the config
level (see D5). This keeps the user-facing safety contract identical while making the internal objects
honest.

### D4 — Configuration typing `HasStack` / `HasConfig` (effects + types only)

A stack transforms a focus type to a whole-program type. Because the focus is always closed, the
stack typing tracks **only effects and computation types** — no grade vectors compose across frames
(each `letF` node carries a full graded continuation derivation internally):

```lean
inductive HasStack : EvalCtx → Eff → CTy → Eff → CTy → Prop
  | nil    : HasStack [] e C e C
  | letF   : HasCTy (qk :: []) [A] N e₂ B →                     -- the let continuation (one binder)
             HasStack K (e₁ ⊔ e₂) B eₒ Cₒ →
             HasStack (Frame.letF N :: K)   e₁ (CTy.F q A)  eₒ Cₒ
  | appF   : HasVTy [] [] v A →
             HasStack K e B eₒ Cₒ →
             HasStack (Frame.appF v :: K)   e (CTy.arr q A B) eₒ Cₒ
  | handleF: opArg ℓ "raise" = A →                              -- throws answer-type (see corrections)
             e ≤ labelEff ℓ ⊔ φ →                               -- discharge ℓ (label-removing, ADR-0022 D4)
             HasStack K φ (CTy.F q A) eₒ Cₒ →
             HasStack (Frame.handleF (Handler.throws ℓ) :: K) e (CTy.F q A) eₒ Cₒ

def HasConfig (cfg : Config) (eₒ : Eff) (Cₒ : CTy) : Prop :=
  ∃ e C, HasCTy [] [] cfg.2 e C ∧ HasStack cfg.1 e C eₒ Cₒ
```

The `letF` node re-uses the EXISTING graded `letC` premise shape (`(q1 * q_or_1 q2) :: γ₂`,
specialized to the closed `γ₂ = []`); firing it is the existing `subst_value` at closed `v`.

### D5 — `preservation` / `progress` restated at the config level (STATEMENT_CHANGE_OK)

```lean
theorem preservation : HasConfig cfg eₒ Cₒ → Source.step cfg = some cfg' →
                       ∃ eₒ' ≤ eₒ, HasConfig cfg' eₒ' Cₒ
theorem progress     : HasConfig cfg ⊥ (CTy.F q A) →
                       isReturnConfig cfg ∨ ∃ cfg', Source.step cfg = some cfg'
  where isReturnConfig ⟨[], ret v⟩ = True
```

`progress` is now **genuinely true for effectful programs**: a `⟨K, up ℓ op v⟩` config at whole-program
effect `⊥` always has a frame in `K` *catching `(ℓ, op)`* — the label `ℓ` (`labelEff ℓ ≰ ⊥`) must be
discharged by some `handleF ℓ` up the stack (`HasStack` forces it), and op-partiality (D6) forces that
handler to actually catch `op` (the only typable op under `throws ℓ` is `"raise"`) — so DISPATCH fires.
The deep counterexample now steps: `cex ↦* ⟨[], ret vunit⟩` = `done`.

`type_safety` keeps its frozen statement (D3) and is re-derived from the config-level
`progress` + `preservation` via the load/unload bridge (`eval` ≈ iterate config `step` from `⟨[], c⟩`).

### D6 — Co-requisite: op-partial signatures + label separation (closes Q13 for real)

The machine fixes the *deep-nesting* facet of the progress wall but **not** the *wrong-op-same-label*
facet. `handle (throws ℓ) (up ℓ "get" v)` is well-typed at `⊥` (label `ℓ` is in the row, the handler
discharges `ℓ`) yet **stuck** (DISPATCH skips the `throws` frame — it doesn't catch `get` — and hits
`[]`). Two `EffSig` additions close it, exactly the two sub-gaps the Q13 note named:

1. **Op-partial signatures** (Q13 option 1): `opArg`/`opRes : Label → OpId → Option VTy` (`none` = the
   operation is not in the label's interface). `up` requires `opArg ℓ op = some _`; `handleThrows`
   requires `ℓ`'s interface is exactly `{"raise"}` (`opArg ℓ op = some _ ↔ op = "raise"`). Then
   `up ℓ "get"` under a `throws ℓ` is **untypable**, so the stuck config never arises.
2. **Label separation**: `labelEff ℓ ≤ labelEff ℓ' ⊔ φ → ℓ ≠ ℓ' → labelEff ℓ ≤ φ`. Needed in
   preservation's DISPATCH case: when `dispatch` skips a *non-matching, different-label* `handleF ℓ'`,
   the performed label `ℓ` must survive past it to reach its handler. Holds for `Finset` singletons
   (atoms in a distributive lattice); added as an `EffSig` law.

These are additive to ADR-0022's `EffSig` (Unit 1) — `labelEff_ne_bot` stays; `opArg`/`opRes` change
codomain to `Option VTy`; two laws join. The `up` rule and every `up` proof case re-touch (the
`some _` premise); this is the "op-aware EffSig redesign" the handoff anticipated, now landed as part
of making `progress` genuinely true rather than as a standalone Q13 task.

## Corrections this exposes (the ADR-0021 pattern, again)

Building the machine surfaces a typing-rule bug, exactly as proving `preservation` surfaced four in
ADR-0021. Record it; do not paper over it.

- **`handleThrows` needs the answer-type premise `opArg ℓ "raise" = A`.** ADR-0022 D5 wrote the throws
  clause as `opArg ℓ "raise" = opRes ℓ "raise"` — the operation's *own* arg=res shape. That is the
  wrong constraint. Under a deep handler, `handle (throws ℓ) (letC (up ℓ "raise" v) N)` has block
  result type `A = (type of N)`, while the raise payload has type `opArg ℓ "raise"`. The ABORT
  reduction yields `ret v` with `v : opArg ℓ "raise"`, which must inhabit `F q A` — so soundness
  needs `opArg ℓ "raise" = A` (payload type = the handle block's result type), **not** `opArg = opRes`.
  In the shallow step this was masked because the body *was* the `up`, forcing `A = opRes ℓ "raise"`
  by coincidence. The `handleF` stack rule (D4) carries the corrected premise; the surface
  `HasCTy.handleThrows` rule is amended to match. (`opRes ℓ "raise"` becomes irrelevant — `raise`
  never returns to its continuation; `N` is dead-but-typechecked code.)

## Implementation staging

```
Unit A (machine)     Operational.lean: Config, plug, handlesOp, the deep-dispatch split, configStep,
                     and eval over configs. Pure executable code — smoke-tested by RUNNING the
                     counterexample to `done vunit` and re-running the existing eval examples. No
                     proofs touched yet; STD block goes red (step signature changed).
Unit B (typing)      HasStack / HasConfig (Syntax.lean); amend HasCTy.handleThrows answer-type
                     premise; restate preservation/progress at config level (Spec.lean,
                     STATEMENT_CHANGE_OK). Build red until Unit C.
Unit C (proofs)      Re-prove preservation/progress/type_safety over the machine, axiom-clean.
                     §A–§D of Metatheory.lean (grade arithmetic, length, weakening, substitution)
                     are STEP-INDEPENDENT and carry over unchanged; only §E (the STD block + the
                     step-inversion lemmas) is rewritten. Pair the proof-engineer.
```

`§A–§D survive` is the reason this is bounded: the hard graded-substitution machinery
(`subst_gen`/`subst_value`, weakening, the `GradeVec` lemmas) is about *typing under substitution*,
not about *stepping strategy*, so the rewrite is confined to the operational layer and §E.

`zero_usage_erasable` stays deferred to ◊4; `state` dispatch + its graded threading stay deferred
to Q12 (now unblocked by the reified continuation the machine provides).

## Rejected alternatives

| option | why not |
|--------|---------|
| Keep the substitution step; restrict typeable handle bodies so operations are head-only | Not expressible as a typing rule (head-position is an operational, not a type, property). A `sorry` over a false statement, or a language with no `let` between perform and handler — both lie about what the kernel accepts. |
| Term-level step defined as load→configStep→unload after **each** config step | A single PUSH step unloads to the *same term* (`plug` is the inverse of decompose), so `step c = some c` — `eval` spins without progress. The machine must run multiple internal steps per observable reduction; the honest object is the config, not the term. |
| Defer the whole thing: keep the `sorry`, move to Unit 3 | Unit 3 (`no_accidental_handling`) doesn't strictly need `progress`, but shipping ◊2 with a headline theorem held up by a `sorry` over a known-false statement fails invariant #1 and the proof discipline. The lie compounds. |
| CEK machine (environments/closures instead of substitution) | Would make the focus *open* (free vars resolved by an environment), forcing grade vectors to thread through the stack and the closure typing — strictly more metatheory for no ◊2 benefit. Substitution keeps the focus closed; grades stay trivial. Revisit only if performance (a second-class concern, invariant #7) ever demands it. |

## Revisit if

- `state` handlers are needed (Q12): the DISPATCH rule's `state` arm resumes with the reified `Kᵢ`
  continuation instead of discarding it; `HasStack` gains a `state` `handleF` case. The machine shape
  here does not revert.
- Multi-shot / first-class continuations are wanted: the captured `Kᵢ` becomes a reifiable value
  (`cont`); a new `Val` constructor + an ADR. The stack is already the continuation, so this is
  additive.
- Operation names go symbolic (Q7) or signatures become op-partial (the Q13 `Option VTy` shape): the
  `handlesOp` predicate and `EffSig` re-key in one place; the machine is unaffected.
