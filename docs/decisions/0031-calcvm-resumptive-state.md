# ADR-0031 · CalcVM resumptive state: `evalD` threads a store and services ops inline; the machine RESUMES with a non-discarding `OP` (shape A stays, one-shot)

- **Status:** Accepted + **LANDED** (`2063c0e`, 2026-06-23 — the `state` arm fully implemented & axiom-clean: `compile_correct`/`evalD_agrees_source`/`sim`/`run_evalD` ⊆ {propext, Classical.choice, Quot.sound}, ◊2 gate intact; both load-bearing claims held, the throws⊗state nesting closed via the raised-IH-handback. The `transaction` arm remains the design lock for the next increment.)
- **Date:** 2026-06-23
- **Layer:** K (kernel-adjacent — the calculated machine + its metatheory and the `evalD ≡ Source.eval` bridge). **Tag: K-ADR** (semantic/verification).
- **Resolves:** the CalcVM port's resumptive-handler increment (the `unwindFind` SKIP that O2 left deferred). Ports **ADR-0025** (kernel resumptive state, `dispatchOn` KEEPS `Kᵢ`) and **ADR-0030** (transaction = state over a list-heap) to the *calculated* machine.
- **Builds on:** ADR-0023/0025 (kernel CK machine `splitAt`/`dispatchOn`), the O2 CalcVM increment (`e07d349`: throws-only `unwindFind`, two-part `sim`/`run_evalD`), ADR-0016/0017 (Bahr–Hutton calculation; invariant #4 — the machine is *derived*, not designed).
- **Reference:** Plotkin–Pretnar (algebraic effects: `get`/`put` as operations of a state handler); Hillerström–Lindley (deep handlers resume by re-entering the captured continuation under a reinstalled handler); Bahr–Hutton 2022 (the calculation discipline).

## Context — O2 SKIPS state; the calculated machine must RESUME it

O2 (`e07d349`) made the CalcVM machine **throws-only**: `unwindFind` catches only a `throws ℓ`
handler on `(ℓ, "raise")`, **skipping** `state`/`transaction` frames; `evalD`'s `handle` likewise
forwards a `raised` past a non-`throws` handler. That SKIP was a deliberate deferral, not the final
shape. The kernel reference it must agree with already resumes: `Source.step` (ADR-0025/0030) uses
`splitAt` (returns the inner prefix `Kᵢ`) + `dispatchOn`, which for a `state ℓ s` frame **KEEPS `Kᵢ`**
and reinstalls a deep `state ℓ s'` frame (`get` → `ret s`, state unchanged; `put w` → `ret unit`,
state `:= w`). `transaction ℓ Θ` is the same mechanism over a list-heap.

The CalcVM port is **incomplete** until the calculated machine resumes state too — that is the ◊3
gate (`exec ∘ compile ≡ eval` over the *whole* kernel semantics, not just its throws fragment).

Two difficulties, one denotational and one operational, drive the decision:

1. **Big-step `evalD` cannot resume via the `raised` Outcome.** `evalD` is big-step; its
   `Outcome = term | raised (ℓ, op, v)` carries **no continuation**. When a body raises `get`,
   `evalD` has evaluated M only up to the raise; the "rest of M" is not reified. For `throws` that is
   correct (the continuation is discarded). For `state` it is fatal: resume needs the rest of M. So a
   resumptive `evalD` must service the op **without** ever letting it escape as a bare `raised`.

2. **The machine's `THROW` discards the inner continuation `c`.** `THROW` jumps to the saved OUTER
   continuation (`Kₒ`), dropping the code after it. Resume must instead **continue `c`** with the
   op-result pushed.

## Decision

### D1 — `evalD` threads a label-keyed **state store** and services `get`/`put` **inline**

`evalD` gains a store of the currently-active state handlers, keyed by label, threaded in and out:

```
evalD : Nat → Store → Comp → Option (Outcome × Store)        -- Store mirrors the active `state ℓ s` frames
```

- `handle (state ℓ s) M`: run M under the store extended with `(ℓ ↦ s)`; on a normal terminal,
  **restore** ℓ's prior binding (lexical shadowing — see the nesting note); the handler-return is the
  identity (Q6).
- `up ℓ "get" _` when `ℓ ∈ store` (a *state* handler is active for ℓ): return `term (ret store[ℓ])`
  **at the leaf** — the op is serviced inline, it never propagates as `raised`.
- `up ℓ "put" w` when `ℓ ∈ store`: thread `store[ℓ] := w`, return `term (ret unit)`.
- `up ℓ op v` when `ℓ ∉ store` (no state handler for ℓ): propagate as `raised ℓ op v` — the **throws**
  path, unchanged from O2.

So `raised` is **reserved for throws** after this ADR. The store is the resumptive mechanism; the
big-step difficulty (1) dissolves because state ops are serviced during the recursive descent, not
raised out of it. The state value stays **closed** (ADR-0025 D2 — the focus is closed; copying a
grade-`[]` value costs no variable budget), so threading it is type-preserving for **any** `S` with no
`ω`-restriction — exactly as in the kernel.

*Representation of `Store` (flat `Label → Val` with save/restore vs. an assoc-list stack) is an
implementation choice for the IC to settle against the cell demonstrator + the bridge proof; this ADR
pins only that the store **mirrors the kernel's active `state ℓ s` frames**, not its concrete type.*

### D2 — The machine RESUMES with a non-discarding `OP` instruction; **shape (A) stays** (one-shot)

The CalcVM header warned that resumptive handlers "will need shape (B) (defunctionalized
continuations)." **That is true only for multi-shot** (reify `Kᵢ` as a first-class value, the ADR-0015
frontier). For **one-shot in-place** resume (ADR-0025 D1, the v1 semantics), it is **not** needed:
after `compile (up ℓ op v) c`, the machine's *current code `c`* **is** `Kᵢ`. We simply do not discard
it.

```
compile (up ℓ op v) c   = OP ℓ op v :: c          -- c IS Kᵢ; kept, not discarded
exec … (OP ℓ op v :: c) s hs:
  · find the nearest `state ℓ`/`transaction ℓ` frame in hs (a non-discarding `stateFind`)
  · get : push `ret s`     onto s, leave the frame; continue c       (frames above it KEPT — deep)
  · put : update that frame's stored state to w **in hs**, push `ret unit`; continue c
  · ℓ not a state frame → fall through to the THROW/unwind path (unchanged)
```

No continuation reification, no new `Val` constructor. The HStack frame's stored state is updated in
place; the frames installed above it (Kᵢ's handlers) stay installed — their `UNMARK`s in `c` pop them
on normal return, in order. `THROW` (O2) is untouched.

### D3 — The bridge invariant is a **store ↔ frame correspondence**

`evalD_agrees_source` extends to state by the invariant: **`store[ℓ]` = the stored `s` of the nearest
active `state ℓ s` frame in the kernel's `EvalCtx`** (and `∉ store` ⟺ only `throws`/no frame for ℓ).
This is a direct correspondence, *not* a representation translation — which is the whole reason D1
keys the store by label (matching the kernel's `state ℓ` label-dispatch) rather than introducing an
external untyped heap. The bridge stays "mechanical" in the D1-A sense.

### D4 — Scope: **state first, then transaction**; **one-shot only**

- **State** (`get`/`put`, single closed cell) lands first — the minimal resumptive mechanism. The
  demonstrator is the cell `handle (state ℓ 0) (let _ = put 7 in get)` reaching `done 7` through
  **both** `evalD` and `exec ∘ compile`.
- **Transaction** (ADR-0030: `new`/`read`/`write` over a list-heap) is "state generalized to a
  list-heap" — the kernel's `dispatchOn` already unifies them. Fold in **after** state is green, as a
  follow-on increment (the store becomes a list-heap; the OP mechanism is identical). Decide fold-in
  vs. separate unit when state lands.
- **Multi-shot / first-class continuations** stay the **ADR-0015 frontier** — explicitly out of
  scope. `Kᵢ` is not reified; the current code `c` is re-entered exactly once, in place.
- **Arithmetic** (a real counter `get; put (get+1)`) stays a separate K-ADR (invariant #5). The cell
  needs none.

## Rejected alternatives

| option | why not |
|--------|---------|
| Reify the continuation in `Outcome` (`raised` carries the rest of M as a function) — denotational shape (B) | Strictly more metatheory (a continuation in the Outcome, its typing) for one-shot state, which D1 services inline with a store instead. Shape (B) is the multi-shot frontier (ADR-0015); pulling it in now over-builds. |
| An external untyped heap keyed by address (not label) | Breaks D3: the bridge becomes a representation translation (address-heap ↔ label-frames) rather than a correspondence, making `evalD_agrees_source`'s state case cross-representational and expensive. Keying by label mirrors the kernel's `state ℓ` dispatch. (This is transaction's *internal* shape later, under one label.) |
| Small-step `evalD` (thread state in a residual config, like `Source.step`) | Abandons the big-step denotational shape that makes `compile_correct` a **plain equality** (no logical relation; k2-playbook §2). The whole D1-A payoff is big-step `evalD` vs. small-step kernel; collapsing `evalD` to small-step throws it away. |
| Multi-shot resume now (reify `Kᵢ` as a `cont` value) — shape (B) machine | More machinery (defunctionalized continuations, a `cont` value, its compilation) for a capability v1 does not need. One-shot in-place is the minimal mechanism that runs a state cell; multi-shot is additive later (ADR-0015 "revisit if"). |
| Keep `unwindFind`/`evalD` throws-only (stay deferred) | The ◊3 gate is `exec ∘ compile ≡ eval` over the **whole** kernel semantics; the kernel resumes state (ADR-0025) and transaction (ADR-0030). Deferring further leaves the CalcVM port structurally incomplete for no remaining technical reason. |

## Implementation staging

```
W0  Design spike + this lock — VALIDATE the two load-bearing claims against the checker before
    committing breadth: (i) the machine "c IS Kᵢ ⇒ shape (A) suffices" claim by running the cell
    through exec∘compile to `done 7`; (ii) the D1 store-threaded evalD by running the cell to
    `term (ret 7)`. If either is refuted, REVISE this ADR (self-correcting — the checker decides).
W1  evalD (CalcVM.lean) — Store + the D1 clauses; cell ⇒ `term (ret 7)`. Outcome/evalD shape change
    (STATEMENT_CHANGE_OK).
W2  machine (CalcVM.lean) — `OP` instr (D2) + `stateFind`/in-place HStack update; compile emits it;
    exec resumes; cell ⇒ `done 7` via exec∘compile.
W3  compile_correct (CalcVM.lean) — extend `sim` to the resume case: relate big-step store-threading
    to the machine's in-place HStack update, deep-handler setting. THE HARD CORE; the proof budget.
W4  bridge (CalcVM.lean) — extend `evalD_agrees_source`/`run_evalD` to state via the D3 store↔frame
    invariant (vs. Source.eval's frame-threading).
W5  gate + audit — new headlines axiom-clean ⊆ {propext, Classical.choice, Quot.sound}; ◊2 gate
    (`no_accidental_handling`, `rowinst_requires_disjoint`) still 0-axiom; rfl/native_decide cell
    demonstrator in the diff-test battery. THEN decide transaction fold-in (D4).
```

`compile_correct` stays op-general; the resume cases are added alongside the throws cases, not
replacing them. The throws path (O2) is invariant under this ADR.

## Revisit if

- **Multi-shot / first-class continuations** are wanted: `Kᵢ` becomes a reified value and the machine
  moves to shape (B). A new ADR (the ADR-0015 frontier); additive to this one.
- **W0 refutes a load-bearing claim** (the "c IS Kᵢ" shape-(A) sufficiency, or the inline-service
  store): revise D1/D2 here with the checker's evidence before W1 proceeds.
- **Transaction needs more than a list-heap** (e.g. typed heterogeneous cells): a separate ADR over
  this mechanism; the state core is unaffected.
