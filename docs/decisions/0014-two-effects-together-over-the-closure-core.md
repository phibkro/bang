# ADR-0014 · Throws *and* State together over the closure core — `CalcCBNEffSt` (the effect-row model realized; State persists through a throw)

- **Status:** Accepted
- **Date:** 2026-06-01
- **Related:** 0012 (Throws over closures), 0013 (State over closures — this fuses the
  two), 0011 (the per-effect machines), 0010 (the CBN closure machine), 0008, 0009,
  0003 (STM is the privileged transactional primitive), roadmap K3

## Context

ADR-0012 (`CalcCBNEff`, Throws) and ADR-0013 (`CalcCBNSt`, State) each composed *one*
effect with the closure/CBN core. But BANG's model is **effect rows** — a function's
row is a *set* of effects, and a program may use several at once. The K3 capstone is
to put **both effects in one machine** and show they coexist: the handler stack of
`CalcCBNEff` *and* the state register of `CalcCBNSt`, threaded through the same
closure core. This realizes the effect-row model in the calculated machine.

Putting two effects together forces one new design decision — **how do State and
Throws interact?** When a `throw` propagates past `put`s, is the state kept or rolled
back?

## Decision

Calculate **Throws (`perform`/`handle`) and State (`get`/`put`) together** as one
module, `Bang/CalcCBNEffSt.lean` — Bahr–Hutton's monad swap with *both* layers at
once: `eval : Nat → State → Env → Src → Option (Outcome × State)`. Every result
carries the current state; on a propagating effect, the carried state is the state
**at the point of the throw**.

- **State persists through a throw** (the design decision). The register simply
  threads through unwinding: a `put` before a `throw` is kept, a handler catching the
  throw resumes from the throw-time state, and an uncaught throw carries the state to
  the top. **Rationale:** STM is BANG's privileged *transactional* primitive
  (ADR-0003), so plain `State` is the simple mutable register and transactional
  rollback is exactly what STM is *for* — not a property of ordinary `get`/`put`. The
  handler frame therefore saves env+stack but **not** state.
- **The machine is the *union* of the two parents' mechanisms, running at once.**
  State **threads** (resumable, no re-throw) while Throws **re-throws** an `uncaught`
  at the meta-call boundary (zero-shot) — see the effect-shape map in ADR-0013. Both
  happen simultaneously: the nested APP/FORCE meta-run returns `(Result × State)`; on
  a normal `halt` the caller threads the new state, on an `uncaught` the boundary
  re-throws *carrying the throw-time state*.
- **Scope: `get`/`put` (a single global register) + `perform`/`handle` + the CBN
  core, `add` only.** `runState` (scoped State) is **omitted** here on purpose: a
  `throw` escaping a `runState` raises a *second* sub-decision (does the inner state
  leak out, or is the outer cell restored on unwind?) that is orthogonal to "two
  effects coexist." It is a documented follow-up.

## Rationale

- **Faithful to the papers** (ADR-0004): the instructions are exactly the union of
  `CalcCBNEff`'s `{MARK,UNMARK,THROW}` and `CalcCBNSt`'s `{GET,PUT}` over the shared
  closure core — nothing hand-designed; both monad layers swapped together.
- **Provable.** `exec ∘ compile ≡ eval` is closed with **no `sorry`** via the
  **four-part** mutual simulation (eval-ret · eval-exc · forceV-ret · forceV-exc,
  by induction on fuel) — `CalcCBNEff`'s four-part proof with the state register
  threaded through every step and `throwExec` carrying the throw-time state. The
  combination is the union of the two parents' proofs; no new technique.
- **It demonstrates the effect-row promise.** The kernel carries *two* effects'
  apparatus at once and they interact correctly — a program whose row is
  `{Throws, State}` runs, with a definite, documented interaction semantics.

## Rejected alternatives

| option | why not |
|--------|---------|
| **rollback / transactional State** (handler checkpoints the state; catching restores it) | conflates plain `State` with STM. STM is the privileged transactional primitive (ADR-0003); ordinary `get`/`put` should be the simple threaded mutable register. Persist is the honest default; transactions are STM's job |
| **include `runState` now** | a `throw` escaping a `runState` forces a *second* decision (leak the inner state vs restore the outer cell on unwind) orthogonal to coexistence; defer it so this increment stays about "two effects in one machine" |
| **a single generic handler engine for both** (toward reification) | unnecessary here — Throws is zero-shot, State is tail-resumable; the per-effect mechanisms compose directly. The generic engine is the reification frontier (ADR-0011/0013), still deferred |

## Consequences

- One new module (`Bang/CalcCBNEffSt.lean`, proven) + oracle ops
  (`evalcbneffst`/`execcbneffst`) + a `harness/test/calc-cbn-eff-st.test.ts`
  differential test (goldens for state-persists-through-a-caught-throw, an uncaught
  throw carrying state, the recovery seeing both payload and carried state, state
  carried through a call-boundary re-throw and through label forwarding, laziness;
  plus a 500-run fuzz). 86 tests green.
- **Open / next:** (a) **`runState` × throw** — pick leak-vs-restore-on-unwind and
  prove it (the deferred sub-decision); (b) a **user-extensible** handler set / effect
  rows over an arbitrary effect signature (generalising beyond the two baked-in
  effects); (c) **continuation reification** for multi-shot / non-tail handlers (the
  frontier; ADR-0011/0013); (d) STM stays axiomatized (ADR-0003); (e) K4 front end.

## Revisit if

- A program needs `get`/`put` to **roll back** on an exception → that is the STM use
  case (ADR-0003), not a change to plain `State`; model it with the STM primitive.
- `runState` is added and its **throw-escape** semantics must be pinned → a focused
  follow-up ADR (leak vs restore-on-unwind), likely making `runState` install an
  unwind-restoring frame.
- More than two effects, or a user-defined effect signature, makes the per-effect
  machines clash → reconsider a single unified effect-monad machine (still calculated).
