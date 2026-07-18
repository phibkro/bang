# PATH-reactive-within-observation-reuse — reuse shared work without freezing live thunks

> Reduce repeated derived-formula work inside one observation using ordinary handler-owned memory,
> while preserving call-by-name force, live freshness, static declaration edges, and route agreement.

## Seam

- **From checkpoint**: `PATH-reactive-recomputation-measurement` reports 401 formula invocations for
  104 stable formulas and shows the shared `unitAmount` body executing 100 times per force.
- **To checkpoint**: the prior 401-call baseline is followed by a reuse realization that preserves
  values before and after an input update and reduces the observable formula count to 203.
- **Contract preserved**: force stays unmemoized; the Memo handler is installed inside each observation,
  so its memory cannot survive a State update or freeze a live thunk.

## Layer

- [ ] Kernel  [ ] Compiler  [x] Surface  [x] Meta (tests/docs)

## Actor journey / observable outcome

- **Actor / need**: a spreadsheet implementer wants to reuse an expensive shared formula without
  committing BANG to global call-by-need or cross-observation invalidation.
- **Public starting point**: `bang run examples/reactive-observation-reuse/main.bang`.
- **Terminal observation**: the scoped route yields 7050/7450 at 203 calls each; the adverse retained
  route visibly freezes at 7050 and falls to 201 calls after the update.
- **Adverse / recovery route**: placing the Memo handler outside the observation would retain 20 after
  price changes from 10 to 12 and return stale totals. Install fresh handler memory inside every force.
- **Downstream journey released**: explicit cache lifetime as a semantic design dimension, with a
  falsifiable stale-retention pole before any general cache API.

## Feeds the constraint

- **Binding constraint now**: ADR-0005 makes thunk non-memoization load-bearing for pull freshness;
  ADR-0008 pins call-by-name in the reference, while the measured workload proves repeated derived work.
- **How this path feeds it**: express reuse as an ordinary user effect with handler-owned memory and an
  explicit lexical lifetime. This reuses BANG's existing capability/handler substrate instead of
  changing force or adding a runtime graph.

## Prospective systemic review

| concern | horizon + evidence | likelihood / impact / late cost | disposition now | reopen trigger |
|---|---|---|---|---|
| global thunk memoization freezes reactive cells | immediate; ADR-0005 + `cell_reflects_latest` | high / high / high | **reject** global call-by-need | a distinct memoized value form with live-cell bypass is designed |
| cache survives an input update | first second observation | high / high / medium | **implement** handler inside each force and gate changed input | cross-observation retention is proposed |
| source hoisting changes the formula reference DAG | current declaration facts | high / medium / medium | **reject** hoisting as the product contract | dependencies become explicit first-class metadata |
| compiler CSE reorders/skips effects | any effectful formula | medium / high / high | **defer** optimizer route | purity/effect proof licenses a semantics-preserving pass |
| one Int sentinel is mistaken for a general cache | current handler memory limitation | high / medium / low | **bound** the tracer to one positive-valued formula | polymorphic/ADT handler memory becomes available |
| cache lookup overhead exceeds saved work | cheap multiplication in tracer | medium / medium / low | **measure calls, not speedup** and make no latency claim | representative expensive formula benchmark exists |
| duplicated generated workload drifts | immediate mechanical fixture | high / medium / low | **implement** one deterministic generator + freshness gate | topology must vary independently |
| first-class custom capabilities need multiple operations in concrete Wasm | current natural `lookup`/`store` probe; source/env/compiled pass, Wasm traps | high / high / medium | **defer as a separate backend PATH**; use one explicit `swap` primitive here | the next natural multi-operation capability consumer, or this cache grows beyond one state cell |

## Baseline, falsifier, and evidence

- **Baseline / red observation**: uncached path returns 7050/7450 with 401 formula calls per force.
- **Smallest tracer bullet**: mirror the same 100-line declarations with one explicit `Cap Memo` and
  one state-like `swap`; cache only the shared `unitAmount`, and install `Memo 0` inside the observation
  thunk. A read swaps in the miss sentinel, then restores a hit or stores the computed miss.
- **Positive evidence**: the prior baseline and reuse values agree, while calls fall to 203 because input formulas execute once while
  every line and cache-checking formula remains observable.
- **Negative or recovery evidence**: after price changes, the cached path must return 7450 and again
  report 203. A handler retained outside the thunk returns a stale 7050 and is the adverse pole.
- **Broader convergence gate**: generator freshness, exact graph/output, source/env/compiled/Wasm,
  `just fitness`, and `just verify`.
- **Assumptions / exclusions**: the count excludes effect-operation overhead and is not a wall-clock
  benchmark. The tracer has one positive Int cache entry, no eviction, invalidation, concurrency, or
  dynamic formula identity.

## Plan

1. [x] Map the load-bearing call-by-name/reactivity constraints and compare alternatives.
2. [x] Prove an ordinary updating custom handler can carry cache memory across calls.
3. [x] Generate the cached 100-line mirror and exact before/after comparison.
4. [x] Add the retained-handler stale negative control and converge source/env/compiled routes.
5. [x] Converge concrete Wasm and close with an explicit library-pattern boundary.

## Status

- [x] Started 2026-07-18
- [ ] In flight: none; successor is first-class multi-operation custom-capability dispatch in Wasm
- [ ] Blockers: none
- [x] Completed 2026-07-18
- Retained failed gates / successors: built-in State caps cannot be named as `Cap State` in surface
  signatures → use an ordinary declared `Memo` effect; first 301-call measurement repeated only input
  identities → retain the strengthened shared-derived workload; a two-operation first-class custom
  capability passes source/env/compiled but concrete Wasm reaches the backend's deliberate single-clause
  runtime guard → retain the one-operation `swap` tracer and open runtime operation dispatch separately.
  Final focused gates: query 107/107; source/oracle 60/60; environment 60/60; compiled dogfood 10/10;
  concrete build/Wasm 20/20.
- Full convergence gate: `CHANGELOG_STABLE_REF=codex/reactive-recomputation-measurement just verify`
  passed.
- Successor status: `PATH-wasm-first-class-multi-operation-caps` implements the exact runtime dispatch
  and per-clause update metadata that the retained two-operation failure exposed.
- Reopen / observe: general cache API only after typed keys/values and cache lifetime are designed;
  reopen the one-operation backend boundary at the next natural multi-operation capability consumer

## Owner

- Agent / human: Codex

## Notes

The decision is **ship an explicit user-defined reuse pattern, not a general cache API**. The handler's
lexical position is the invalidation policy: fresh memory per force preserves pull reactivity without
altering thunk semantics or the compiler's static formula graph. The 401→203 reduction is an invocation
count for this fan-out/fan-in workload, not a latency claim.

The one-operation `swap` protocol is semantically sufficient for this single-cell cache and exercises
the same updating-handler memory needed by a richer interface. The failed `lookup`/`store` probe is not
discarded evidence: it identifies a high-likelihood, high-impact backend successor requiring exact
runtime operation identity and per-clause update metadata for first-class custom capabilities.
