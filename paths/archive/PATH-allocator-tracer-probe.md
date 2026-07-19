# PATH-allocator-tracer-probe — bank the first systems-wedge boundary

> Determine whether the accepted userland-handler surface can own a modeled allocator arena and
> expose honest misuse poles without broadening ownership or kernel scope.

## Seam

- **From checkpoint**: compiled browser pack at ◊5.75 plus one-shot permit and ADR-0114 stateful
  custom clauses
- **To checkpoint**: a machine-backed allocator stop and a shared follow-on door justified by two
  north-star consumers
- **Contract preserved**: no kernel/checker/Wasm-emitter change, generalized ownership system, or
  unsupported execution claim

## Actor journey / observable outcome

- **Actor / need**: a Bang systems programmer needs to know whether a handler-owned arena can reject
  allocator misuse without exposing its private state.
- **Starting point**: `just test-allocator-tracer-probe` and
  `docs/notes/allocator-tracer-probe.md`.
- **Terminal observation**: structured state, queryable effect law, exact-once result binding, and a
  direct value update run; all pure computed update spellings stop on the same retained diagnostic.
- **Adverse route**: duplicate and forgotten use report B018; computed transitions retain the exact
  generic JSON refusal.
- **Released decision**: allocator and CALM max-join jointly justify one future effect-free computed
  updating-clause increment.

## Evidence and falsifier

- A literal outer pair with pure computed components was the decisive falsifier. Both `let`
  projections and typed `match` components fail, while a direct pair of values passes.
- Positive programs agree across `env`, `oracle`, `compiled`, and concrete Wasmtime.
- `bang query contract` exports the `Arena` operation/law and checked evidence.
- Exact `check --json` and query JSON are committed under `scratch/allocator-tracer/evidence/`.
- The gate statically pins the absence of a finalizer and rejects any diff to the checker, Core, or
  Wasm emitter authorities used by this probe.

## Prospective systemic review

| concern | evidence | disposition | reopen trigger |
|---|---|---|---|
| private arena transition | computed-update pass/fail matrix | shared pure-computation door, deferred | allocator and CALM max-join acceptance witnesses are designed together |
| stable refusal/misuse codes | generic refusal plus B018 quantity poles | retain generic; do not fix diagnostics in S0 | semantics are ruled and fixture-first product poles exist |
| leak at handler pop | no surface clause; identity pop | finalizer explicitly excluded | independent operator decision with a second consumer |
| effectful/general clauses | ADR-0114 answer-grade boundary | exclude D5, grade polymorphism, type classes, special cases | separate concrete consumer and proof plan |
| ownership/regions/layout/performance | no consumer evidence or measurements | exclude | later concrete systems rung supplies evidence |

## Plan and status

1. [x] Read roadmap, allocator/memory/capability surveys, ADRs, code, and prior questions.
2. [x] Run S0 for structured parameter, at-pop behavior, and `use [1]` operation-result binding.
3. [x] Bisect direct value pair, literal computed components, typed matches, and let-wrapped pair.
4. [x] Retain fixtures through exact JSON, all-engine, query, Wasm, and static gates.
5. [x] Stop before implementation and bank the shared effect-free computed-update door.

- **Started/completed**: 2026-07-19
- **Owner**: Codex systems-allocator lane
- **Result**: semantic stop; no allocator implementation or product diagnostic landed
- **Reopen**: one shared increment, witnessed by allocator and CALM max-join
