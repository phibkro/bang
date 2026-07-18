# PATH-reactive-spreadsheet-tracer — make pull reactivity observable as a spreadsheet

> Extend the proven one-cell reactivity mechanism through the smallest spreadsheet-shaped public
> journey, including the most likely authoring mistake, before deciding whether explicit dependency
> observation or cached incremental recomputation is justified.

## Seam

- **From checkpoint**: resource-contract evidence integrity is paved; organic correction is explicitly
  deferred, not completed
- **To checkpoint**: a multi-formula spreadsheet journey runs with identical live and stale-snapshot
  observations across the supported execution routes
- **Contract preserved**: reactivity remains equation/operator behavior over ordinary unmemoized thunks
  under ADR-0005/0006; no second kernel primitive or runtime is invented

## Layer

- [ ] Kernel  [ ] Compiler  [x] Surface  [x] Meta (docs/process)

## Actor journey / observable outcome

- **Actor / need**: a BANG developer needs to connect mutable input cells to derived formulas and know
  whether a later input update remains visible.
- **Public starting point**: `examples/reactive-spreadsheet/main.bang` through `bang check` and `bang run`.
- **Terminal observation**: every run route prints `((22, 26), (22, 22))`: the live formula changes after
  the price update while the deliberately sampled snapshot does not.
- **Adverse / recovery route**: forcing a formula before wrapping the result in a thunk freezes a value;
  keep the force inside the formula thunk to retain the live relationship.
- **Downstream journey released**: this journey.

## Feeds the constraint

- **Binding constraint now**: `docs/roadmap/project-roadmap.md` names spreadsheet/reactive dataflow as the
  next project that exercises BANG's distinctive dormant reactivity operator; ADR-0005 proves only the
  mechanism and one-cell liveness.
- **How this path feeds it**: put two inputs and three dependent formulas through the public compiler and
  execution chain, making live recomputation and sampling loss observable before adding machinery.

## Prospective systemic review

| concern | horizon + evidence | likelihood / impact / late cost | disposition now | reopen trigger |
|---|---|---|---|---|
| early forcing silently turns a formula into a stale snapshot | first spreadsheet; ADR-0005 makes sampling explicit but source shape is subtle | high / high / low now | **implement** adverse route and recovery explanation | closed for this tracer; reopen on a new formula syntax |
| dependency shape cannot be queried independently of source | next spreadsheet/toolchain slice; local `let` formulas are not compiler fact nodes | medium / medium / rising with tooling consumers | **preserve and defer** explicit graph work | second consumer, or inability to explain/inspect dependencies from source |
| every observation recomputes the whole reachable formula chain | larger sheets; current thunk semantics deliberately do not memoize | medium / medium / high if a cache contract leaks late | **defer** cached incremental recomputation until measured | representative sheet (for example ≥100 cells) plus recomputation trace/benchmark shows cost |
| cycles become possible but have no diagnostic | future recursive or first-class formula graphs; this static `let` DAG cannot cycle | low now / high later / medium | **defer** | recursive/formula-graph support or first real cyclic dependency |
| push scheduling introduces glitches or hidden ordering | not required by this pull-observed program | low / high / high | **reject** for this tracer | a project requires push propagation or multi-observer scheduling |
| a new signal/kernel primitive duplicates proven semantics | current program already checks and runs end to end | low / high / high | **reject** | only if a demanded journey is impossible under the existing operator/thunk contract |
| one engine masks a route-specific semantic mismatch | current compiled/Wasm chain has distinct machines | medium / high / low now | **implement** corpus and concrete-Wasm differential evidence | any route diverges from `expected.txt` |

## Baseline, falsifier, and evidence

- **Baseline / red observation**: `Bang.Surface.cell_reflects_latest` establishes one-cell pull liveness,
  but no public example composes a formula DAG or exposes the sampling failure mode.
- **Smallest tracer bullet**: two named State inputs (`price`, `quantity`) and three ordinary thunk
  formulas (`subtotal`, `tax`, `total`) observed before and after one update.
- **Positive evidence**: source/oracle, environment-machine, calculated-machine, compiled, and concrete
  Wasm routes all produce `((22, 26), (22, 22))`.
- **Negative or recovery evidence**: the same program contrasts live `total` (`22 → 26`) with an
  early-forced `snapshot` (`22 → 22`) and documents how to retain the dependency.
- **Broader convergence gate**: example corpus, effects-to-Wasm differential, `just fitness`, and
  `CHANGELOG_STABLE_REF=codex/actor-journey-lifecycle just verify`.
- **Assumptions / exclusions**: formulas and their dependency shape are static source structure. This
  proves pull recomputation on observation, not an explicit runtime graph, caching, selective
  invalidation, push propagation, cycle diagnostics, performance, or glitch freedom.

## Plan

1. [x] Freeze the smallest live/stale spreadsheet program and generate its expected output from the runner.
2. [x] Document the public journey, recovery route, and honest semantic boundary beside the example.
3. [x] Run every example route, concrete Wasm differential, repository fitness, and full verification gate.
4. [x] Move CONTEXT and the product roadmap to this tracer while retaining organic correction as deferred.
5. [x] Close this tracer and use its evidence to choose dependency observation before any caching work.

## Status

- [x] Started 2026-07-18
- [ ] In flight: none; successor work begins from dependency observation rather than caching
- [ ] Blockers: none
- [x] Completed 2026-07-18
- Retained failed gates / successors: first fitness run caught that moving CONTEXT's lead orphaned the
  completed `PATH-contract-query-integrity` record → retain it in the completed-path map; second fitness
  run caught the compiled battery's stale generated tool index → regenerate `tools/README.md`;
  one-cell-only baseline → multi-formula live/stale tracer; unobservable local dependency graph →
  candidate dependency-observation successor
- Reopen / observe: add caching only after a representative workload and trace demonstrate repeated
  recomputation cost; reopen semantics if any execution route disagrees

## Owner

- Agent / human: Codex

## Notes

This PATH is the second lifecycle canary after `PATH-organic-resource-validation`. Its actor terminal and
adverse route changed the artifact: the stale-snapshot contrast is part of the same executable program,
not merely a warning in prose. The spreadsheet project remains live after this tracer; the tracer does
not claim the roadmap's full incremental-recomputation capability.
