# PATH-queryable-module-graph — expose the resolver DAG before caching it

> Export the exact transitive module set and dependency edges already discovered by BANG's resolver,
> so a tool author can observe invalidation fanout before the project designs hashes or a cache.

## Seam

- **From checkpoint**: exact multi-operation capability dispatch removed the concrete-Wasm workaround
  exposed by the spreadsheet/reuse sequence.
- **To checkpoint**: `bang query dump examples/json/main.bang` reports one entry node, three imported
  modules, and the five exact dependency edges of its diamond-shaped resolver walk.
- **Contract preserved**: the resolver remains the single source of truth; query facts add no second
  parser, resolver, checker, filesystem traversal, or incremental scheduler.

## Layer

- [ ] Kernel  [x] Compiler  [ ] Surface language  [x] Meta (query schema/tests/docs)

## Actor journey / observable outcome

- **Actor / need**: a build-tool or editor author needs the compiler's real module DAG to determine
  which modules might be affected by a change.
- **Public starting point**: `bang query dump <entry.bang>`.
- **Terminal observation**: the existing flat fact base includes `modules` and `moduleDeps` tables;
  JSON/Calc diamonds contain one row per logical module and one row per dependency edge.
- **Adverse / recovery route**: a single-file/stdin program reports only `@entry` and no edges; diamond
  imports do not duplicate nodes; resolution failures still return the standing fail-loud diagnostic.
- **Downstream journey released**: a following measurement slice can compute reverse-dependency fanout
  and compare changed module/core facts without first reverse-engineering private resolver state.

## Feeds the constraint

- **Binding constraint now**: `dump` exposes only the entry file's direct `imports`/`uses`; the resolver's
  transitive dependency-first walk disappears when modules are merged into one flat `Prog`.
- **How this path feeds it**: carry flat logical module/dependency facts beside the already-retained
  declaration provenance in `ResolvedFile`, then pass them to `Query.dumpJsonP`.

## Prospective systemic review

| concern | horizon + evidence | likelihood / impact / late cost | disposition now | reopen trigger |
|---|---|---|---|---|
| a second graph disagrees with resolution | this PATH; existing resolver state already has the graph | medium / high / high | **implement** by projecting the completed resolver walk only | resolver representation changes |
| source paths leak host layout | first public dump; agent-readable JSON may be shared | medium / medium / compatibility-high | **reject paths**; export logical names and a reserved `@entry` only | a diagnostic/source-map consumer requires locations |
| bundled and project modules become indistinguishable | first host-IO graph; resolver already knows bundled precedence | medium / medium / low | **preserve** an explicit origin field | a third module origin is introduced |
| additive tables break strict consumers | current public schema contract says ignore unknown fields | low / medium / medium | **preserve** schemaVersion 1 and extend its golden/forward-compatibility gates | a field is removed, renamed, or changes meaning |
| content hashes harden at the wrong boundary | next cache/store slice; Q34 keeps surface-vs-core fork open | high / high / high | **defer hashes**; observe topology first | invalidation measurement or store implementation starts |
| graph order becomes accidental API | resolver order is dependency-first but consumers need relations | medium / low / medium | **document rows as ordered deterministically, semantics as sets** | a consumer demonstrates order dependence |
| module aliases/`use` selections need edge kinds | build invalidation currently needs dependency reachability only | low / medium / low | **defer with trigger**; keep entry `imports`/`uses` tables unchanged | a query needs transitive import-vs-use semantics |
| large graph export costs dominate queries | current examples have tiny DAGs; no measurement | low / low / low | **accept linear projection**, measure before optimizing | representative query latency or graph size crosses a named threshold |

## Baseline, falsifier, and evidence

- **Baseline / red observation**: JSON's entry dump names only its three direct imports. The `Parse →
  Json` and `Print → Json` edges and the deduplicated transitive node set are not observable.
- **Smallest tracer bullet**: reuse `examples/json`'s existing diamond; add no new language program.
- **Positive evidence**: exact four-node/five-edge facts from the resolver, plus the existing declaration,
  reference, law, import, and use facts unchanged.
- **Negative or recovery evidence**: single-file output is one entry/zero edges; no absolute path appears;
  existing cycle/missing/private resolution failures remain unchanged.
- **Broader convergence gate**: query schema/golden tests, full examples/modules batteries, `just fitness`,
  and `just verify`.
- **Assumptions / exclusions**: facts describe logical dependency topology, not hashes, cache hits, rebuild
  timing, source maps, persisted artifacts, or a separate-compilation ABI.

## Plan

1. [x] Re-audit the toolchain route and reject the unrelated general-handler-body expansion.
2. [x] Project module nodes/edges from the existing resolver walk without filesystem paths.
3. [x] Add single-file, diamond, bundled-origin, and failure-preservation query gates.
4. [x] Regenerate the versioned schema reference and derived facts.
5. [x] Run full convergence; publish the tracer-bullet increment.

## Status

- [x] Started 2026-07-18
- [ ] In flight: none; successor is measured reverse-dependency fanout
- [ ] Blockers: none
- [x] Completed 2026-07-18
- Focused evidence: `tools/test-query.sh` — **113 passed, 0 failed**; exact JSON diamond is four
  nodes/five edges, bundled `Io` retains `origin: bundled`, and exported topology is path-free.
- Full convergence: `just fitness` and `just verify` passed; verify includes 61/61 source and
  environment examples, 31/31 registered batteries, and 63/63 module-resolution checks.
- Retained boundary / successor: the schema intentionally carries no source path, content hash,
  cache hit, rebuild timing, or separate-compilation claim. Compute reverse-dependency fanout from
  these facts next; choose a hash/cache boundary only after that consumer exposes what it needs.
- Reopen / observe: hash-boundary design starts only after a concrete invalidation/fanout measurement;
  general computing handler clauses remain with Q27's answer-grade/resumption trigger

## Owner

- Agent / human: Codex
