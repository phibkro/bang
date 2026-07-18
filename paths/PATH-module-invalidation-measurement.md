# PATH-module-invalidation-measurement — consume the module DAG before designing its cache

> Turn `bang query dump`'s resolver facts into an exact reverse-dependency measurement over an
> existing multi-module project, without claiming that structural module counts are compile time.

## Seam

- **From checkpoint**: `PATH-queryable-module-graph` made the resolver's path-free DAG observable.
- **To checkpoint**: one reusable dump consumer measures the affected module set for every possible
  single-module change in `examples/calc` and distinguishes structural work from latency/cache claims.
- **Contract preserved**: this is a derived query over the public fact base, not another resolver,
  scheduler, hash implementation, persisted cache, or compiler-internal graph.

## Layer

- [ ] Kernel  [ ] Compiler  [ ] Surface language  [x] Meta (tool consumer/tests/docs)

## Actor journey / observable outcome

- **Actor / need**: a build-tool author wants to estimate which modules a dependency-aware rebuild
  could avoid touching before choosing storage, hashing, or scheduling machinery.
- **Public starting point**: `bang query dump examples/calc/main.bang`.
- **Terminal observation**: piping the dump through `tools/module-impact.py` reports six modules,
  exact affected sets, 36 whole-program module/change pairs, 15 dependency pairs, and 21 avoided
  pairs under the explicitly equal-weighted structural model.
- **Adverse / recovery route**: single-file input reports 1/1/0; malformed, dangling, duplicate, or
  cyclic topology fails loudly; unknown additive fields remain tolerated by schema-v1 consumers.
- **Downstream journey released**: the hash-boundary review can distinguish topology savings from
  the separate result-hash firewall needed to suppress semantically unchanged downstream rebuilds.

## Feeds the constraint

- **Binding constraint now**: topology is observable but no consumer demonstrates how it affects work.
- **How this path feeds it**: compute reverse transitive closure from `moduleDeps`, with the dump's
  `modules` table as the complete, deterministic identity set.

## Prospective systemic review

| concern | horizon + evidence | likelihood / impact / late cost | disposition now | reopen trigger |
|---|---|---|---|---|
| structural pairs are reported as speedup | first measurement; module costs differ | high / high / medium | **name and document pairs, not time** | representative compile timings exist |
| consumer silently accepts corrupt topology | first external graph consumer | medium / high / low | **validate** nodes, endpoints, duplicates, and acyclicity | schema supplies stronger invariants |
| additive dump growth breaks the script | current public schema contract | medium / medium / medium | **ignore unknown fields**, require only used v1 fields | schemaVersion changes |
| module names become cache identities | store-design successor; names change independently of core | high / high / high | **reject** cache/identity claims here | content-addressed store work starts |
| graph closure is recomputed inefficiently at scale | current maximum tracer has six nodes | low / low / low | **accept simple linear traversals**, measure before indexing | representative DAG crosses a named latency/size threshold |
| equal-weighted change scenarios mislead priorities | current structural comparison | medium / medium / low | **publish every affected set and assumptions**, not one opaque ratio | real edit frequency/cost data becomes available |

## Baseline, falsifier, and evidence

- **Baseline / red observation**: the dump exposes edges, but a tool author must still write and
  validate reverse-closure logic before answering “what rebuilds if `Ast` changes?”
- **Smallest tracer bullet**: reuse `examples/calc`'s six-node shared-`Ast` graph; add no language code.
- **Positive evidence**: exact per-module affected rows and the 15-of-36 structural-pair measurement.
- **Negative or recovery evidence**: single-entry 1/1/0, forward-compatible unknown-field tolerance,
  and explicit dangling/cycle refusals.
- **Broader convergence gate**: focused query battery, tool-index derivation, `just fitness`, and
  `just verify`.
- **Assumptions / exclusions**: every hypothetical module change and rebuild has weight one. No claim
  covers change frequency, parse/typecheck/codegen cost, result hashes, cache hits, persistence,
  concurrency, separate compilation, or wall-clock improvement.

## Plan

1. [x] Audit Q34/ADR-0076 and select `examples/calc` as the existing shared-dependency tracer.
2. [x] Implement one forward-compatible dump consumer with fail-loud graph validation.
3. [x] Gate exact Calc, JSON, single-file, and malformed-graph outcomes.
4. [x] Record what the measurement decides—and what remains deferred—at the hash boundary.
5. [x] Run full convergence and publish the tracer-bullet increment.

## Status

- [x] Started 2026-07-18
- [ ] In flight: none; successor is the canonical elaborated-core fingerprint probe
- [ ] Blockers: none
- [x] Completed 2026-07-18
- Focused evidence: `tools/test-query.sh` — **126 passed, 0 failed**; Calc measures 15/36
  dependency/whole-program pairs (21 structurally avoided), JSON 9/16, and single-file 1/1.
- Convergence evidence: `just fitness` and `just verify` pass; the latter includes **31/31**
  batteries plus the live architecture/proof, documentation-model, and grammar checks.
- Decision: retain the resolver DAG as coarse invalidation topology; probe a canonical elaborated-core
  fingerprint next to supply the result-hash firewall for semantically unchanged upstream edits.
- Reopen / observe: build a hash/store only after this measurement is interpreted alongside Q34's
  already-pinned elaborated-core direction and a concrete result-hash/firewall consumer.

## Owner

- Agent / human: Codex
