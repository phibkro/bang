# PATH-reactive-recomputation-measurement — measure before choosing a cache

> Make whole-DAG pull recomputation observable on a representative spreadsheet workload without
> introducing memoization, invalidation, a scheduler, compiler instrumentation, or a new runtime graph.

## Seam

- **From checkpoint**: `PATH-reactive-dependency-observation` exposes stable formula identities and
  their static declaration-reference DAG through the existing compiler fact base.
- **To checkpoint**: a 100-line-item workload reports both its value and the exact number of formula
  calls on the first observation and after an input update, identically across supported engines.
- **Contract preserved**: formulas remain ordinary functions, State remains the input substrate, and
  each force remains an unmemoized pull observation.

## Layer

- [ ] Kernel  [ ] Compiler  [x] Surface  [x] Meta (tests/docs)

## Actor journey / observable outcome

- **Actor / need**: a spreadsheet implementer needs evidence that repeated evaluation is materially
  present before designing a cache contract.
- **Public starting point**: `bang run examples/reactive-recomputation/main.bang` plus `bang query
  dump examples/reactive-recomputation/Workload.bang`.
- **Terminal observation**: 104 stable formula declarations and 202 static dependency edges produce
  401 formula calls per force; changing price changes the value but not the full-recomputation count.
- **Adverse / recovery route**: treating static edge count as runtime cost is rejected. The executable
  result carries a call count, so query facts and runtime measurement remain distinct evidence.
- **Downstream journey released**: a cache decision grounded in a measured redundancy ratio rather
  than an assumed performance problem.

## Feeds the constraint

- **Binding constraint now**: the prior path found a visible diamond but no runtime count; caching was
  explicitly gated on a representative workload and trace.
- **How this path feeds it**: use an invoice-shaped 100-line fan-out/fan-in DAG with a shared derived
  `unitAmount` formula and in-band counters whose values are observed by every engine. This
  establishes the baseline cost without changing it.

## Prospective systemic review

| concern | horizon + evidence | likelihood / impact / late cost | disposition now | reopen trigger |
|---|---|---|---|---|
| profiler changes evaluation behavior | immediate; counts travel in returned pairs | medium / high / low | **implement** a separate profiled workload and preserve ordinary spreadsheet tracer | measured and unprofiled values diverge |
| compiler optimization erases the measurement | any compiled route; counts are terminal output | low / high / low | **implement** exact source/env/compiled/Wasm output gates | an engine disagrees |
| static edges are mislabeled execution counts | immediate; shared inputs execute repeatedly | high / medium / low | **reject** inference; gate both facts and runtime count separately | dynamic trace facility exists |
| 100-line invoice is not representative of future sheets | next workload class | medium / medium / medium | **preserve** workload shape and bound claims to fan-out/fan-in pull evaluation | organic workload has materially different topology/cost |
| a cache is built before invalidation semantics are known | successor slice | medium / high / high | **defer** implementation; decide only after measured ratio and semantic review | this path closes with material redundancy |
| generated-looking source becomes unmaintainable | first edit | high / low / low | **implement** deterministic generator, freshness check, and structural query checks | workload semantics outgrow the generator |

## Baseline, falsifier, and evidence

- **Baseline / red observation**: the five-node tracer proves freshness but cannot quantify how much of
  the reachable graph executes on each observation.
- **Smallest representative tracer bullet**: two shared inputs, 100 line formulas, and one total.
- **Positive evidence**: values are 7050 then 7450; each force reports 401 calls. Query facts report
  104 declarations and 202 dependency edges, including 100 references to the shared derived formula.
- **Negative or recovery evidence**: the second force occurs after a State update yet still reports
  401. A missing call, retained cached result, malformed graph, or route drift changes a gated fact.
- **Broader convergence gate**: focused check/run/query, example corpus, environment machine, compiled
  dogfood, concrete build/Wasm differentials, `just fitness`, and `just verify`.
- **Assumptions / exclusions**: the counter measures semantic formula invocations in this workload,
  not wall-clock time, allocation, compiler internals, arbitrary dynamic dependencies, or user latency.

## Plan

1. [x] Freeze the representative DAG, observable counter, and falsifier.
2. [x] Generate the 100-line workload deterministically without changing the existing small tracer.
3. [x] Gate declaration/edge shape and exact first/updated execution counts.
4. [x] Converge every standing execution route and record the measured redundancy ratio.
5. [x] Close with a cache/no-cache decision and the smallest justified successor.

## Status

- [x] Started 2026-07-18
- [ ] In flight: none; successor begins with within-observation reuse semantics
- [ ] Blockers: none
- [x] Completed 2026-07-18
- Retained failed gates / successors: first prototype produced 301 calls but repeated only trivial
  input-identity declarations → add one genuinely derived shared formula before treating redundancy as
  cache evidence. Final query battery: 103/103; source/oracle: 59/59; environment: 59/59; compiled
  dogfood: 8/8; concrete build/Wasm: 18/18.
- Full convergence gate: `CHANGELOG_STABLE_REF=codex/reactive-dependency-observation just verify`
  passed.
- Reopen / observe: topology drift, engine disagreement, or an organic workload that invalidates the
  invoice-shaped model

## Owner

- Agent / human: Codex

## Notes

The measured invocation-to-declaration ratio is 401/104 (about 3.86), but it is not a wall-clock
speedup claim. The decision is **yes to a cache-contract successor, no to cache implementation yet**.
Start with reuse inside one force, where the sampled inputs are fixed and no cross-observation
invalidation is needed. Cross-observation retention, argument-keyed memoization, compiler CSE, and a
runtime dependency graph remain separate alternatives that the successor must compare explicitly.
