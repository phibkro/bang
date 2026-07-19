# PATH-slice-execution-boundary — classify body-slice execution without inventing an artifact

> Differentially execute resolved whole programs and entry-rooted body slices, retain the strict
> initializer counterexample, and turn it into the first measured requirement for a future linker.

## Seam

- **From checkpoint**: `PATH-canonical-body-effect-identity` published stable environment-relative
  body observations while keeping `linkReady=false`.
- **To checkpoint**: execution is classified across the complete example corpus, and one permanent
  counterexample proves that a body slice is not a standalone executable when strict module
  initialization is removed.
- **Contract preserved**: module-body schema and digests are unchanged; the internal differential
  measures the existing slicer and production engines without becoming public API or a DCE mode.

## Layer

- [ ] Kernel  [x] Compiler  [ ] Surface  [x] Meta (tests/docs)

## Actor journey / observable outcome

- **Actor / need**: a build-tool author needs to know which semantic obligations remain before
  treating stable export-body identity as input to a linker.
- **Public starting point**: `bang query dump <file.bang>` reports body identity with
  `linkReady=false`; `just test-slice-fidelity` reproduces the project evidence.
- **Terminal observation**: all 61 resolved examples agree whole-versus-slice at fuel 100000 on both
  oracle and env lanes, and the env result matches every committed `expected.txt`; the same gate
  classifies a strict unreachable divergent initializer as an exact asymmetry.
- **Adverse / recovery route**: a slice returning `1` while the whole program exhausts fuel is not
  normalized into a false green. The harness reports both engine outcomes and exits nonzero; the gate
  expects that red pole as the module-initialization boundary.
- **Downstream journey released**: census top-level initializers, then choose an inert-description
  module discipline or an ordered initializer contract before specifying import slots/linking.

## Feeds the constraint

- **Binding constraint now**: `foldLetDecls` makes top-level values a strict lexical chain, while
  `reachableValueSliceProg` intentionally removes unreachable value declarations; the retained
  `strict-initializer` fixture makes their semantic mismatch executable.
- **How this path feeds it**: separate corpus-relative positive evidence from the general
  counterexample and carry module initialization forward as an explicit link-contract input.

## Prospective systemic review

| concern | horizon + evidence | likelihood / impact / late cost | disposition now | reopen trigger |
|---|---|---|---|---|
| corpus agreement is overclaimed as a theorem | 61 examples agree; strict initializer refutes generality | realized / critical / high | **publish both poles and say corpus-relative at fixed fuel** | corpus or evaluator changes |
| body identity is mistaken for standalone execution | whole `outOfFuel`/env `stuck` versus slice `done:1` | realized / critical / high | **keep `linkReady=false`; require initialization contract** | a linker design begins |
| fixing the witness by retaining every value destroys useful slicing | every strict top-level let is observable in bounded semantics | high / high / medium | **do not change the identity projection; classify the boundary** | initializer census shows a smaller sound rule |
| measurement apparatus becomes accidental public API | resolver currently lives in the CLI leaf | medium / medium / high | **hide under `bang internal`; omit usage/reference and let the battery own it** | a third non-CLI resolver consumer appears |
| engine collapse hides disagreement | env maps several failures to `stuck` | medium / high / low | **oracle remains arbiter; report both lanes exactly** | env gains terminal subclasses |
| process-per-file makes the gate slow/flaky | initial 61-process sweep approached the runner ceiling | realized / medium / low | **batch subjects through one compiled process with ordered rows** | batch latency crosses the verify budget |
| another output or refusal class is silently skipped | resolver, lowering, oracle, env, and row count can all fail | medium / high / low | **aggregate nonzero and exact row/corpus accounting** | a new engine or host-only class enters the corpus |

## Baseline, falsifier, and evidence

- **Baseline / red observation**: the published `linkReady=false` had no execution evidence behind it;
  body slices were hashed but never run.
- **Pre-scope positive probe**: custom handlers, mutual recursion, result-only generics, trait
  recursion, factorial, resolved spreadsheet, Calc, and host-IO simulation agreed exactly.
- **Stop-condition falsifier**: an unreachable top-level initializer calls a divergent recursive
  function before `main=1`. Whole oracle is `outOfFuel`, whole env is `stuck`, while both sliced lanes
  return `done:1`. This is strict initialization, not the investigated `progUsesVar` fuel heuristic.
- **Smallest tracer bullet**: turn the temporary synthetic-entry probe into hidden resolver-aware
  lifecycle instrumentation, sweep the complete corpus, and permanently pin the falsifier.
- **Positive evidence**: **61/61** resolved examples agree whole-versus-slice at fuel 100000 on both
  measured engines; env also matches every expected output. Oracle observations are exact too:
  `nqueens=outOfFuel`, `policy-host-allowlist=stuck`, and `sched-seeded-lcg=stuck` name the three
  existing non-value lanes; the other 58 match `done:<expected>`. The prior selected-body fixture
  agrees at `41`, tying execution evidence to the published identity family.
- **Negative or recovery evidence**: exact asymmetric lowering categories are guarded, the strict
  initializer must exit 1 with all four outcomes, and a repeated handler measurement is byte-identical.
- **Broader convergence gate**: `tools/test-slice-fidelity.sh` passes **64/64** as a default battery;
  focused query evidence passes **268/268**; generated views, fitness, full `just verify`, and the
  persistent-advisor skeptical review all pass.
- **Assumptions / exclusions**: fixed-fuel corpus measurement is not contextual equivalence. The
  synthetic entry adds one strict let step while pruning may remove several; a subject exactly on a
  fuel boundary can therefore classify an apparatus-cost asymmetry and must be diagnosed rather than
  assumed to expose semantic reachability. No function-valued export testing, artifact, import slot,
  label relocation, initializer order, DCE optimization, store, reuse, skipped work, digest theorem,
  cache safety, or link readiness is claimed.

## Plan

1. [x] Execute a diverse pre-scope kill shot through the production slicer.
2. [x] Stop on and minimize the strict-initializer counterexample.
3. [x] Implement hidden resolver-aware classification and batch corpus execution.
4. [x] Gate 61 positive subjects, identity tie-back, determinism, adverse classes, and retained red.
5. [x] Update the live map/Q34, run full convergence, and close skeptical advisor review.
6. [x] Publish the converged measurement and scope the top-level initializer census.

## Status

- [x] Started 2026-07-18
- [ ] In flight: none; successor is the checked-row top-level initializer census
- [ ] Blockers: none
- [x] Completed 2026-07-18
- Focused evidence: `tools/test-slice-fidelity.sh` passes **64/64**; `tools/test-query.sh` passes
  **268/268**; `just autoquality` passes.
- Convergence evidence: `CHANGELOG_STABLE_REF=a4c5cea1 just fitness` and
  `CHANGELOG_STABLE_REF=a4c5cea1 just verify` pass; the latter builds **1452 jobs**, passes all
  **32/32** batteries and both **61-example** engine journeys, and matches live proof facts. The
  persistent Fable 5 skeptical audit found no publication blocker after independently checking the
  apparatus accounting, hidden CLI boundary, exact non-value outcomes, and fuel-overhead limitation.
- Published baseline: `132a31ef` on `origin/codex/slice-execution-fidelity`.
- Retained failed gates / successors: strict initializer asymmetry → top-level initializer census →
  initialization-contract fork.
- Reopen / observe: `linkReady` stays false until initialization, runtime labels, import slots, and
  independently validated linking are jointly answered.

## Owner

- Agent / human: Codex, with persistent Fable 5 advisor in Herdr `lang-bang`
