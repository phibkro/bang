# PATH-distributed-lattice-store — lattice core plus consumer-pulled wall

> Bank the generic join-only core and the first real BANG consumer's refusal without claiming an
> end-to-end CALM tracer that the current surface cannot express.

## Seam

- **From checkpoint**: R2 replicated-KV examples with hand-written LWW folds and no proved generic
  lattice-store law
- **To checkpoint**: one axiom-clean generic Lean core, one retained max-join surface refusal, and
  one independent absent-CAS refusal
- **Contract preserved**: effect rows remain sets; the kernel gains no primitive or label; the
  existing ADR-0114 diagnostic remains the observable boundary

## Layer

- [ ] Kernel  [ ] Compiler  [x] Surface  [x] Meta (docs/process)

## Actor journey / observable outcome

- **Actor / need**: a BANG library author tries to instantiate the generic join-only design as an
  ordinary parameter-updating `Int/max` handler.
- **Public starting point**: `examples/lattice-store/computed-update-wall.bang` and
  `just test-lattice-store`.
- **Terminal observation**: checking the genuine max-join update fails at ADR-0114's value-shape
  gate with `must return a value pair`; the retained generic diagnostic is the evidence.
- **Adverse / recovery route**: `cas-excluded.bang` uses a direct accepted value pair around an absent
  `cas`, so checking independently fails with `unknown operation 'cas'`.
- **Downstream journey released**: one shared frontend increment can admit pure computed components
  in an updating pair and validate both the allocator transition and this max-join handler.

## Feeds the constraint

- **Binding constraint now**: ADR-0114 admits only ret-shaped outer pairs whose components are
  already syntactic values. A real join computes its next parameter from `param` and the payload.
- **How this path feeds it**: retain the smallest rejected consumer and its exact diagnostic while
  landing the generic core and scoped algebraic laws that establish why the consumer remains useful.

## Prospective systemic review

| concern | horizon + evidence | likelihood / impact / late cost | disposition now | reopen trigger |
|---|---|---|---|---|
| pure computed update components | both allocator S0 and this max-join handler hit the same ADR-0114 shape gate | high likelihood, high consumer value, moderate proof cost | **one shared follow-on owner**, not a lattice-local workaround | the shared increment carries both consumers in its acceptance matrix |
| effectful updating clauses / finalizers | explicitly beyond the pure value computation needed here | uncertain, high semantic and proof cost | exclude | a separate consumer requires effects or cleanup during transition |
| full D5 proof port / grade-polymorphism | no current consumer requires either generalization | high late cost | exclude | an accepted architecture path demonstrates the need |
| general CALM transfer | the survey records the Datalog-to-CBPV wall | high impact and proof cost | defer; keep the conjecture untouched | formal network semantics and fragment interpretation exist |
| `coord` row label and CAS semantics | only an absent-operation guard exists | premature semantic cost | preserve the door; do not add either | a runnable coordinating consumer needs classification |
| network loss/liveness | the proved law assumes a symmetric exchange | distinct model cost | exclude explicitly | delivery/fairness becomes the proof subject |

## Baseline, falsifier, and evidence

- **Baseline / red observation**: the R2 story had no generic lattice-store core or proved scoped
  convergence law; the first honest BANG handler is rejected before execution.
- **Smallest banked increment**: `JoinUpdate.join`, `LatticeStore.apply/merge`, their focused laws,
  the rejected max-join consumer, and the independently rejected CAS call.
- **Positive evidence**: Lean proves inflation, pairwise reorder, duplicate idempotence, and equality
  after one symmetric exchange.
- **Negative evidence**: the battery pins the generic ADR-0114 computed-pair diagnostic and the
  separate absent-CAS diagnostic.
- **Broader gates**: `just check Bang/Distribution/LatticeStore.lean`,
  `just test-lattice-store`, derived-document checks, `just fitness`, and `just verify`.
- **Assumptions / exclusions**: no runnable BANG lattice store yet; no coordination-free execution
  claim; no arbitrary merge certification, general CALM theorem, consensus/CAS implementation,
  `coord` label, kernel primitive, effectful clause, finalizer, D5 proof port, grade-polymorphism, or
  consumer-specific operation.

## Plan

1. [x] Add the generic join-only core and scoped laws without changing the proof spine.
2. [x] Retain the max-join consumer at the real frontend wall and isolate the CAS refusal.
3. [x] Run the executable refusal battery and derived-document hygiene, then close the path.

## Status

- [x] Started 2026-07-19
- [ ] In flight.
- [ ] Blockers: none.
- [x] Completed 2026-07-19
- Retained failed gates / successors: root's authoritative focused Lean gate and clean-build
  `just test-lattice-store` pass. Lane-owned architecture, generated-doc, reference-adjacent, and
  hygiene checks pass. This sandbox cannot stage or commit because the linked worktree index is
  read-only, so full `just fitness` stops when index-aware checks see the new files as untracked;
  after staging, the inherited virtual landing's 28-product-commit changelog policy is the remaining
  known repository-level failure. The expected max-join refusal is product evidence, not a gate
  failure; its successor is the shared pure-computed-update-components increment described above.
- Reopen / observe: do not reopen this branch to implement that frontend feature; consume the shared
  increment later and add a runnable journey then.

## Owner

- Agent / human: Codex (GPT-5.6 Sol lane)

## Notes

Kill shot: the generic Lean update language makes every accepted update a join and proves its scoped
laws, while the first concrete max-join handler deterministically exposes the exact shared frontend
wall. CAS remains independently absent. This is core plus consumer-pulled wall evidence, not a
completed end-to-end CALM tracer.
