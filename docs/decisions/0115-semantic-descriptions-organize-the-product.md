# 0115 — semantic descriptions organize the product

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: Describe bang as a language of semantic descriptions. Computation, effects, and
  resource obligations are stated independently of realization; handlers and compiler calculation
  choose progressively concrete executions while preserving those descriptions. “Paradigm and
  runtime are values” remains an important consequence, not the top-level identity.
- **Depends-on**: [0016](0016-two-hop-architecture-calcvm-and-wasmfx.md) (calculated machine),
  [0037](0037-abstract-correctness-implementation-performance.md) (generative constraints),
  [0111](0111-effect-contracts-static-handler-realizations.md) (contract/realization seam)
- **Date**: 2026-07-18
- **Deciders**: operator + Codex
- **Ties**: `paths/PATH-resource-contract-tracer.md`, `docs/PRD.md`

## Context

The previous product sentence — “paradigm and runtime are values, not language features” — correctly
describes handlers, but it is narrower than the architecture now implemented. Named effect contracts
and laws survive multiple handler realizations; rows and pledges state obligations without selecting
runtime behavior; the calculated machine derives execution from reference semantics; differentially
tested Wasm is another explicitly bounded realization.

The resource side exposes the same shape but is not yet public: QTT grades already constrain kernel
terms, while the surface defaults them to `ω`. A framing centered only on runtime handlers would make
surfaced quantities, erasure, and future ownership transfer look like unrelated additions instead of
other descriptions consumed by realization.

## Decision

Use this organizing pipeline in product and project documentation:

```text
description → semantic obligations → selected/calculated realization → evidence
```

- A description states observable computation plus independent effect and resource axes.
- Semantic obligations include types, rows, quantities, laws, and explicit ceilings.
- A realization may be a selected handler, a calculated abstract machine, or a concrete backend.
- Evidence names its strength and boundary: machine-checked, property-tested, differential, or open.

This is product vocabulary, not a sixth kernel primitive or a universal specification language.
Existing thunks, rows, grades, handlers, laws, and compiler calculations remain the mechanisms.

## Consequences

- README, PRD, roadmaps, and contributor orientation lead with semantic descriptions.
- “Paradigm and runtime are values” remains a concise derived claim and concrete demonstration.
- New language work should identify the description, obligation, realization, and evidence it adds.
- The next resource tracer must make one quantity visible and observable before the project claims a
  general resource or ownership system.
- Machine-readable contract views should separate semantic compatibility from backend/ABI evidence;
  a package registry remains outside the current slice.

## Rejected

- **Keep the handler-only sentence as the identity** — rejected because it under-explains grades,
  laws, compiler calculation, and evidence boundaries.
- **Lead with formal verification** — rejected because verification is evidence for the language
  design, not the semantic description users write.
- **Build a universal semantic-package platform now** — rejected because one complete in-repository
  contract card is the consumer needed to discover the minimum schema.
- **Treat realization independence as backend abstraction only** — rejected because handler policy,
  evaluation strategy, resource representation, and compilation are all realization choices.
