# 0114 — stateful custom clauses use explicit update keys

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: Let an individual custom-handler clause opt into parameter transition. A plain
  clause keeps returning its operation result and reinstalls the existing parameter. An updating
  clause returns an explicit `(resumeValue, nextParam)` envelope; dispatch installs `nextParam`
  before resuming. Represent the distinction in the core clause key rather than guessing from the
  returned value's shape.
- **Depends-on**: [0025](0025-resumptive-state-handler.md) (deep state transition),
  [0087](0087-custom-clauses-finite-rep-dissolves-capsh-wall.md) (finite custom clauses),
  [0092](0092-stage3-typing-user-effects-program-derived-effsig.md) (ret-shaped custom clauses),
  [0113](0113-value-level-resource-policy-is-handler-configuration.md) (runtime policy consumer)
- **Date**: 2026-07-18
- **Deciders**: operator + Codex, choosing option A from
  `docs/notes/stateful-handler-policy-probe.md`
- **Ties**: `paths/PATH-stateful-handler-policy.md`, `Bang/Witness/D5ParamHandlerWitness.lean`

## Context

ADR-0113 showed that a read-only handler parameter is enough for runtime-selected allowlists. The
next consumer is a one-request quota: one unchanged plugin performs the same operation twice; the
handler admits the first request and denies the second without exposing quota state to the plugin.

The existing custom arm cannot express that transition. It substitutes the current `param` into a
clause and reinstalls the handler with that same value. General effectful clauses would solve much
more than the consumer asks for and would reopen the answer-grade and clause-environment problems
deliberately deferred by ADR-0092.

The earlier D5 design note proposed recognizing any returned pair as `(resumeValue, nextParam)` and
falling back to read-only behavior for non-pairs. That is not type-safe: an operation may
legitimately have a product result, so its ordinary result could be mistaken for protocol metadata.
The update intent must be represented separately from the result value.

## Decision

Extend the finite custom-clause key with an explicit per-operation mode:

```text
ClauseKey.plain    op
ClauseKey.updating op
```

Both keys name the same declared effect operation for lookup and interface typing. They differ only
in the clause-result protocol:

- `plain op` has the existing behavior. Its clause returns the operation result, and dispatch
  reinstalls `.custom label param clauses` unchanged.
- `updating op` returns `pair resumeValue nextParam`. Dispatch reinstalls
  `.custom label nextParam clauses`, then resumes the captured continuation with `resumeValue`.

The mode is per clause, not per handler. A handler may therefore expose read-only observations and
state-changing operations over one private parameter, matching the familiar `get`/`put` split
without adding another handler constructor or primitive.

The first kernel slice remains ret-shaped. An updating clause is structurally
`ret (pair resumeValue nextParam)`, so dispatch can perform the transition atomically without
evaluating an effectful clause or introducing a first-class continuation. A malformed updating
clause is stuck/fail-loud in untyped core terms; `HasClauses` excludes it from typed terms.

## Why explicit keys

1. Product-valued operations remain ordinary values. No runtime value shape silently changes the
   meaning of a plain clause.
2. Update intent is visible to lowering, typing, semantics, machines, proofs, and tooling through
   one core datum. There is no reserved operation-name convention or frontend-only flag.
3. Existing clauses lower as `plain`; the shipped read-only behavior is preserved by default.
4. The transition is the custom analogue of the existing deep `state` reinstall: update the
   handler-owned cell before the captured continuation resumes.

## Consequences

- `Handler.custom` remains one of the existing handler constructors, but its finite association
  list is keyed by `ClauseKey` rather than raw `OpId`.
- Operation coverage and dispatch compare `ClauseKey.op`; duplicate checking must reject two keys
  for the same operation even if their modes differ.
- Core clause typing gains an updating case whose resume component has the operation result type
  and whose next-parameter component has the handler parameter type.
- The source semantics, CalcVM, environment machine, and Wasm execution must agree on installing
  the next parameter before resumption. The surface spelling ships only after those routes agree.
- The shipped spelling is `update op(x) => (resumeValue, nextParam)`. The existing
  `op(x) => body` stays plain, including for an operation literally named `update`.
- This decision does not admit arbitrary effects before resume. General computed/effectful update
  bodies remain a separate continuation/interception design problem.

## Rejected

- **Infer updates from any returned pair** — rejected because it collides with legitimate product
  operation results.
- **Reserve a magic operation-name prefix** — rejected because semantic mode would be encoded in a
  string namespace rather than represented in the IR.
- **Make the whole handler stateful** — rejected because observation and mutation are naturally
  per-operation properties.
- **Use an outer builtin `State` from the clause** — rejected for this path: it broadens clauses to
  arbitrary effects and exposes the ADR-0092 answer-grade wall.
- **Let the plugin thread a quota token** — rejected because the plugin could forge policy state;
  complete mediation requires the handler to own it.

## Confirmation

The first witness installs a custom handler with parameter `1` and one updating operation whose
clause returns `(param, 0)`. Two calls through the same capability yield `1` then `0`, combined as
`10`. This is established through `Source.eval`, CalcVM, EnvMachine, the abstract Wasm machine, and
a real Wasmtime run of the concrete WasmGC emitter. The same witness now ships at the public surface
as `examples/stateful-quota/`; parser, formatter, checker, lowering, all engines, and concrete
emission retain the explicit update mode. The public `bang build` battery also parses and validates
the resulting `.wasm`, then observes `10` on Wasmtime.

## Revisit if

The consumer needs arithmetic or effects inside the update computation itself. That requires an
explicit return-interception frame (or a broader continuation design), not weakening the envelope
or reviving pair-shape inference.
