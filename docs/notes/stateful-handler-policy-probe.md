<!-- note-status: active -->
<!-- describes: Bang/Core/IR.lean Bang/Core/Typing.lean Bang/Core/Semantics/Dispatch.lean Bang/Backend/AbstractMachine.lean Bang/Backend/EnvMachine.lean Bang/Frontend/TypeCheck.lean @ 5312ec0419dfc25fc38e1920f6e8dfc3cf298c8f -->
# Stateful handler policy probe — quotas expose the read-only parameter boundary

> **Outcome (2026-07-18):** option A was accepted as ADR-0114. Explicit `ClauseKey.updating`
> transitions now agree across the source semantics, CalcVM, EnvMachine, abstract Wasm, and the
> concrete WasmGC emitter. This note records the pre-decision probe; its deferral language is
> historical. Public syntax now ships as
> `update op(x) => (resumeValue, nextParam)`; `examples/stateful-quota/` is the two-call witness.

> Follow-up to ADR-0113 and the completed `PATH-semantic-contracts`. The host-allowlist consumer
> proved that immutable value policy already belongs in ordinary handler configuration. This probe
> asks the next concrete question: can the same unchanged plugin be mediated by a quota that
> decreases after each operation?

## Consumer

The target is intentionally smaller than a filesystem sandbox:

```text
effect Net { connect : Int -> Int }
initial policy: one permitted request
plugin: perform connect twice through the same Cap Net
observable result: first request admitted, second denied
```

The quota must be held by the handler, not supplied by the plugin. If the plugin supplies an
ordinal or threads the remaining count itself, it can forge the policy state and the handler is no
longer a complete mediation point.

## Public-surface probe

The smallest attempt puts one builtin state cell around a custom handler and updates it from the
custom clause:

```bang
effect Net { connect : Int -> Unit }
state 1 as quota in
handle net.connect(7)
with Net as net {
  connect(host) => quota.put(0)
}
```

`bang check --json` rejects it with the stable teaching diagnostic:

```text
B005: handle: clause 'connect' body must be a `ret`-shape value in v1
      (no effects before resuming)
```

This is not merely a parser or inference omission. It agrees with every semantic layer below.

## Trace of the wall

- `Bang/Core/IR.lean` defines `Handler.custom ℓ p clauses`; `p` is the carried parameter.
- `Bang/Core/Typing.lean`'s `HasClauses` admits only `Comp.ret w` under the operation argument and
  parameter binders. There is no clause effect row or updated-parameter result.
- `Bang/Core/Semantics/Dispatch.lean` reinstalls `.custom ℓ p clauses` with **the same `p`** before
  running the clause.
- `Bang/Backend/AbstractMachine.lean`'s `customUpdate` returns the clause body with the handler stack
  unchanged. Its correctness lemmas explicitly depend on the read-only payload.
- `Bang/Backend/EnvMachine.lean` evaluates a clause with the stored `p`, but leaves the custom store
  `κ` unchanged.
- `Bang/Frontend/TypeCheck.lean` mirrors the core restriction by requiring the resolved clause row
  to be empty and emitting `B005` otherwise.

Therefore a persistent quota cannot be added faithfully by loosening one frontend check. Doing so
would make the tested surface disagree with the source semantics and both executable machines.

## Decision fork

| option | shape | benefit | cost / risk |
|---|---|---|---|
| A. Handler-local parameter update | A clause produces a resume value and a next parameter; dispatch stores the next parameter before resuming | Direct model of quotas, counters, and revocation; policy stays hidden from the plugin | Changes core dispatch, `HasClauses`, frame/store correspondence, both machines, Wasm paths, and proofs; requires a K/C ADR and a precise result protocol |
| B. General effectful clauses | A clause may capture an outer `State`/audit capability and perform before resuming | Most general; policy can compose arbitrary effects | Crosses the answer-grade/resumption gate named by ADR-0092/0095, plus clause-environment closure semantics; substantially broader than the quota consumer |
| C. Explicit policy token in the operation/plugin | The plugin threads `(remaining, request)` values itself | Expressible with current pure computations | Reject: the plugin can forge state, the `Cap Net` contract changes, and handler complete mediation is lost |

## Recommendation

Choose **A, handler-local parameter update**, if stateful policy is worth entering the kernel-facing
arc now. It is narrower than general effectful clauses and preserves the successful ADR-0113 split:
the plugin keeps one stable `Cap Net` contract while the handler owns policy state.

Do not pick syntax before the semantic protocol is fixed. Two plausible spellings—an explicit
`next param` clause tail or a surface pair that elaborates to an internal result—have different
failure and typing behavior. The implementation should begin with a hand-built core quota witness,
derive the source step and machine transition, then choose surface sugar over that proven shape.

The ruling retained ordinary clauses' read-only behavior and added a separate explicit update key.
The `B005` fail-loud remains for effectful clause bodies; state transition itself uses the typed,
effect-free update envelope rather than loosening that gate.

## Historical operator fork

The options presented for the now-completed decision were:

1. Open a K/C path for option A (recommended), with a new ADR before semantic edits.
2. Deliberately broaden the target to option B and accept the resumption-grade/closure scope.
3. Defer stateful policy; ADR-0113's immutable runtime policies remain the shipped boundary.
