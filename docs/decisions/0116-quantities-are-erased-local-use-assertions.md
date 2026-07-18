# 0116 — quantities are erased local use assertions

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: Surface the first value quantity as `use [q] x in body`. It checks the free use of an
  existing binding at `q = 0` or `q = 1`, treats `omega` as the unrestricted compatible ceiling,
  then erases before kernel lowering. Rows remain sets. Concrete grade-zero evidence omits the
  unused bound value's environment cell while still evaluating its `let` RHS.
- **Depends-on**: [0019](0019-typing-context-split-gradevec-and-types.md) (kernel grades),
  [0020](0020-de-bruijn-representation.md) (positional usage),
  [0066](0066-surface-type-system.md) (`omega`-default surface),
  [0112](0112-row-attenuation-as-erased-pledge.md) (erased checked obligation precedent)
- **Date**: 2026-07-18
- **Deciders**: operator + Codex, consumer-driven by the one-shot permit fixtures
- **Ties**: `paths/PATH-resource-contract-tracer.md`, `docs/notes/questions/Q27-surfacing-the-grade-axis.md`

## Context

The kernel already assigns a QTT grade to every variable occurrence, but the public checker defaults
returners and arrows to `omega` and carries only types in its named context. Surfacing grades on every
arrow would force a broad type-syntax and inference redesign before a program demanded it. The first
consumer asks for something narrower: assert that one existing capability is consumed exactly once,
and reject duplicate or forgotten use.

The grade-zero backend claim also needs care. `let x = M in N` evaluates `M` even when `x` has grade
zero; the kernel's `q_or_1` floor is load-bearing for that behavior. Grade zero licenses omission of
the result binding's representation and reads, not deletion of arbitrary effects in `M`.

## Decision

Add the checked, runtime-erased expression:

```bang
use [0] ghost in body
use [1] permit in body
use [omega] shared in body
```

- `x` must name a binding already in scope; the construct does not bind a new value.
- `[0]` requires no free use of `x` in `body`.
- `[1]` requires one use on every reachable alternative path. Sequential uses add and saturate at
  `omega`; alternative branches must agree before their common usage is combined.
- `[omega]` is unrestricted and preserves the existing surface default. It is explicit documentation,
  not an exact “at least twice” assertion.
- Lexical shadowing is respected. A nested binder named `x` does not count toward the outer assertion.
- The node erases to `body` during lowering, like `pledge`; the kernel term and five primitives do
  not change.

The concrete emitter may eliminate an unused `let` result cell by evaluating the RHS, dropping its
result, removing the dead de Bruijn binder from the continuation, and emitting the continuation under
the original environment. The optimization is valid for any manifestly unused binder; `use [0]`
makes that property an explicit checked source obligation.

## Why an assertion block first

It composes with handler-generated capabilities without changing every binder grammar, lets the
consumer name the exact region whose resource policy matters, and mirrors `pledge`'s successful
“checked description, erased realization” shape. A later ownership system may infer or attach grades
directly to binders and arrows; this syntax remains useful as a local assertion and migration target.

## Rejected

- **Grade effect rows** — rejected: rows remain idempotent sets (ADR-0001); quantities are a separate
  value axis.
- **Delete a grade-zero `let` RHS** — rejected because it changes observable effects and contradicts
  the kernel's `q_or_1` evaluation floor.
- **Surface annotated arrows first** — rejected for this slice: it broadens type syntax, inference,
  polymorphism, and every declaration form before the permit consumer needs them.
- **Make a special linear-capability handler form** — rejected because quantities apply to all values,
  not only capabilities, and would couple the value and effect axes.
- **Use the answer-type capability-occurrence check** — rejected because the escaped-thunk witness
  already refuted that enforcement mechanism; lifetime/capture is a separate axis.

## Revisit if

Two consumers require quantity-polymorphic functions or exported resource contracts in signatures.
That is the trigger to add binder/arrow quantity syntax and inference rather than extending this local
assertion with type-level behavior it does not carry.
