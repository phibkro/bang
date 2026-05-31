# ADR-0003 · Own the runtime; don't transpile to a borrowed effect runtime

- **Status:** Accepted
- **Date:** 2026-05-31
- **Related:** 0004 (how we own it), 0006 (no-implicit-capture unlocks what owning enables)

## Context

Effect TS was the planned transpile target. Its appeal was a free effects-and-handlers runtime, the JS ecosystem, and gradual adoption ("BANG is sugar for Effect TS"). Against that: TypeScript's substrate is unsound, Effect is a fast-churning dependency (v3/v4), and you don't own it. The stated goal is correctness-by-construction and independence.

## Decision

**Own the runtime.** Do not transpile to a borrowed effect runtime as the canonical path.

## Rationale

- Correctness-by-construction: the verified reference can *be* the implementation, instead of a transpiler validated against an unsound, unformalized target.
- Ecosystem independence: no dependence on a third-party runtime's release cadence or semantics.
- Performance is second-class (invariant 7), so even a naive owned runtime is an adequate shipping runtime.

## Rejected alternatives

| option | why not |
|--------|---------|
| stay on **Effect TS** | unsound TS substrate; churning dependency; can't verify a transpiler against an unformalized target |
| **OCaml 5** (borrow its native effect handlers) | strong like-for-like, sound, fast — but still *borrowing*, and loses the browser. Held as the pragmatic bridge if shipping pressure demands it |
| JVM (Loom) / .NET / BEAM | no advantage over OCaml 5 (Loom), or a hard semantic mismatch for lazy thunks (BEAM) |

## Consequences

- (−) You now maintain a runtime: handler dispatch, the STM journal, a scheduler. The kernel/library split (design doc) defines exactly what must be native.
- (−) You give up Effect TS's "no runtime to ship," its npm ecosystem, and transparent interop.
- (+) Owned, correct-by-construction, ecosystem-independent. The capabilities this enables (distribution, durable execution) are unlocked by ADR-0006.

## Revisit if

Near-term shipping or **browser deployment** becomes a hard requirement before the owned runtime is ready → **OCaml 5** (borrow effects, stay sound/fast) or a Wasm path is the bridge, with the owned VM as the destination.
