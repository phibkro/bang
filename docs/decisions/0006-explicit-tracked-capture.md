# ADR-0006 · Capture is explicit and tracked; no implicit lexical closure

- **Status:** Accepted
- **Date:** 2026-05-31
- **Related:** 0003 (this unlocks what owning the runtime enables), spec `bang-lang-description-value.md`

## Context

A bare thunk currently closes implicitly over its lexical environment → the closure-serialization problem, hidden coupling, and surprising memory retention (a thunk keeps its whole captured frame alive). There are already **two** explicit channels into a computation — direct arguments and effects — both visible and tracked. Implicit lexical capture is a hidden **third** channel that defeats the visibility the effect system is built to provide.

## Decision

**No implicit lexical capture.** Capture is **explicit and tracked**; serializability is a tracked property of a thunk. **Module-level immutable bindings are exempt** (content-addressed, cheap to ship).

## Rationale

- Makes every thunk **honestly serializable** → distribution ("move code to data") and durable/resumable execution fall out — exactly the capabilities owning the runtime (0003) is meant to unlock.
- A function's **complete input surface = parameters + effect row**. Nothing arrives invisibly. Maximal honesty about data flow.
- Predictable memory: a thunk retains only what it was given.
- **Simpler calculated closures:** defunctionalized closures with explicit captures are cleaner to derive a machine for (helps K2/K4).
- Same direction as 0003/0005: make information flow explicit; the powerful/expensive capability is opt-in.

## Rejected alternatives

| option | why not |
|--------|---------|
| **full scope isolation** (a scope sees nothing of its parent) | too austere — kills currying, helper closures, ordinary `map`-with-outer-var idioms. Right thing to *measure against*, wrong thing to ship |
| keep **implicit capture** (status quo) | the hidden third channel; defeats the whole effect/type-visibility project |
| require **all captures serializable**, always | too strict; capture should be allowed but its serializability consequences visible in the type |

## Consequences

- **Open forks** (track these, don't silently resolve):
  - capture-list **syntax** (C++ `[x,&y]` / Rust `move` / Swift `[weak]`-style) — TBD spelling.
  - serializability **mechanism** — tracked effect vs type-class constraint vs content-address-derived. Current lean: **content-address-derived**.
- A thunk capturing non-serializable things is itself non-serializable, surfaced in its type.
- Reinforces reversibility later: a reversible op cannot silently destroy a captured value; it must record it.

## Revisit if

Explicit capture lists prove too noisy for daily use → consider **inferring** capture sets (still tracked in the type, just not hand-written), rather than reverting to implicit capture.
