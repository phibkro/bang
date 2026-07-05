# ADR-0070 · Surface named capabilities — `with H as h in e` + `h.op`, exposing the kernel cap the ambient forms already use

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: Named capabilities surface the cap VALUE the kernel already binds at every handler (ADR-0054/0055): `with state 1 as h in e` binds `h : Cap state` to the installed handler's cap, and `h.get` / `h.put(v)` perform on THAT cap. The ambient forms (`get`, `state s in e`) stay as sugar for the single-instance common case — they resolve an implicit sentinel cap. The win is MULTIPLE COEXISTING INSTANCES (two state cells) and capability-PASSING (`h` is a first-class value), neither expressible with the nearest-sentinel ambient form. Correction to the issue framing: both forms dispatch by IDENTITY (lexical) — bang has no dynamic/nearest-label dispatch (ADR-0052); "ambient" here means implicit-cap-resolution, NOT dynamic dispatch.
- **Resolves**: tracer bullet #3 (named vs ambient capabilities)
- **Depends-on**: 0054, 0055, 0052, 0068

- **Status:** Accepted (operator-ratified 2026-07-05)
- **Date:** 2026-07-05
- **Layer:** C (surface design — exposing an existing kernel capability, no kernel change)
- **Builds on:** ADR-0054 (`perform : Val→OpId→Val`, the cap-value operation form) · ADR-0055
  (`handle` binds a fresh-identity cap at de Bruijn 0) · ADR-0052 (dispatch is identity-keyed =
  lexical; nearest-label/dynamic REJECTED) · ADR-0068 (the typed elaboration path this rides).

## Context — the cap is already there, just unnamed

Every handler the surface lowers already binds a capability value: `state s in e` lowers to
`handle (state …) <e under #state>`, and ambient `get` performs on the sentinel binder `#state`
(the nearest enclosing state handler — `Bang/Frontend/Surface.lean`). So the machinery for named
capabilities EXISTS; the sentinel is just a reserved name the user can't write. #3 is: expose that
binder under a USER name and add `h.op` perform syntax.

The functional gap this closes — the ambient form resolves the NEAREST handler of a kind, so it can
reach only ONE state cell. Two independent cells, or passing a handler to a function, are
inexpressible. The kernel supports both (caps are first-class `vcap n ℓ` values, identity-keyed);
only the surface couldn't say it.

**Framing correction (load-bearing).** The issue cast ambient as "dynamic, Effect-TS-like" vs named
as "lexical, Koka/Effekt-like". In bang that dichotomy does not exist: ADR-0052 REJECTED
nearest-label/dynamic dispatch — every `perform` dispatches on the cap's generative IDENTITY, so
BOTH ambient and named are lexical. What actually differs: ambient resolves an IMPLICIT sentinel cap
(one per kind, nearest); named binds an EXPLICIT `Cap ℓ` value (many, first-class, passable). The
distinction the type carries is "is there a nameable/passable `Cap` value" — not the dispatch rule.

## Decision

1. **Named-handler binding** — `with <H> as <name> in <e>`, where `<H>` is a handler spec
   (`state <e0>` | `throws` | `atomically`). Installs the handler and binds `<name> : Cap ℓ` to its
   cap for `<e>`. `with` is the handler-installation keyword the glossary already uses ("installed
   with a `with` block").
2. **Method-perform** — `h.op` / `h.op(arg)` / `h.op(a, b)` performs `op` on the named cap `h`:
   `h.get`, `h.put(v)`, `h.raise(v)`, `h.new(v)`, `h.read(r)`, `h.write(r, v)`. The `.` is the only
   new punctuator; it means "perform on this capability", nothing else in v1 (no product field
   access — products destructure by `let (a,b)`).
3. **Ambient forms STAY as sugar** for the single-instance common case: `state s in e` ≡
   `with state s as #state in e` with `get`/`put` resolving `#state` implicitly. No deprecation —
   the ambient form is the ergonomic default; named is the opt-in for multiplicity/passing.
4. **`Cap ℓ` is first-class** (the kernel's `VTy.cap ℓ`): a named cap can be `let`-bound and passed
   to a function (`fun k => k.get`, `k : Cap state`) — capability-passing, the Effekt payoff. The
   effect row still carries `ℓ` at the perform site (the handler discharges it as today).
5. **No kernel change, no new primitive.** `with … as h` reuses the `handle` lowering with a user
   name where the sentinel went; `h.op` is `perform (vvar <h>) op arg`. Invariant #5 holds.

## v1 scope (deferred, not decided against)

- Payload/result types stay the surface convention (`Int` for state/exn/stm payloads, ADR-0030) —
  no per-op payload-type threading yet (same limit as the ambient forms).
- A named cap ESCAPING its handler (returned/captured past `with`) is the kernel's defined
  `escapedCap` fail-loud terminal (ADR-0063); post-v1 scoped cap types make it untypeable (#21/#18).
- `h.op` on a cap whose handler does not provide `op` is a checker rejection (label mismatch).

## Rejected alternatives

- **Dynamic / nearest-label dispatch for "ambient"** — already refuted (ADR-0052, the stale
  `evalD`); would reintroduce accidental handling (the `no_accidental_handling` soundness obligation
  exists precisely to forbid it).
- **Named-only (drop ambient)** — worse ergonomics for the 90% single-instance case; the sentinel
  sugar is free and reads better (`state 5 in get`).
- **A `sig`-style separate construct** — reintroducing `sig` is a standing DO-NOT (CLAUDE.md); the
  cap value already IS the signature-carrier.
- **`h#op` or `h::op` sigils** — `.` is the familiar method-call spelling (agent-generable, ADR-0040
  §5 rationale); reserve the others.

## Consequences

- Two state cells: `with state 1 as a in (with state 2 as b in (let x = a.get in (let y = b.get in x + y)))`
  → distinct identities, distinct cells — the demo the ambient form cannot write.
- The checker gains `Cap ℓ` synthesis for `with`-bound names and `h.op` row-contribution; ambient
  ops are unchanged.
- Capability-passing sets up the polymorphism story (a function `∀. Cap state → …`) once HM lands
  (ADR-0027) — a named cap is the first first-class effect value at the surface.

## Revisit if

- Scoped/region cap types land (#18/#21) — clause "v1 scope: escape" becomes untypeable-by-construction.
- HM lands — capability-passing generalizes to effect-polymorphic functions over `Cap`.
