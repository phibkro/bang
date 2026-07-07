# ADR-0084 · Networking is a typed effect + handler, gated on user-defined effects (#44); real sockets deferred to the backend

<!-- adr-frontmatter -->

- **Status**: Proposed
- **Summary**: The web-server northstar demands networking. Q39 frames it as a typed `{Net}` effect (`listen`/`accept`/`read`/`write`) realized by a swappable handler — capability-secured, effect-tracked, mock-for-tests/real-for-prod. VERIFIED FROM CODE: the kernel `Handler` (`Bang/Core/IR.lean`) is a CLOSED triple (`state`/`throws`/`transaction`) with operations HARDCODED in `handlesOp`/`dispatchOn` — there is no general handler carrying user op-clauses + a reified continuation. So a genuine `{Net}` effect (its own ops) REQUIRES **user-defined effects (#44)** as a hard KERNEL prerequisite (#44 = L, weeks, spine-touching, ~424 `Handler`-match sites, ripples to the calc machine/LR/soundness/backend per invariant #4). `{Net}` is a small INSTANCE of #44, not a peer. The achievable-now slice is a mock/simulated handler on the pure `Source.eval` (no syscalls); real sockets need the FFI seam (Q37) + compiled backend (◊5+). **Decision: name B (genuine {Net} via #44) as the correct answer; ship A (a "net-shaped" demonstrator over the existing `state` handler — zero kernel change, honestly labelled a demo, ops are get/put) as the cheap near-term slice; gate B on #44; defer D (real sockets) to ◊5+; REJECT C (a bespoke `| net` kernel constructor — spends #44's full ripple to buy one hardcoded effect, violating invariant #5's "generalize, don't special-case").**
- **Depends-on**: 0030, 0063, 0070
- **Relates-to**: Q39 (net-as-effect), Q37 (FFI-as-effect — the seam D needs), Q40 (compilation strategy), #44 (user-defined effects — the prerequisite), ◊5 (the backend a real server needs)

- **Status:** Proposed — scoped by the netscope design spike (2026-07-07); the #44-kernel-gate finding manager-verified against `IR.lean`/`Dispatch.lean`. Not accepted/started — the net prong is a longer chain gated on #44 + the runtime; this records the design + the achievable-now line for when it's taken up.
- **Date:** 2026-07-07
- **Layer:** effects/kernel (B/C touch the kernel via #44; A is a surface library over the existing `state` handler).
- **Builds on:** ADR-0030 (STM/concurrency — the `listen`/`accept` multiplexing substrate), ADR-0063 (`escapedCap` = the fail-loud "no handler ⟹ can't network"), ADR-0070/0072 (named capabilities — how a `Net` label instance is named at the surface). Reference: Q39 (the network-as-effect thesis), Q37 (FFI-as-effect).

## Context

The northstar (`docs/PRD.md`, the web-server/client project) demands networking. Q39 frames networking not as a
primitive but as a typed `{Net}` effect (`listen`/`accept`/`read`/`write`) realized by a swappable handler —
capability-secured (no handler ⟹ can't network), effect-tracked (the row shows a fn touches the net),
mock-for-tests / real-for-prod. The question: **can bang express a `{Net}` effect today, and if not, what is the
smallest thing it CAN run?** The kernel is a pure, fuel-bounded interpreter (`Source.eval`) — it cannot do a
syscall — so the real-net end is clearly deferred; the design question is where the achievable line sits.

## The gating fact (verified from the code)

The kernel `Handler` (`Bang/Core/IR.lean`) is a CLOSED set of three (`state`/`throws`/`transaction`); operations
are HARDCODED strings in `handlesOp`/`dispatchOn` (`Bang/Core/Semantics/Dispatch.lean` — `get`/`put`, `raise`,
`newTVar`/`readTVar`/`writeTVar`). There is no general handler carrying user operation-clauses + a reified
continuation. Named capabilities (ADR-0070/0072) name an *instance* of the three built-ins; they do not declare a
fourth effect kind. **Therefore a genuine `{Net}` effect requires user-defined effects (#44) as a hard KERNEL
prerequisite.**

## Considered options

- **A — "net-shaped" demo over the existing `state` handler.** A network buffer is state; under a distinct `Net`
  label (`Label` is a `Nat`, freely chosen at the surface), `read`/`write` are library functions over `get`/`put`
  on an in-memory buffer. Zero kernel change; runs on `Source.eval` today.
- **B — genuine `{Net}` effect + mock handler, via #44.** A user-declared `effect Net { read; write; … }` with its
  own named ops, discharged by a pure mock handler. Needs #44 (general handler) first. Runs on `Source.eval`; still
  no real socket.
- **C — bespoke `| net` `Handler` constructor.** A fourth kernel constructor for networking. **REJECTED.**
- **D — real `{Net}` + real sockets.** The FFI seam (Q37) + compiled backend (◊5+).

## Decision

Name **B** the correct answer; ship **A** now as an honest demonstrator; gate **B** on **#44**; defer **D** to ◊5+;
**reject C** (it spends #44's full ~424-site ripple to buy one hardcoded effect instead of the general form —
invariant #5 and #44 both say generalize the handler, don't special-case one more effect).

### The mock-now / real-later boundary (the load-bearing line)

```
runs PURE on Source.eval (in-memory simulation)  │  needs the RUNTIME (◊5+)
─────────────────────────────────────────────────┼──────────────────────────────
  A  net-shaped demo over state   (now, S)        │  D  real sockets via FFI (Q37)
  B  {Net} + mock handler (via #44, M)            │     + compiled backend
─────────────────────────────────────────────────┴──────────────────────────────
```
Everything left of the line is a pure request→response SIMULATION. A real web server is right of the line and does
not exist yet. The near-term prong is effect-MODELING, not a running server.

## Prerequisite chain

A (S, now) → **#44** (L, weeks, spine-touching) → B `{Net}`+mock (M, pure) → Q37 FFI seam + backend (XL, ◊5+) →
web server.

## Consequences

- A ships a real slice of the Q39 thesis (capability-security + handler-swap) with no kernel line touched
  (invariant #5 provably held) — but its ops are `get`/`put`, not the `{Net}` interface, so it must be labelled a
  demonstrator, not the effect.
- The chain is honest: #44 is the real gate, the backend the real server — nobody mistakes A for a running server.
- The genuine `{Net}` effect is far (behind #44, the largest post-MVP direction).

## Revisit if

#44 (user-defined effects) is taken up → B becomes a small instance (finalize this ADR to Accepted, first cut
`read`/`write` request→response, defer `listen`/`accept` = concurrency multiplexing to ADR-0030); OR the compiled
backend + FFI seam (Q37, ◊5+) lands → D (real sockets) becomes reachable.
