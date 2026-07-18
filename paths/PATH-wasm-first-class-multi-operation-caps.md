# PATH-wasm-first-class-multi-operation-caps — dispatch every runtime custom operation exactly

> Carry exact operation identity and per-clause update behavior with a first-class custom capability,
> so concrete Wasm agrees with the source when an effect has more than one operation.

## Seam

- **From checkpoint**: `PATH-reactive-within-observation-reuse` found that a natural two-operation
  cache passed source, environment, and compiled execution but trapped in concrete Wasm.
- **To checkpoint**: a capability passed through a function invokes distinct plain and updating
  operations, preserves handler memory, and returns 255 identically on every execution route.
- **Contract preserved**: lexical custom dispatch keeps its compile-time position fast path; escaped
  capabilities still trap; custom clauses still resume one-shot in place.

## Layer

- [ ] Kernel  [x] Compiler  [x] Surface tracer  [x] Meta (tests/docs)

## Actor journey / observable outcome

- **Actor / need**: an effect author passes `Cap Register` into a reusable function and expects both
  declared operations to dispatch to their own clauses on concrete Wasm.
- **Public starting point**: `bang run examples/first-class-multi-operation-cap/main.bang` and `bang
  build examples/first-class-multi-operation-cap/main.bang`.
- **Terminal observation**: plain `inspect` reads 2, updating `advance` installs and returns 5, and a
  second `inspect` reads 5; the encoded result is 255 on source/env/compiled/Wasm.
- **Adverse / recovery route**: selecting clause 0, applying one handler-wide update bit, losing the
  updated parameter, or confusing distinct operation identities changes the value or traps.
- **Downstream journey released**: natural multi-operation effect interfaces can cross function and
  source-module boundaries within one emitted whole program without compressing their protocol into a
  one-operation workaround.

## Feeds the constraint

- **Binding constraint now**: the concrete emitter had no operation identity once a capability crossed
  an argument slot. It guarded position 0 with `clauselen == 1`, correctly refusing to guess but making
  typed multi-operation capabilities unusable on the product target.
- **How this path feeds it**: intern source operation names exactly into module-local numeric identities;
  store identity, update mode, and closure together in each runtime clause record; search only the
  supplied capability's records when compile-time `CapSlot` metadata is absent.

## Prospective systemic review

| concern | horizon + evidence | likelihood / impact / late cost | disposition now | reopen trigger |
|---|---|---|---|---|
| hashes collide and silently choose a wrong clause | first large program; dispatch identity | low / critical / high | **reject hashes**; exact String interning assigns collision-free module-local ids | identities become serialized or externally supplied |
| one update bit is applied to every operation | first mixed plain/updating handler; tracer | high / high / medium | **implement** update mode on each clause record | a third clause mode is introduced |
| runtime search cost grows with effect size | every first-class perform; currently tiny protocols | medium / medium / low | **accept linear search**, measure before indexing | a representative effect has many operations or profiles show dispatch cost |
| module-local ids leak into an ABI | separate compilation/dynamic linking | medium / high / high | **bound** ids to one emitted whole-program module | independently emitted modules exchange capabilities |
| an undeclared runtime op selects another clause | malformed/untyped IR; typed surface forbids it | low / high / low | **trap** when exact search misses | GC emitter gains a runtime raise-forward path |
| clause records break lexical custom dispatch | immediate; every existing custom example | medium / high / low | **preserve** position lookup and run the full emitter corpus | lexical and runtime representations diverge again |
| shared `$txbox` changes break transactions | immediate representation edit | medium / high / low | **gate** STM/rollback and concrete build corpus unchanged | transaction storage splits from `$txbox` |
| runtime metadata becomes collectible before closures | immediate GC reachability | low / high / medium | **store records in the cap-owned env list**; records strongly reference closures | weak references or manual memory enter the backend |

## Baseline, falsifier, and evidence

- **Baseline / red observation**: the two-operation `lookup`/`store` cache probe returned correctly on
  three evaluators, then Wasmtime trapped at the deliberate single-clause runtime guard.
- **Smallest tracer bullet**: one function argument, two operation identities, a plain first clause,
  an updating second clause, and a final read that observes handler memory.
- **Positive evidence**: 255 across source, environment, compiled, and concrete Wasm; existing lexical
  custom handlers, transactions, capability liveness, and module builds remain in their standing gates.
- **Negative or recovery evidence**: the tracer's clause ordering makes both old shortcuts fail: always
  choosing position 0 calls `inspect` for `advance`, while using the first clause's plain mode returns
  an unconsumed pair and fails to install 5. Missing exact ids trap in `$clausefind`.
- **Broader convergence gate**: source/env example corpus, compiled differential, concrete build/Wasm,
  auto-discovered rung-5 emitter differential, `just fitness`, and `just verify`.
- **Focused gate results**: source 61/61; environment 61/61; compiled dogfood 12/12; concrete build/
  Wasmtime 22/22; query 107/107; emitter differential 47 whole programs, 24 effectful, plus the raw
  stateful custom witness and 14 exact named frontend/harness/host-IO refusals.
- **Assumptions / exclusions**: ids are internal to one emitted module; search is linear; the concrete
  text emitter remains differential-tested rather than part of the abstract backend proof claim.

## Plan

1. [x] Reproduce and isolate the first-class multi-operation concrete-Wasm trap.
2. [x] Compare runtime strings, hashes, static type metadata, and module-local exact interning.
3. [x] Implement runtime clause records with exact operation id, update mode, and closure.
4. [x] Land the mixed-mode actor tracer and focused cross-engine/concrete-Wasm gates.
5. [x] Converge the auto-discovered emitter and full repository gates; publish the increment.

## Status

- [x] Started 2026-07-18
- [x] Converged: focused differentials, `just fitness`, and `just verify` passed
- [ ] Blockers: none
- [x] Completed 2026-07-18
- Retained failed gates / successors: a handler-clause body beginning with `let` is outside the current
  update-clause ret-shape → use `(next, next)` directly; general computing update clauses stay with the
  existing handler-return-shape frontier, not this dispatch representation slice
- Reopen / observe: separate compilation of capability-bearing modules, measured large-effect dispatch,
  or a runtime raise-forward path for malformed/unhandled operation ids

## Owner

- Agent / human: Codex
