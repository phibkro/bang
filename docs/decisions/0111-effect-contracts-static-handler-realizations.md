# 0111 — effect contracts with statically selected named handler realizations

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: Effects may carry laws and named handlers may declare reusable realizations of an
  effect. A named installation is selected statically and elaborates to the existing custom-handler
  form; `bang test` and `bang query laws` reuse the trait-law machinery over effect × handler pairs.
  No kernel constructor, dynamic handler value, or trait/effect syntax merger is introduced.
- **Depends-on**: [0040](0040-laws-as-algebraic-interfaces-proof-first.md) (law-bearing interfaces
  and the proof→test ladder), [0085](0085-general-handler-coexist-one-shot-v1.md) (the existing
  `Handler.custom` runtime meaning), [0095](0095-stage7-handler-surface.md) (inline custom-handler
  syntax and one-shot clause convention), [0106](0106-trait-op-name-call-dispatch.md) (the current
  trait realization/law runner machinery this decision generalizes rather than duplicates)
- **Date**: 2026-07-18
- **Deciders**: operator + Codex, from the semantic-contract framing adopted in conversation
- **Ties**: `docs/notes/laws-taxonomy.md`, `examples/codec-contract/`,
  `paths/PATH-semantic-contracts.md`

## Context

Bang already had both halves of the idea, but they were disconnected. Traits could declare laws
and `bang test` could check each matching `impl`; effects could declare operations and install an
inline custom handler. What could not be stated was the product-level claim we want the language to
make: a computation depends on an explicit contract, multiple realizations may implement it, and the
same observable laws travel across those realizations.

The tempting implementation was to turn handlers into a new dynamic `Val` and change the kernel.
That spends the most trusted-layer budget before a consumer needs runtime handler selection. The
existing frontend already has a cheaper truthful seam: it can retain named declarations in the
elaboration environment and expand a selected name into the already-proven custom-handler surface.

## Decision

Adopt the following tested-superset surface:

```bang
effect Codec {
  encode : Int -> Int
  decode : Int -> Int
  law roundtrip(codec, x):
    let encoded = codec.encode(x) in codec.decode(encoded) == x
}

handler Shift7 implements Codec {
  encode(x) => x + 7,
  decode(x) => x - 7
}

handle body with Shift7 as codec
```

1. An effect law's first parameter is an explicit capability binder. Remaining parameters are the
   sampled inputs. This keeps the law honest about where its operations come from.
2. `handler H implements E { … }` is a named static realization. `E` must already be declared;
   every effect operation must have a clause, and no clause may name a foreign operation.
3. `handle body with H as cap` statically looks up `H`, substitutes its effect and clauses, and then
   follows the existing inline-custom-handler elaboration, typing, lowering, and runtime path.
4. Law discovery forms effect-law × matching-handler instances. The generated body installs the
   realization around the law body; the existing deterministic sampler, shrinking, result model,
   and CLI reporting are reused unchanged.
5. Query facts grow additively: declarations gain kind `handler`; effect shapes list laws; law facts
   gain `contract` and nullable `realization`. The historical `trait` field remains as a compatibility
   key (`Codec@Shift7` for this new case), so schema version 1 remains valid.

This is a frontend/tested-superset decision. `Bang.Core.Handler`, the effect-row algebra, calculated
machines, soundness statements, and compilation theorems do not change.

## Consequences

- One contract can now govern multiple operational choices, and a broken realization produces an
  ordinary reproducible counterexample through `bang test`.
- Handler choice is explicit at the use site without duplicating clauses at every installation.
- Traits and effects converge in law machinery and query vocabulary while retaining distinct
  declaration surfaces and binding-time meanings.
- Runtime selection (`if … then H1 else H2`) is deliberately unavailable. Add it only when a real
  program needs handlers to inhabit `Val`; that change must pay the kernel/machine/proof ripple then.
- Effect-operation arguments remain value positions. A dependent operation sequence uses an
  explicit `let`; this decision does not hide or redesign the current CBPV boundary.

## Rejected or deferred

- **Make handlers first-class values now** — deferred: no current consumer requires dynamic
  selection, and it would touch the trusted kernel and every derived machine.
- **Merge `effect`/`handler` into `trait`/`impl` syntax** — rejected for this slice: shared law
  mechanics do not imply identical binding time or calling convention. Convergence belongs in the
  implementation layer until evidence justifies a surface merger.
- **Copy laws onto every handler** — rejected: it inverts ownership and permits realizations to
  silently choose weaker obligations.
- **Create a second effect-law runner** — rejected: `lawInstancesOf` already supplies the correct
  discovery/evaluation/query seam.

## Confirmation

- `examples/codec-contract/main.bang` evaluates a `Shift7` encode/decode round trip to `35`.
- `bang test examples/codec-contract/Codec.bang` passes four deterministic instances (two laws ×
  two realizations).
- `tools/test-law.sh` also installs `BrokenShift` and requires a failing counterexample.
- Resolver-aware `query dump`/`query laws` retain the Codec module's qualified contract × handler
  facts through the shared `lawInstancesOfProg` declaration walk.
- `examples/stage-swap/` keeps its same-typed installer functions runtime-selectable while each
  installer statically selects a named `Net` realization; both realizations pass the shared
  stability law and the observable result remains `30005`.
- Lean guards pin the rendered effect-handler law instances, while the formatter/query/example
  batteries cover the new declaration shapes end to end.

## Revisit if

A concrete program must store, pass, return, or choose a handler at runtime; contract discharge
needs proof artifacts rather than the existing tested rung; or effect laws need quantified inputs
beyond the current Int sampler.
