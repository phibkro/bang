# PATH-semantic-contracts — computation descriptions with explicit, swappable realizations

> Make the project framing executable one thin slice at a time: effects and obligations remain
> explicit, realizations are selected by handlers, and calculation into the existing runtime stays
> visible rather than hidden behind new primitives.

## Seam

- **From checkpoint**: ◊5.25 close + demo — user-defined effects and custom handlers are runnable
- **To checkpoint**: ◊5.75 compiled demo pack — examples expose stable contracts independently of
  the realization/backend chosen for them
- **Contract preserved**: no kernel primitive without a consumer; proof and machine routes continue
  to ride the existing custom-handler representation

## Layer

- [ ] Kernel  [x] Compiler  [x] Surface  [x] Meta (docs/process)

## Feeds the constraint

- **Binding constraint now**: the runtime-as-handler thesis was executable only with inline clauses,
  while laws applied only to trait implementations (`docs/notes/laws-taxonomy.md`); there was no
  reusable, queryable contract × realization unit a project could organize around.
- **How this path feeds it**: add the smallest law-bearing effect + named-handler slice, then let its
  next real consumer expose whether the binding constraint is module facts, dynamic selection,
  richer law inputs, or resource obligations.

## Plan

1. [x] Add effect laws and named static handler declarations; elaborate installation through the
   existing custom-handler path, with no kernel change.
2. [x] Generalize `bang test`/`bang query laws` from trait × impl to contract × realization and pin
   positive plus counterexample behavior.
3. [x] Land `examples/codec-contract/` and ADR-0111 as the first end-to-end witness.
4. [x] Close the resolver-aware query gap so imported contracts retain law facts in an entry-file
   `dump`; use the Codec module split as the consumer.
5. [x] Choose the next semantic-contract slice from a real example: `stage-swap` shows that runtime
   selection belongs at the already-first-class installer layer and does not yet require handler
   values in the kernel.
6. [x] Give `stage-swap` a reusable `Net` contract, two named realizations, and one shared stability
   law while preserving its runtime-selected installer and observable result.
7. [x] Let the next consumer decide whether explicit resource obligations are now the binding
   constraint: the sandboxed-plugin sketch exposed row-only attenuation as the smallest missing
   statement, so land `pledge {E, …} in body` as an erased checked upper bound (ADR-0112).
8. [x] Let a consumer test the remaining value-level resource-policy boundary: the
   `policy-host-allowlist` program keeps both host values in one `{Net}` row and enforces the
   runtime allowlist through a parameter-carrying handler installer. No refinement, new syntax, or
   kernel value is needed (ADR-0113).

## Status

- [x] Started 2026-07-18
- [x] In flight: contracts, imported law facts, runtime-selected `stage-swap`, erased row ceilings,
  and the value-level handler-policy consumer are implemented
- [ ] Blockers: none
- [x] Completed 2026-07-18

## Owner

- Agent / human: operator + Codex

## Notes

The first slice deliberately says “statically selected realization,” not “handler is a value.” The
latter would be a kernel claim. `stage-swap` sharpens the boundary: programs can already pass and
choose same-typed installer functions dynamically, while those installers select named handlers
statically. Cross into kernel handler values only when that composition pattern is insufficient.

`pledged-plugin` sharpens the next boundary: rows can now state **which effects** a region may use;
handlers remain the truthful place to restrict **which resources or values** an admitted operation
may touch. Do not present `pledge` as a path sandbox or runtime filter.

`policy-host-allowlist` closes that question for the first consumer. One plugin and one `{Net}` row
run under two runtime-selected host values; the existing `(Effect init)` / `param` handler seam is
already sufficient. The next honest stressor is stateful policy (quota/revocation): read-only
`param` and ret-shaped clauses, not value refinements, are the likely boundary to test.
