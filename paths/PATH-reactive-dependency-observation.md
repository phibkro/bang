# PATH-reactive-dependency-observation — expose the spreadsheet formula DAG before caching it

> Give stable spreadsheet formulas queryable compiler identities and prove their static dependency
> edges are observable through BANG's existing fact base, without claiming runtime subscription or
> incremental recomputation.

## Seam

- **From checkpoint**: `PATH-reactive-spreadsheet-tracer` proves live pull recomputation and the
  early-sampling failure mode across every execution route
- **To checkpoint**: the same journey runs unchanged while `bang query dump` exposes the exact static
  formula DAG and `bang impact` answers its reverse blast radius
- **Contract preserved**: formulas remain ordinary declarations/functions and the live observation
  boundary remains an unmemoized thunk over named State capabilities; there is no new reactive
  primitive, query schema, runtime graph, cache, or scheduler

## Layer

- [ ] Kernel  [ ] Compiler  [x] Surface  [x] Meta (docs/process)

## Actor journey / observable outcome

- **Actor / need**: a spreadsheet author or tool needs to answer “which formulas read this input or
  formula?” before changing it.
- **Public starting point**: `examples/reactive-spreadsheet/Formulas.bang`, queried with
  `bang query dump`, plus the unchanged `bang run examples/reactive-spreadsheet/main.bang` journey.
- **Terminal observation**: dump's existing `refs` facts equal `expected-dependencies.json`, with edge
  orientation `from depends on to`; `bang impact … subtotal` reports `tax` and `total`; execution still
  prints `((22, 26), (22, 22))`.
- **Adverse / recovery route**: expression-local `let` formulas have no stable declaration identity and
  therefore produce no `dump.refs` facts. Promote reusable/queryable formulas to top-level declarations
  in a module; do not invent ordinal local-node IDs that would churn after source edits.
- **Downstream journey released**: static spreadsheet dependency inspection and pre-edit impact.

## Feeds the constraint

- **Binding constraint now**: the completed spreadsheet tracer selected dependency observation before
  a cache, while ADR-0076 and the compiler-as-DBMS design already designate `dump` as BANG's versioned
  extensional fact base.
- **How this path feeds it**: make formula identity explicit at the source boundary and reuse the
  existing declaration-reference relation. This tests whether a new reactive graph is necessary; the
  tracer says it is not necessary for stable static formulas.

## Prospective systemic review

| concern | horizon + evidence | likelihood / impact / late cost | disposition now | reopen trigger |
|---|---|---|---|---|
| local formula identities are exposed as unstable traversal ordinals | immediate if local lets are added to the public schema without spans/IDs | high / high / high | **reject** ordinal IDs; keep the public graph declaration-granular | stable spanned-node identity plus an IDE or spreadsheet consumer that needs locals |
| requiring a formula module is too much authoring ceremony | first tracer uses five tiny declarations; recovery is explicit | medium / medium / low | **implement** module convention and document it | organic user cannot discover or accepts neither module nor local opacity |
| a new dependency table drifts from existing `refs` | existing fact base already emits the exact graph | high / high / medium | **reject** duplicate extraction/schema | required dependency semantics cannot be expressed as name references |
| diamond dependencies recompute shared formulas repeatedly | `total` reaches `subtotal` directly and through `tax`; no runtime count yet | medium / medium / high if caching leaks late | **preserve and defer** measurement/caching | ≥100-cell representative sheet plus trace shows material repeated work |
| static references are mistaken for runtime subscriptions | query facts describe source declarations, not force events | medium / high / low | **implement** explicit static/runtime boundary in docs and evidence | runtime graph or dynamic formula construction is introduced |
| cycles need diagnostics | top-level non-recursive declarations are ordered; recursive declarations are explicit | low now / high later / medium | **defer** | recursive formula API or first cyclic dependency consumer |
| execution and observation disagree after modularization | resolver and compiled paths can differ | medium / high / low | **implement** query, source/oracle, env, compiled, and concrete-Wasm gates | any route or graph fixture diverges |

## Baseline, falsifier, and evidence

- **Baseline / red observation**: the prior single-expression spreadsheet runs, but its local formula
  names are not `Decl` facts, so the query fact base cannot address them.
- **Smallest tracer bullet**: five stable top-level descriptions (`price`, `quantity`, `subtotal`,
  `tax`, `total`) in `Formulas.bang`, selected by the runtime entry file.
- **Positive evidence**: the exact five-edge DAG is derived from `dump.refs`; reverse impact on
  `subtotal` is `{tax,total}`; runtime output is unchanged across every standing route.
- **Negative or recovery evidence**: a local-let fixture yields an empty reference array, while the
  formula module yields the expected graph through the same query operation.
- **Broader convergence gate**: query battery, example corpus, compiled/Wasm differentials,
  `just fitness`, and `CHANGELOG_STABLE_REF=codex/fresh-paper-review just verify`.
- **Assumptions / exclusions**: this is static, declaration-granular dependency observation. It does
  not expose local subexpressions, count evaluation, maintain runtime subscriptions, cache results,
  selectively invalidate, schedule propagation, diagnose general cycles, or prove glitch freedom.

## Plan

1. [x] Prototype stable formula declarations and confirm the existing reference fact base emits the DAG.
2. [x] Gate the exact graph, local-let negative control, and reverse impact through the public CLI.
3. [x] Preserve the live/stale runtime differential across source, machines, compiled, and Wasm routes.
4. [x] Document the formula-module convention and the static/runtime boundary beside the example.
5. [x] Close the path and decide whether measurement—not caching—is the next spreadsheet slice.

## Status

- [x] Started 2026-07-18
- [ ] In flight: none; successor work begins from measured recomputation tracing
- [ ] Blockers: none
- [x] Completed 2026-07-18
- Retained failed gates / successors: the first prototype left the two identity-input declarations
  polymorphically underdetermined in query output → pin them to `Int -> Int`; local formula names absent
  from declaration facts → recover with stable formula module; diamond recomputation visible statically
  but unmeasured → measurement successor. Final query battery: 99/99; source/oracle: 58/58;
  environment: 58/58; compiled dogfood: 6/6; concrete build/Wasm: 16/16.
- Full convergence gate: `CHANGELOG_STABLE_REF=codex/fresh-paper-review just verify` passed.
- Reopen / observe: local-node facts only with stable identities and a consumer; caching only after a
  representative workload and evaluation trace establish cost

## Owner

- Agent / human: Codex

## Notes

This is a representation tracer, not an optimizer. Its strongest result is negative: BANG does not need
a second dependency extractor or reactive graph to make stable formulas inspectable. The existing
compiler fact relation is sufficient once the program gives formulas durable declaration identities.
