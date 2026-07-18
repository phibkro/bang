# 0112 — row attenuation as an erased `pledge`

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: `pledge {E₁, …} in e` checks that `e`'s inferred effect row is a subset of the
  named closed row, retains the actual inferred row, and erases before kernel lowering. This is
  an effect-label ceiling, not runtime filtering or value-level resource policy.
- **Depends-on**: [0001](0001-effect-rows-as-finset-semilattice.md) (row order),
  [0026](0026-correctness-ladder-and-checker-boundary.md) (tested-superset boundary),
  [0066](0066-surface-type-system.md) (checked ascriptions),
  [0107](0107-effect-row-subeffecting-at-reuse-sites.md) (subset relation at use sites)
- **Date**: 2026-07-18
- **Deciders**: operator + Codex, from the resource-obligation consumer in
  `paths/PATH-semantic-contracts.md`
- **Ties**: `docs/notes/os-inspiration-survey.md`, `examples/pledged-plugin/`

## Context

The semantic-contract framing now has effect contracts, laws, named realizations, and dynamically
selectable installer functions. The next real gap appeared in the sandboxed-plugin design: a
sub-computation could use explicit capabilities, but it had no row-only way to state “these are all
the effects this region may perform.” A full type ascription could impose the same upper bound only
by repeating the result type, coupling an authority assertion to unrelated type detail.

Bang already has the required row order and checker operation. The missing piece is a surface form
that makes the authority ceiling explicit and local without introducing a runtime primitive.

## Decision

Add this tested-superset expression:

```bang
pledge {Audit} in audit.record(41)
```

Its rule is:

1. Infer or check the body normally, producing result type `A` and actual row `ρ`.
2. Resolve every named built-in or user effect in the pledge to a concrete label. An unknown name
   is an error; it never becomes a fresh or empty row.
3. Require `ρ ⊆ ρmax`. If not, reject the region with a `pledge violation` diagnostic showing the
   inferred and allowed rows.
4. Return `A` with the original `ρ`, not `ρmax`. A pure body under `pledge {Audit}` remains pure.
5. Erase the `pledge` node during surface lowering. The core term, handlers, machines, and runtime
   behavior are unchanged.

Module resolution qualifies locally declared effect names in pledges by the same rule used for row
annotations. The formatter preserves a canonical `pledge {E₁, E₂} in …` spelling.

## Why this model

1. The statement is an upper-bound assertion, which is exactly the existing row-subset relation.
2. Preserving the actual row keeps inference precise and makes the construct monotone: widening the
   permitted ceiling does not make a body appear more effectful.
3. Erasure keeps policy in the frontend stratum. No new trusted runtime representation is needed.
4. A result-type-independent form remains stable when the computation's data type changes; that is
   the practical advantage over duplicating a whole `(e : T ! {…})` ascription.

## Consequences

- Plugin and callback boundaries can make their complete effect-label authority reviewable in the
  source, and adding a wider effect becomes a compile-time failure.
- `pledge` does not grant capabilities. A body still needs an in-scope `Cap E` to perform `E`.
- `pledge` does not intercept operations at runtime. Handlers continue to define the meaning of
  admitted effects.
- The construct restricts **which effect labels** may occur, not **which values or resources** an
  admitted effect may access. Filesystem paths, hostnames, quotas, and similar `unveil`-style policy
  remain handler-enforced today and may later gain refinement types.
- This slice adds no irreversibility or temporal privilege state. Nested source regions may state
  different ceilings; each assertion is checked independently against its lexical body.

## Rejected or deferred

- **Runtime masking/filtering** — rejected for this slice: it would add a new failure mode and
  machine semantics where a static subset check is sufficient.
- **Return the declared row rather than the actual row** — rejected: it loses information and makes
  a pure computation spuriously effectful.
- **Use only ordinary type ascriptions** — rejected as the user surface: technically sufficient,
  but it forces authority policy to duplicate an unrelated result type.
- **Path/value attenuation in this construct** — deferred: rows carry labels, not predicates over
  operation arguments. Handler policy is the honest current mechanism.
- **First-class attenuated capability values** — deferred until a consumer needs per-capability
  operation subsets rather than a computation-row ceiling.

## Confirmation

- `examples/pledged-plugin/` runs an `Audit`-only plugin under the named `Count` realization and
  prints `1`; its sibling `Secret` contract makes the denied authority visible.
- Lean guards pin parsing, formatter round-trip/idempotence, exact/wider accepted bounds, an extra
  effect rejection, an unknown-effect rejection, and end-to-end erasure through evaluation.
- `tools/test-check-json.sh` requires the admitted program to exit 0 and the two-effect program to
  report `pledge violation` with exit 1 through the public CLI.
- `examples/policy-host-allowlist/` confirms the deliberately separate value-level boundary: two
  runtime handler parameters admit different hosts under the same pledged `{Net}` row (ADR-0113).

## Revisit if

A real consumer needs value-level resource restrictions, irreversible privilege state, operation-
subset capabilities, or a runtime boundary for dynamically loaded code whose body was not checked
by Bang.
