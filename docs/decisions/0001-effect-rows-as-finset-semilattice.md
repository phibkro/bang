# ADR-0001 · Effect rows are idempotent sets (a join-semilattice), modeled as `Finset`

- **Status:** Accepted
- **Date:** 2026-05-31
- **Related:** 0002 (Lean substrate makes the laws free), spec `bang-lang-design.md` ("rows are sets… compose via union")

## Context

Effect rows must be represented for both the type system and the unifier. The spec states rows are order-insensitive, duplicate-free, and compose by union. We needed a concrete algebra to build the unifier and its correctness proof on.

## Decision

Model a row's label set as an **idempotent set** — a bounded **join-semilattice** under union. In the Lean reference, this is `Finset ℕ` with `∪`. An open (polymorphic) row is `{ labels : Finset, tail : Option RVar }`.

## Rationale

- Matches the spec verbatim: sets, order-insensitive, compose by union.
- Union laws (commutative, associative, idempotent, `∅` identity) are **inherited** from Mathlib's `Finset` `Lattice` + `OrderBot` instances — not proven by hand.
- Extensional equality is **definitional** (`Finset.ext`), so "canonical form is unique" (the keystone we'd have proved manually in F\*) is free.
- Matches Effect TS's `R`/`E` channel behavior (dedup, order-insensitive), keeping any future lowering honest.

## Rejected alternatives

| option | why not |
|--------|---------|
| ordered list of labels | introduces order artifacts → false diffs in the harness; needs ACI unification machinery |
| multiset | wrong algebra; rows are idempotent, multiplicity is meaningless |
| sequence / stack | implies order matters; it doesn't |

## Consequences

- (+) The unifier already answers the spec's open question on row variables (`with IO, ...e`): open/closed/open-open unification over `(labels, tail)`.
- (+) Soundness (`unify_sound`) is the property to prove; **most-generality (MGU) is deferred to the differential test** (ACI unification is finitary but not unitary).
- (−) None material.

## Revisit if

Rows ever need to carry per-effect **multiplicity** (graded/quantitative effects) or **ordering** — at which point the algebra changes from semilattice to something graded, and this ADR is superseded. (Not anticipated.)
