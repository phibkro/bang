---
type: design-question
title: "`group_recovers` bridge: E group ⇒ F dagger-Frobenius?"
description: "reversibility needs Frobenius (stronger than a group); group_recovers RETIRED, unresolved-but-bounded"
status: decided
area: effects
resolved-by: ["ADR-0032"]
ties: ["ADR-0016", "ADR-0030", "ADR-0032"]
see-also: ["references/papers/adjacent/heunen-karvonen-reversible-monadic.pdf", "references/papers/adjacent/compositional-reversible-2024.pdf"]
---
**Question** (from the original wasmfx spec; surfaced in ADR-0016 + §6 of
Spec.lean): if `Eff` forms a group (effects are invertible), does the
graded monad `F` become dagger-Frobenius (Heunen-Karvonen)? If yes,
`group_recovers` is a corollary. If no, the theorem needs an explicit
observability side-condition.

**Resolution (2026-06-23, ADR-0032 — the ◊4 PROOF_ORDER #2 research gate):** the
H-K bridge as stated is **unsupported** — reversibility needs the monoid to be
**Frobenius** (involutive + the Frobenius coherence law), strictly stronger than a
group; our idempotent join-semilattice `Eff` is even further from Frobenius. AND
`group_recovers` was **false-as-stated** (a diverging `c` makes `(c;ret()) ≉ ret()`)
and **vacuous** (no `AddGroup` instance for the real effect lattice). So
`group_recovers` is **RETIRED**, not side-conditioned: v1 rollback is a HANDLER
mechanism (`all_or_nothing_abort`, ADR-0030/0031), not an effect-algebra inverse.
Q8 stays formally open (post-v1: a correct Frobenius-conditioned law would be a NEW
theorem) but bounded — it gates nothing in v1. References on disk:
`references/papers/adjacent/{heunen-karvonen-reversible-monadic,compositional-reversible-2024}.pdf`.

**Revisit signal**: Phase B PROOF_ORDER #2 (sequenced second precisely so
this surfaces before compiler work depends on it).
