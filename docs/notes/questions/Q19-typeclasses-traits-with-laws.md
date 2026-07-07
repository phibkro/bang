---
type: design-question
title: "Typeclasses/traits with laws (ad-hoc polymorphism + the laws surface)"
description: "ad-hoc polymorphism = the laws surface; enforced algebraic interfaces (traits + law members)"
status: decided
area: type-system
resolved-by: ["ADR-0040"]
ties: ["Q17", "ADR-0026", "ADR-0040"]
see-also: []
---
**Resolution**: **ADR-0040** (the user-grilled laws-surface design) answers this: laws are
first-class, enforced **algebraic interfaces** (Rust-ish traits whose `law` members are
operations + equations relating them; the moat's user-facing face). Discharge is **proof-first**
→ property-test → assert, descent explicit + marked (amends ADR-0026's test-default). Monomorphic
first, Hindley-Milner next (ADR-0027). The *resolution discipline* (option 1 vs 2 vs 3 below) is
subsumed by the algebraic-interface framing. The full rationale + rejected alternatives live in
**ADR-0040** (the SoT); the original deliberation is preserved below.

**Question**: how does bang do ad-hoc polymorphism / overloading (`+`, `Eq`, `Ord`, `Monoid`)? And —
since **a typeclass IS a set of operations + laws** — is the typeclass mechanism *also* the **laws
surface** (the moat's user-facing face, design-space #3)?

**Why it matters**: `Monoid {op, id; assoc, unit-laws}` is exactly "fields, operations, and the
laws/relations between them" from the original vision. Unifying ad-hoc polymorphism with the
law-declaration surface would make the moat fall out of the module/class system rather than being a
separate feature (one-construct-per-problem).

**Detail**: the discharge of the laws is settled (ADR-0026: assert + property-test by default, climb to
SMT/proof). Open is the *surface*: how a `class`/`trait`/`structure` declares ops + laws, how instances
are resolved (typeclasses à la Haskell? traits à la Rust? canonical structures / implicits à la
Lean/Coq?), and how that resolution interacts with the grades + effect rows (a method may itself be
effectful). Links tightly to Q17 (qualified polymorphism = constrained type variables).

**Options**: (1) Haskell-style typeclasses with law obligations attached, discharged on the ADR-0026
ladder (recommended — unifies ad-hoc poly + the moat); (2) Rust-style traits (coherence via orphan
rules); (3) Lean/Coq implicits + canonical structures (powerful resolution, heavier). All three make
laws first-class; the choice is the resolution discipline.

**Blocked on**: Q17 (polymorphism) — qualified polymorphism needs type variables first.

**Revisit signal**: the first overloaded operation (rung 2's stack wanting `Eq`/`Monoid`), or building
the user-facing law surface.
