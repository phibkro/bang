---
type: design-question
title: "Polymorphism + effect-row polymorphism"
description: "parametric + effect-row + grade polymorphism, staged monomorphic → HM → System F"
status: decided
area: type-system
resolved-by: ["ADR-0027"]
ties: ["Q18", "Q19", "ADR-0001", "ADR-0027"]
see-also: []
---
**Resolution**: **Staged across three tiers; v1 takes only the first.** (1) v1/MVP = **monomorphic**
(no type/row/grade variables; rung 2's stack is `Stack Int`, not `Stack a`); (2) next = **Hindley-Milner**
(rank-1, decidable inference — where "paradigms as libraries" becomes real); (3) ambitious = **System F**
+ effect-row variables `⟨e | ε⟩` (cashing the K1 unifier) + grade polymorphism. See **ADR-0027**.
Original deliberation preserved below.

**Question**: the kernel type syntax (`VTy = unit | int | U eff cty`; `CTy = F mult vty | arr …`) is
**monomorphic** — no type variables, no effect-row variables. How does bang express parametric
polymorphism, and crucially **effect-row polymorphism** (a function generic over the effects of its
argument)?

**Why it matters**: without it there is no reusable higher-order effectful code. `map : (a →^e b) →
List a → List b !e` must be polymorphic in BOTH the element types AND the effect row `e` — otherwise
every effect needs its own `map`. Forced at rung 3+ (any HOF over effects); blocks the whole library
story (paradigms-as-libraries needs effect-generic combinators).

**Detail**: two axes — (1) ordinary parametric polymorphism (System-F-style type variables / `∀`);
(2) **row polymorphism** (effect-row variables `ε` with `e ⊔ ε`), the Koka/Frank/Links mechanism. The
grades complicate both: a polymorphic function must also be generic in the multiplicity/coeffect
grades (grade polymorphism — Granule territory). Interacts with Q18 (polymorphic data types) and
inference (grade + row inference is hard).

**Options**: (1) System-F + row variables (Koka-style open rows `⟨e | ε⟩`); (2) bounded/qualified
polymorphism (constraints, links to Q19 typeclasses); (3) stay monomorphic + rely on metaprogramming
(Q20) to generate monomorphic instances — rejected as a non-answer (no real genericity). The row
algebra is already `Lattice + OrderBot` (ADR-0001); row variables sit on top as `e ⊔ ε`.

**Blocked on**: nothing structural now; forced when rung 3 (or any effect-generic combinator) is built.

**Revisit signal**: writing the first effect-generic higher-order function (a `map`/`fold` over an
arbitrary effect row); or rung 2's stack needing element-type polymorphism.
