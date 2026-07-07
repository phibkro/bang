---
type: design-question
title: "Type isomorphism — how to check two types are isomorphic and convert between them (types-as-algebra: derive structural isos, law-check witnessed ones)"
description: "A type iso is a lawful inverse pair (to/from with from∘to=id, to∘from=id). Two ways: STRUCTURAL — types-as-algebra (sum=+, product=×, Unit=1, Void=0 semiring), normalize both + compare, DERIVE the iso; WITNESSED — user gives to/from, property-test the laws (the bite-2 trait-law mechanism). Option a ≅ Either Unit a, Result e a ≅ Either e a are structural."
status: open
area: type-system
ties: ["Q31", "ADR-0081", "ADR-0068", "ADR-0069"]
see-also: ["Fiore et al. — decidable type isomorphism", "the schema-as-derived-codec thread (Q37/native validation)", "prelude Option/Result/Either isos", "Curry-Howard (Q42)"]
---

**Question**: how do we CHECK that two types are isomorphic, and CONVERT between them? (Raised via
`Result e a ≅ Either e a` and `Option a ≅ Either Unit a` — "mapping to left/right types".)

**The definition**: a type isomorphism `A ≅ B` is a **lawful pair of mutually-inverse conversions**:
```
to : A → B      from : B → A      with   from ∘ to = id_A   AND   to ∘ from = id_B
```

**Two ways to establish it (they map onto the derivation ladder):**
```
STRUCTURAL (DERIVE)   types-as-ALGEBRA: sum = +, product = ×, Unit = 1, Void = 0 (a SEMIRING).
                      Normalize both types to canonical algebraic form; EQUAL ⟹ the iso is DERIVABLE.
                      Option a = 1 + a  ·  Either Unit a = 1 + a  → same normal form → GENERATE to/from.
                      Result e a = e + a  ·  Either e a = e + a  → same → derivable.
                      Rewrite rules = the semiring laws: a+b ≅ b+a, a×(b+c) ≅ a×b + a×c, a×1 ≅ a, a×0 ≅ 0, …
WITNESSED (TEST)      user gives to/from; PROPERTY-TEST the two laws (from∘to = id, to∘from = id).
                      This IS the bite-2 trait-law mechanism — an `Iso a b` is a lawful trait, exactly like
                      `decode ∘ encode = id` from the schema-as-derived-codec thread.
```

**Why it matters / fits the thesis**: same "the type is the source of truth" move as native schema validation
— structural isos can be GENERATED (drift-unrepresentable rung) and any claimed iso is LAW-CHECKED (test
rung). It unifies generic data (the algebraic types, ADR-0069/0081), bite-2 laws (the witnessed check), and
deriving (the schema thread). The forgetful map to an interface (parametricity, [[Q42 proving in bang]]) is
the same idea one level up.

**Now vs later**:
- **Witnessed isos work TODAY** (bite-2): manual `to`/`from` + property-tested round-trip laws. The prelude
  `Option`/`Result`/`Either` conversions (`resultToEither`/`optionToEither`/inverses) are the FIRST witnessed
  isomorphisms — round-trip `#guard`s are their proof.
- **Structural-iso DERIVATION** (normalize type-algebra + generate the conversions, handling recursion/μ) is a
  genuine research feature — Fiore et al.'s decidable type-isomorphism is the reference. Post-v1.

**Blocked on**: nothing for the witnessed form (bite-2 laws suffice — prelude isos land now); the derived form
needs the type-algebra normalizer + a `derive Iso` metaprogram (post-v1); richer type equality (definitional
vs propositional) rides [[Q31 dependent types]].

**Revisit signal**: a `derive Iso`/`derive Codec` metaprogram is wanted (structural derivation); OR type-level
equality gets richer (Q31 refinement/dependent — `A ≅ B` as a propositional-equality proof); OR the schema
thread is taken up (type-is-schema, decoder derived — same normalize-the-structure machinery). Ties
[[Q31 dependent types]] (propositional type equality), ADR-0081 (generic-data intro — the algebraic types),
ADR-0068 (traits+laws — the witnessed-iso mechanism), ADR-0069 (data = the sum/product/μ algebra).
