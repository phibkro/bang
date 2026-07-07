---
type: design-question
title: "Proving in bang — parametricity gives free substitutability NOW; Curry-Howard/dependent types make bang a prover LATER"
description: "Two levels of proof. Substitutability/uniformity: FREE from parametricity (Reynolds' abstraction theorem — a parametric client can't distinguish instances of an interface; the type IS the proof), already latent in bang's polymorphism. Arbitrary propositions: needs dependent types (Curry-Howard: propositions-as-types, proofs-as-programs) — the Q31 far end, where a bang program IS a proof."
status: open
area: type-system
ties: ["Q31", "Q41", "ADR-0075", "ADR-0081"]
see-also: ["Reynolds 1983 (abstraction theorem)", "Wadler — Theorems for Free", "Curry-Howard", "Q41 type isomorphism", "the stratification principle (verified core)"]
---

**Question**: can bang PROVE things? Does that require "logic as a programmable feature"? (Raised via: "if a
conversion to the abstract shape is provided, shouldn't two instances satisfying that shape be substitutable
when only the shape is required? — you lose specific info but retain the generic structure.")

**The answer is TWO levels:**
```
substitutability / uniformity   FREE from PARAMETRICITY — the type IS the proof, no new feature   [bang has this NOW]
arbitrary propositions          needs DEPENDENT TYPES (Curry-Howard: propositions-as-types)        [Q31 far end]
```

**The operator's insight IS a real theorem — Reynolds' ABSTRACTION THEOREM (parametricity / representation
independence; Wadler's "theorems for free"):**
```
a generic client that uses ONLY the abstract shape is PARAMETRIC — it cannot inspect the concrete type,
  only call the interface's operations
  ⟹ it CANNOT distinguish two instances satisfying the interface
  ⟹ they are SUBSTITUTABLE   ("lose specific info, retain generic structure" = the forgetful map to the interface)
```
PRECISIFICATION (owed for correctness): it is NOT the conversion ALONE that proves it — it is parametricity
(the client uses only the interface) PLUS the conversion being a LAWFUL HOMOMORPHISM (it preserves the
interface's operations + laws). The conversion witnesses "this concrete thing IS an instance of the shape";
parametricity guarantees the client respects only the shape. A law-BREAKING conversion would let the client
observe the difference. Given both, substitutability is the theorem.

**bang already EARNS these proofs.** Everything from bite-0 through #55 is PARAMETRIC polymorphism, so the
abstraction theorem applies: a generic bang function proves its own UNIFORMITY. `map : (a→b) → List a →
List b` cannot inspect `a`, so it MUST treat every element uniformly — a proven property carried by the type,
no proof written. That is "logic as a programmable feature" in latent form: the type system discharges
substitutability for free. (This is the type-level twin of [[Q41 type isomorphism]] — an iso is a proof of
type equality; parametricity is a proof of client-indistinguishability.)

**Full proving = CURRY-HOWARD.** To prove ARBITRARY propositions, climb to dependent types (Q31's Nat →
refinement → dependent road): a PROPOSITION is a TYPE, a PROOF is a PROGRAM of that type. Then a well-typed
bang program IS a proof, and bang can prove things about ITSELF. It fits the thesis: a proof becomes a
first-class DESCRIPTION (of why a proposition holds), forced with `$` like everything else. Today the KERNEL
is proven in Lean (the metalanguage); Curry-Howard would give bang's OWN type system that power (the object
language becomes a prover).
```
parametricity   (HAVE)   free theorems: uniformity · substitutability-through-an-interface — the type is the proof
refinement      (Q31)    types carry constraints ({n : Nat // n < 10}) — proofs ABOUT values
dependent       (Q31)    propositions-as-types — a program IS a proof — bang becomes a prover
```

**Blocked on**: nothing for the parametricity level (it's a metatheorem about the existing type system — could
be DOCUMENTED/exploited as free theorems now); the full-proving level needs dependent types (Q31, post-v1,
research). Performance/soundness of the kernel is unaffected (this is object-language proving, orthogonal to
the Lean-verified core).

**Revisit signal**: free theorems are wanted as a TOOL (e.g. a parametricity-derived optimization or a
substitutability check); OR dependent types are taken up (Q31) — then propositions-as-types makes bang a
prover; OR [[Q41 type isomorphism]] gets a propositional-equality form (an iso as a proof term). Ties
[[Q31 dependent types]] (the road to full proving), [[Q41 type isomorphism]] (proof of type equality),
ADR-0075 (parametric polymorphism = the source of free theorems), ADR-0081 (generic data — the parametric
values).
