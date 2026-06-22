# ADR-0027 — Polymorphism is staged: monomorphic v1 → Hindley-Milner → System F (+ effect-row + grade)

- **Status**: Accepted
- **Layer**: K+C (defines the v1 type-system scope + the staging roadmap)
- **Depends on**: 0026 (the correctness ladder — inference is a checker on it), 0001 (set-rows + the K1 unifier)
- **Date**: 2026-06-23

## Context

Design-space #1 / Q17: the kernel typing is **monomorphic** — `VTy`/`CTy` have no type variables, the
effect rows no row variables, the grades no grade variables. A multi-paradigm language eventually needs
polymorphism, *especially* **effect-row polymorphism** (`map : ∀ a b ε. (a →^ε b) → List a → List b !ε`),
without which there is no reusable higher-order effectful code — the "paradigms as libraries" thesis
needs it to be real.

The fork is *how much, how soon*. Full System F + row + grade polymorphism is the most expressive point
but carries undecidable inference (annotations everywhere) and entangles every other v1 feature.

## Decision

**Polymorphism is staged across three tiers; v1 takes only the first.**

1. **v1 / MVP — MONOMORPHIC.** The type system gains no type / row / grade variables for v1. Demo rungs
   use concrete types: rung 2's verified stack is `Stack Int`, not `Stack a`. This keeps the MVP minimal
   (invariant #7) and **isolates the data-types (Q18) + laws-surface (Q19) work from polymorphism** — the
   moat (laws between operations) needs concrete types, not generic ones.
2. **Next — Hindley-Milner** (rank-1 prenex, let-polymorphism, **decidable inference**). The point where
   "paradigms as reusable libraries" becomes real (a State library generic in the state type). Sits on the
   ADR-0026 ladder's automatic rung (inference decidable ⇒ no annotation burden).
3. **Ambitious — System F** (higher-rank / impredicative) + **effect-row polymorphism** (row variables
   `⟨e | ε⟩` over the set-rows, **cashing the existing K1 sound unifier** in `Bang/EffectRow.lean`) +
   **grade polymorphism** (`∀ q. …`, Granule-level). Higher-rank inference is undecidable ⇒ annotations
   (the ADR-0026 explicit climb).

## Why staged

1. **MVP minimalism** (invariant #7): monomorphic suffices to demonstrate the multi-paradigm thesis on
   concrete types (state cell, `Stack Int`). Polymorphism is *genericity*, not a new paradigm.
2. **Decidable-inference-first**: HM's rank-1 keeps inference automatic (the ADR-0026 "verified/auto"
   rung); System F's undecidable inference needs annotations — earn that complexity only when needed.
3. **Separation of concerns**: rung 2's data types (Q18) + laws surface (Q19) don't need polymorphism;
   deferring it unblocks rung 2 without entanglement.
4. **No wasted work, no premature wiring**: the K1 unifier is already built; effect-row polymorphism
   cashes it at the HM/System-F stage, but it stays dormant for the monomorphic MVP.

## Rejected alternatives

1. **Full System F (+ rows + grades) from v1.** *Why not*: over-scopes the MVP; undecidable inference →
   annotations everywhere; entangles rung 2's data/laws work with a hard type-system feature (invariant #7).
2. **HM in v1 (skip monomorphic).** *Why not*: even rank-1 + grade-polymorphic inference is non-trivial;
   the demo rungs (counter, `Stack Int`) don't need it; defer until reusable-library code demands it.
3. **Never add polymorphism — monomorphic + monomorphization via macros (Q20).** *Why not*: Rust/C++-style
   monomorphization (generate a copy per type, via Q20 metaprogramming) covers *some* reuse but not
   effect-row genericity or first-class polymorphic values. A partial bridge, not a replacement.

## Consequences

- **v1 = monomorphic** (PRD §6 scope). rung 2's verified stack is concrete-element — simplifies Q18/Q19.
- **Q17 resolved** (staged); design-space-map #1 → staged.
- The **K1 unifier remains dormant** until the HM/rows stage — its payoff is *scheduled*, not now.

## Revisit if

- "Paradigms as libraries" hits the duplication wall (the same handler written for `Int` and `String`) —
  promote **HM**.
- An effect-generic combinator (`map`/`fold` over an arbitrary effect row) is needed — that's the
  **effect-row-polymorphism** trigger (cash the K1 unifier).
- Grade-generic library code appears — **grade polymorphism**.
