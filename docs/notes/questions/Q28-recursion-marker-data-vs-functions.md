---
type: design-question
title: "Recursion marker: reuse `rec` for data + functions, or keep them separate?"
description: "keep data (marker-free, total) and function recursion (Div) separate; unify at the effect row"
status: decided
area: surface
resolved-by: ["ADR-0073"]
ties: ["ADR-0028", "ADR-0029", "ADR-0069", "ADR-0073"]
see-also: []
---
**Question**: when recursive FUNCTIONS land (the deferred `fix`/`Div` bullet), should the surface
reuse ONE `rec` modifier for both recursive data types and recursive functions (one construct,
multiple uses), the way some designs unify — or keep them distinct?

**Why it matters**: it is the SOUL "one construct per problem" test applied to a case where the
surface intuition (self-reference) tempts unification but the language's central axis pulls them
apart. Getting it wrong hides the total/Div seam that IS bang's identity.

**Detail** — the lean is: **keep them separate**, for three grounded reasons:
```
recursive DATA type          recursive FUNCTION
structural / well-founded    general / may not terminate
TOTAL (⊥-row, ADR-0029 μ)    DESCENDS into Div (fuel-bounded)   ← opposite sides of the seam
a value-type former          a computation-level fixpoint (fix)
```
1. **Data needs no marker at all** — ADR-0069 auto-detects recursion (the type's own name in a
   payload position IS the recursion, auto-μ-wrapped). A `rec` there is redundant.
2. **Functions DO need a marker** — to bring the name into scope in its own body. Different NEEDS ⟹
   not really one construct.
3. **`rec` is the wrong cut even for functions** — the load-bearing distinction is STRUCTURAL
   recursion (total, stays ⊥-row) vs GENERAL recursion (Div); `rec` blankets both.

**The constructive unification** (more on-thesis than a shared keyword): unify at the EFFECT-ROW
level — *recursion that can't be shown to terminate introduces `Div`*. Data contributes nothing
(total by construction); function recursion contributes `Div` unless structural. The row carries the
distinction (the generative constraint the type system reasons about), not a cosmetic keyword.

**Options**: (1) **separate + row-level unification** (recommended: `data` marker-free; recursive
functions signal generality via `Div` in the row). (2) shared `rec` modifier on both (surface
uniformity, but conflates the seam). (3) Lean-style separate keywords (`inductive` vs a recursive
`let`) — but bang's `data` already needs no keyword, so this is (1) without the row insight.

**Blocked on**: the recursion/`fix` bullet existing at all (not yet implemented; deferred from
ADR-0069's scope note). This is a design pin to apply THEN.

**Revisit signal**: starting the recursion bullet (`fix` + the `Div` row); or a request for
structural-recursion totality checking (which is where the structural-vs-general cut becomes real).
