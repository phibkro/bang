# 0040 — Laws as first-class algebraic interfaces; proof-first discharge (amends ADR-0026)

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: Surface laws are first-class, enforced algebraic interfaces; discharge is proof-first → test → assert. Amends 0026's test-default.
- **Amends**: 0026
- **Resolves**: Q19
- **Depends-on**: 0026, 0027, 0029, 0016

- **Layer:** C (language design / discharge methodology) — the moat surface, near-permanent
- **Status:** Accepted (user-grilled, 2026-06-24)
- **Depends on:** 0026 (amends), 0027 (polymorphism staging), 0029 (ADTs), the ◊4 LR

## Context

The surface track needs a way to *write + verify* programs — the moat is "safe to generate into."
A grilling session fixed the laws surface. This ADR records it; the surface implementation lives in
`Bang/Surface/Trait.lean` (additive sugar, **no kernel change**).

## Decision

1. **Laws are first-class, enforced ALGEBRAIC INTERFACES.** A trait/interface = **operations +
   equations (laws) relating them**. A type is an *instance* iff it provides the ops AND satisfies the
   laws. Composable hierarchy by extension (`eq → preorder → order`). *Structure, not content*: the
   interface is an algebraic **theory**, instances are **models**, equivalence is up-to-the-theory
   (categorical) — which the LR underwrites (see §coherence).

2. **It is a SEPARATE CONSTRUCT** from refinement types (value-predicates `{x | P x}`) and dependent
   types (value-indexed `Vec n`). It is an *algebraic theory* (signature + equations). Lighter to check
   than refinement: a law is a discharged `Prop`, not a per-value type-predicate the checker verifies
   everywhere.

3. **Discharge is PROOF-FIRST → property-test → assert, descent EXPLICIT + MARKED** (this **amends
   ADR-0026**, which had *test*-by-default). A `Law` carries its `Prop` **and** evidence — a proof
   (`rfl`/`simp`/`grind`/`decide` by default) **or** an explicit descent marker (`test`/`assert` → a
   `Plausible` test). A law with *neither* is **unconstructible** → "no silent pass" is a **type error**,
   not a runtime check (make the bad state unrepresentable). Cost: proof-first needs automation for the
   common case — but *algebraic* laws are exactly the automatable kind, and the LR's compatibility
   machinery is the proof engine.

4. **Polymorphism: MONOMORPHIC first.** The interface hierarchy + concrete instances ship now;
   HM (generic code *over* an interface, `sort : Ordered a => …`) is the **next** surface phase
   (advances ADR-0027's mono→HM). Sequences the laws-machinery and the polymorphism lift — one hard
   thing at a time.

5. **Syntax: Rust-ish `trait`/`impl` with first-class `law` members.** Familiar ⇒ agent-generable
   (the moat); `trait`/`impl` maps cleanly to theory/model. The `$`/`!`/`with` glyphs stay reserved
   (ADR-0005/0007).

## Coherence — this is the surface of what the LR proves

The laws are the **theory**; the LR (◊4) is the **semantics** that makes "lawfully equivalent ⇒
observationally interchangeable" a *theorem*. Two models of the same theory being interchangeable
regardless of representation — "structure not content / categorical equivalence" — *is* contextual
equivalence. So: **simple algebraic laws discharge operationally** (`rfl`/`grind` on the lowered defs);
the **hard rep-independence laws use the LR**, and are unlocked by ◊4.5 (the LR completed for the
resumptive paradigms). The surface track and the LR track meet exactly at the discharge layer.

## Rejected alternatives

1. **Test-by-default (ADR-0026 original).** Makes the proof→test descent the *silent* default —
   violating the project's own "descent is explicit and marked, never silent." Flipped to proof-first.
2. **Refinement / dependent types for laws.** Wrong construct (per-value predicates vs algebraic
   equations) and heavier to check. The algebraic construct is lighter and more faithful to "structure".
3. **HM-first.** Entangles the laws-machinery with the polymorphism lift; monomorphic-first sequences
   them.
4. **Novel `theory`/`model` syntax.** Most faithful to the categorical framing, but unfamiliar ⇒ worse
   for "safe to generate into" (agents emit Rust/Haskell reliably, not bespoke syntax).

## Revisit if

- The HM phase reshapes the interface model (expected — it *adds* generic reuse on top).
- Refinement-style *conditional* laws (preconditions, e.g. `pop` on non-empty) are needed — they
  *extend* the algebraic core, not replace it.

## Consequence for ADR-0026

ADR-0026's *ladder* (verified > tested > unsafe) stands. Only the **default direction flips**: proof
is the default rung, descent to test/assert is the explicit, marked move. Amendment noted in 0026.
