# ADR-0068 · Surface trait/impl wiring — tested-rung ceiling for source laws, structural keying, resolution as elaboration

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: The #24 parser↔Trait↔checker wiring, three decisions: (1) a law parsed from SOURCE lands on the tested rung by construction in v1 (decidable predicate over kernel runs, checked sample, rung DISPLAYED) — the verified rung stays Lean-level; a later meta-elaborator lifts the ceiling without syntax changes. (2) Instances are keyed on STRUCTURAL types (`impl Add for (Int, Int)`) — nominal keying arrives with #23. (3) Operator resolution is a type-directed ELABORATION pass over a decl-prelude program (`Prog = decls + body`) behind a NEW typed entry point; the untyped path is untouched.
- **Resolves**: the #24 wiring fork (the handoff's predicted representation choice)
- **Depends-on**: 0040, 0066, 0029, 0067

- **Status:** Accepted (operator-ratified 2026-07-05)
- **Date:** 2026-07-05
- **Layer:** C (surface design — the moat's law surface meets the type layer)
- **Builds on:** ADR-0040 (laws as algebraic interfaces, proof-first — the design this WIRES; its
  discharge ladder is unchanged). ADR-0066 (the bidirectional checker whose inferred types drive
  resolution). ADR-0029 (structural products — the v1 instance keys). ADR-0067 (the carrier is
  unbounded ℤ, so the demo instance's laws hold without width caveats).

## Context — the pipeline is pure functions; proofs are not data

ADR-0040 + `Bang/Frontend/Surface/Trait.lean` discharge laws with **Lean proof terms**
(`Evidence.proof (h : ∀ x, pred x)`, written by tactics at Lean elaboration). The surface pipeline
(`parse → synthSC → lower → eval`) is **pure functions over data** — a `law` parsed from BANG source
text cannot produce a `Prop` + tactic proof; there is no metaprogram in the pipeline. Wiring #24
therefore forces three choices the handoff predicted: what evidence a parsed law carries, what an
instance is keyed on, and where resolution rewrites terms.

## Decision

1. **Source-law evidence: the tested rung is the v1 CEILING, by construction and displayed.**
   A parsed `law` elaborates to a decidable predicate over KERNEL RUNS (`Source.eval` the oracle,
   per Trait.lean §3's `runBool` idiom), checked on a sample — i.e. `Evidence.tested`, the `holds`
   field discharged by `decide`. The rung is REPORTED in the checker/display output, so the descent
   is visible, never silent: it is the honest ceiling of a language that has no proof-term syntax
   yet ("programs are proofs" arrives exactly when this ceiling lifts). The VERIFIED rung remains
   reachable by providing the instance at the Lean level (`Trait.lean`'s `intOrder` style).
   ADR-0040's proof-first default is preserved where proofs can be written — Lean — and the
   stratification principle (verified core / tested superset / explicit seam) now governs laws too.
2. **Instance keying is STRUCTURAL in v1.** An `impl` targets a type expression over the existing
   structural grammar — `impl Add for (Int, Int)` keys on `.prod .int .int`. The northstar demo is
   `(1,2) + (3,4) ⟶ (4,6)` with checked laws: same moat content, zero dependency on #23 (named
   type declarations). Nominal keying rides on top when #23 lands.
3. **Resolution is a type-directed ELABORATION pass, behind a new typed entry point.** Programs
   grow a decl PRELUDE — `Prog := (decls : trait/impl list) × (body : Surf)`; the elaborator
   collects an instance environment from the decls and rewrites `binopS` on non-Int operands into
   an application of the resolved instance op, using `synthSC`'s inferred operand types. This is a
   NEW entry point (`runTyped`-style); the untyped `parse → lower → eval` path is untouched, so the
   whole existing corpus is stable and the typed/untyped seam stays visible. `TypeCheck.lean` stops
   being a leaf on the typed path only.

**v1 scope notes** (deferred, not decided against): trait *hierarchy* in source syntax (`trait
Order : Preorder` — Lean-level extension exists; source-level extension is a follow-up); law-body
*implication* (`=>`) — v1 law bodies are Bool-valued expressions, so equations come free via `==`.

## Rejected alternatives

- **Meta-elaborator first** (a `#bang_trait`-style elab command discharging obligations by an
  auto-tactic bundle, reaching the verified rung from source). Deferred, not refuted: it is the
  designed ladder CLIMB (ADR-0026) and changes no syntax — but it makes the auto-tactic set
  load-bearing, pulls the pipeline into metaprogramming, and blocks piece 1 on machinery the demo
  doesn't need.
- **Parse ops only, laws stay Lean-level.** Guts the moat demo — "laws checked from source" is the
  point of #24.
- **Nominal keying first.** Blocks on #23's decl layer for zero additional demo content.
- **Mutating the untyped path** (making `lower` type-directed in place). Breaks corpus stability
  and blurs the typed/untyped seam the stratification principle wants explicit.

## Consequences

- Piece 1 (parse `trait`/`impl`/`law` into decl forms + the `Prog` prelude shape) is
  syntax-stable across all the above — safe to build immediately.
- Piece 2 = instance environment + the elaboration pass + `runTyped`. Piece 3 = the `(Int, Int)`
  Add instance with laws checked and displayed, guards flowing into the generated reference.
- The display layer gains a rung marker (law name + `✓ proof`/`↓ tested`), extending `showType`'s
  visibility contract from effects to evidence.

## Revisit if

- The meta-elaborator climb lands (source laws reach the verified rung) — clause 1's ceiling note
  becomes historical.
- #23 lands nominal types — clause 2 gains nominal keys alongside structural ones.
