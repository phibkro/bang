# ADR-0026 — Correctness is a dispatched ladder; the kernel defines semantics, checkers are a pluggable layer

- **Status**: Accepted
- **Layer**: K+C (defines the kernel boundary + the verification methodology)
- **Depends on**: 0016 (two-hop), 0024 (◊2 gate), Q15, Q16
- **Date**: 2026-06-23

## Context

The keystone of the design-space survey (`docs/notes/design-space-map.md` #2): **how much proof power
lives in the type system, and via what mechanism?** The field offers three points — full dependent
types (Agda/Idris/Lean), refinement + SMT (F\*/Liquid Haskell/Dafny/Verus), graded-only (Granule, and
what bang has today).

Two facts force the answer:
1. The moat (PRD §2) is *"proof by construction, like Rust's memory safety"* — **sound, automatic,
   structural**. Not "write Agda proofs by hand."
2. The practical way to state a user-level law (`Decode ∘ Encode == id`, `Monoid` associativity) is an
   **assertion + property test** over arbitraries — cheap, practical, **unsound** (it samples).

Those collide unless correctness is *tiered*. And the same tiered structure already recurs across the
project: Q15's staging stages, Q16's oracle gradient (proof > differential-test > fuel > foreign), and
the SOUL's own derivation ladder (generate > test > convention). It is **one ladder**, seen three
times.

## Decision

1. **One correctness ladder, dispatched per obligation.**
   ```
   verified   proof — Lean export / SMT          sound,   high cost   climb when assurance demands
   tested     assertion + property test          unsound, low cost    ← DEFAULT for user laws
   unsafe     no check; oracle = differential     none,    zero cost   explicit, marked opt-out
              test vs the real thing
   ```
   Each obligation is dispatched to a rung; the rung is visible.

2. **The kernel defines semantics only; it is not a verifier.** The five primitives
   (thunk · force · effect rows · handlers · STM) define *meaning*. **Checkers** are a *separate,
   pluggable layer* that *judges* programs against specs, dispatching each obligation to a strategy
   (test │ SMT │ Lean). This keeps the trusted base minimal (invariant #5) and makes correctness
   granular and modular. (Answers Q16's "is checking the kernel's job?" — **no**.)

3. **User-law discharge defaults to assertion + property testing** — `assert (Decode ∘ Encode == id)`,
   tested with arbitraries over tractable shapes. Climb to SMT, then to proof, *per obligation*.

4. **The moat is two-level.** The kernel **floor** — resources / effects / memory, via the grades +
   type system — is verified **by construction** (sound, automatic, the Rust-like part; it never drops
   below "verified"). User **specs** sit on the ladder. The honest claim: *the dangerous stuff is
   unrepresentable-when-wrong; your domain laws are as-verified-as-you-choose.*

5. **Descent is explicit, never silent.** Drop a rung only when (a) verification is **unreasonable**
   (cost-disproportionate — SMT stalls, proof too dear), (b) **explicit developer opt-out** (a marked
   `unsafe`-like construct), or (c) the construct is **deemed unverifiable** (foreign, genuinely
   undecidable). A lower-rung construct is **marked** — the effect-row taint (Q16) carries it into the
   type, so callers see it. The firewall is the row.

## Why this model

1. **Matches the moat anchor.** "Like Rust's memory safety" = sound floor by construction + domain
   logic as-verified-as-you-choose. More credible than "everything is proven."
2. **Keeps five primitives.** Checkers out of the kernel preserve the minimal TCB; bang does not become
   a proof assistant.
3. **Unifies three ladders** already in the design (Q15 staging, Q16 oracle gradient, SOUL
   generate>test>convention) into one concept — less to maintain, one mental model.
4. **Pragmatic default, sound escape.** Property-test by default; verify on demand — the
   gradual-verification sweet spot. No unsound shortcut is *hidden* (descent is marked).
5. **Pluggable checkers evolve independently** of the semantics. A new SMT backend or tactic library
   never touches the kernel.

## What it commits to

- The kernel never grows a verifier; checkers are libraries/tools *over* it.
- An **assertion / law surface** (how a user states a law) + a **property-testing generator framework**
  (arbitraries, shrinking) become first-class *surface* concerns.
- Descent must be **type-visible** (effect-row / annotation taint) — unsafety cannot be silent.
- PRD §2/§3 sharpen from a flat "proof by construction" to **sound floor + laddered specs** (docs
  follow-up).

## Consequences for other ADRs / questions

- **Resolves** design-space #2 (the proof-power dial). **Answers** Q16's checker-location sub-question
  (separate layer). **Unifies** Q15 (staging) + Q16 (oracle gradient) under the one ladder.
- **Opens** (logged): Q17 polymorphism + effect-row polymorphism, Q18 data types, Q19 typeclasses with
  laws (the assertion/law surface), Q20 surface extensibility (pseudoinstructions via macros).
- **First data point already exists**: rung 1 (ADR-0025) — the kernel floor (state type-safety) is
  *verified* by construction; the state-cell demo is *tested* (`rfl`). The two-level split, in miniature.

## Rejected alternatives

1. **Full dependent types in the kernel** (bang becomes a proof assistant; Agda/Idris/Lean). *Why not*:
   violates five-primitive minimalism; manual-proof friction contradicts "like Rust, automatic"; huge TCB.
2. **Verification-mandatory / SMT-only.** *Why not*: undecidability + cost make 100% verification
   impractical; forces hidden unsound shortcuts; kills ergonomics. (SMT stays as a *climb* rung — only
   rejected as the *mandatory default*.)
3. **Checkers inside the kernel.** *Why not*: couples meaning with judgment; bloats the TCB; blocks
   pluggable, granular dispatch.
4. **Property-testing only, no climb.** *Why not*: unsound for the high-stakes core; the moat needs the
   by-construction floor + a verified escape.
5. **Refinement + SMT as the mandatory everyday default** (F\*-style). *Why not*: heavier than the common
   case needs; property-test is the cheaper everyday rung. SMT remains available as a climb.

## Revisit if

- A user-law class proves to *need* sound-by-default (property-test too weak) — promote SMT/proof to the
  default *for that class*.
- The pluggable-checker boundary leaks (a checker needs to change kernel semantics) — re-examine the
  kernel/checker split.
- The descent-taint proves insufficient to contain unsafety (a *silent* escape is found) — strengthen
  the firewall.
