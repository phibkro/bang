# 0047 — The sugar surface: dialects + user-extensible macros, one mechanism, safe by core-recheck

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: The sugar surface (ADR-0046's "language API") is a layer of DETERMINISTIC ELABORATORS to the canonical core. ONE mechanism serves both DIALECTS (curated sugar bundles — v1 ships a single C-like one, in the Rust/Zig/Gleam family) and USER MACROS (ad-hoc, post-v1). Safe by construction: the core RE-CHECKS every elaboration, so untrusted user sugar can produce at-worst a wrong-but-core-checked program, never an unverified one; and the lexical-capability discipline (ADR-0045) gives effect-hygiene for free. The load-bearing cost is AMBIGUITY DETECTION — every surface program has a UNIQUE elaboration or a LOUD ERROR, never a silent pick. v1 ships a fixed C-like dialect (ambiguity = an unambiguous grammar, easy); user-extensible sugar is post-v1, and the cheapest way to keep it unambiguous is keyword-led macros.
- **Depends-on**: 0046, 0045, 0026

## Context

ADR-0046 fixed the architecture: a canonical explicit core + an inference-bridged sugar surface, with the elaborator as tested-not-verified shell and "no-ambiguity = deterministic-or-loud-error". It left open what the *sugar* looks like, whether there can be MULTIPLE surface forms, and whether userland can WRITE sugar.

## Decision

1. **Default dialect: C-like (Rust/Zig/Gleam family).** The sugar surface is the concision mode for humans, so familiarity is the right optimisation — `with h { … }` handler blocks, `match` for case/split, `{}`/`$` (or `!`) for thunk/force, method-/`perform`-style effect calls. The skin is familiar; the elaboration carries the CBPV/effect truth.

2. **Dialects are free.** A dialect is *just* a deterministic front-end to the shared core. So multiple dialects (Rust-like, Gleam-like, S-expr-direct) can coexist, all targeting the same canonical terms — **interoperable by construction**, because they mean the same thing (their elaborations). The core is the lingua franca. Precedent: Racket's `#lang`.

3. **One mechanism, two scales.** A dialect is a *curated bundle* of sugar shipped with the language; user-sugar is the *same elaboration mechanism*, ad-hoc and user-authored. We design ONE layer (the elaboration/macro system) and dial how much is shipped vs user-extensible — not two systems.

4. **Safe by core-recheck.** Sugar (shipped or user) is untrusted SHELL. The core re-checks the elaboration output (type-check + verify), so a buggy or hostile macro produces at-worst a *wrong-but-core-checked* program — never an unverified or unsafe one. This is ADR-0026 stratification: sugar in the tested superset, the core the verified floor; a macro lives entirely in the superset and the core is the immovable backstop. ("Racket's extensibility, with a verified backstop Racket lacks.")

5. **Effect-hygiene for free.** The hardest part of macros-over-effects is accidental handler capture. The lexical-capability discipline (ADR-0045) forbids it structurally — dispatch is lexical and the elaborator resolves caps deterministically, so a macro-introduced `perform` cannot accidentally bind to a user handler (nor vice-versa). `no_accidental_handling` extends to macros at no cost.

6. **Ambiguity detection (the load-bearing cost).** Every surface program elaborates to a UNIQUE core term or raises a LOUD ERROR — NEVER a silent pick. Ambiguity arises in parsing (precedence/associativity) and in rule-overlap (two sugars matching the same form). Resolution: **structural avoidance** where possible (an unambiguous dialect grammar — LR-checked, no conflicts; keyword-led macros — distinct lead keywords make overlap impossible), **detect-and-reject** where not (static overlap-detection + precedence declarations for general infix operators). PEG-style ordered-choice "first match wins" is FORBIDDEN — it silently disambiguates, which an agent cannot predict and which hides a real "two meanings" error.

7. **v1 scope.** v1 ships ONE fixed, closed, tested C-like dialect (a parser/desugarer + the existing cap-assignment elaborator). User-extensible sugar (the macro system + general ambiguity detection) is POST-v1 — the architecture is ready for it; it is not a v1 build.

## Rejected alternatives

- **Sugar primitives in the core.** Violates ADR-0046 (sugar never enters the core) — bloats the verification surface and ends the "true shape" guarantee.
- **PEG / ordered-choice silent disambiguation.** Picks the first matching rule, hiding ambiguity. Violates deterministic-or-loud-error: unpredictable for agents, and it swallows a genuine error.
- **A single fixed surface (no dialects, no extensibility).** Simpler, but forecloses language-oriented programming — which this architecture makes *free and safe*, so the cost of forbidding it is unjustified.
- **Verifying the elaborator / macros.** Too complex to verify; the core-recheck is the correct backstop (tested-not-verified, ADR-0046). Verifying the macro layer would be effort spent where the core already guarantees safety.

## Consequences

- v1 surface = the C-like dialect; the verification spine is untouched (sugar adds no semantics — ADR-0046).
- **The agent ecosystem is insulated from user-sugar:** agents work at the core (inspectable, generable) and never need to understand a human's macros. User-sugar is a human convenience that cannot fragment the agent story.
- **Ambiguity detection is the one mechanism the architecture demands that we do not yet have.** It is the design priority when user-sugar is built; keyword-led macros are the cheapest structural avoidance and the recommended starting point.
- Dialects interoperate by construction (shared core), so a multi-dialect ecosystem does not fragment meaning.
