# ADR-0007 · Force is always explicit; grouping ≠ forcing; operator precedence is global

- **Status:** Accepted
- **Date:** 2026-06-21 (rewritten from earlier glyph-specific version of 2026-05-31)
- **Layer:** K (kernel — semantic decisions; surface spellings are liquid)
- **Related:** 0005 (reactive sampling reuses explicit force; same operator-grammar family), 0006 (the no-hidden-channels principle, applied here to grammar), CBPV foundation

## Context

CBPV makes description-vs-value a *kind shift* that must be marked. Two semantic questions had to be settled at the kernel level:

1. Is the description → value boundary always explicit, or can it be implicit (e.g., parens force, as in some Lisps; or function application implicitly forcing its argument)?
2. Can the operator-precedence table be modified per-module, or is it fixed globally?

Both questions are about whether reading code requires non-local knowledge — the same hidden-channel problem ADR-0006 evicted from closures, sneaking back through the grammar.

## Decision (semantic — K-layer)

1. **Force is always explicit.** A single distinguished syntactic mark performs the description → value kind-shift. Nothing else implicitly forces — not application, not grouping, not equation, not pattern match.
2. **Grouping and forcing are distinct.** Pure structural grouping does NOT force. A parenthesized expression remains a description until explicitly forced.
3. **No user-defined operator fixity.** Operator precedence is a fixed global table (like C). Per-module / per-import precedence redefinition is banned; it makes parsing non-local.

## Rationale

- **Explicit force = the central CBPV distinction is visible at every site it occurs.** Greppable. No type-dependent local disambiguation (the failure mode of `!x`-style force colliding with `not`).
- **Grouping-vs-forcing separation** cleanly resolves the syntax tension: the two jobs (structure / kind-shift) get distinct treatments; neither overloads the other.
- **Fixed global precedence + explicit grouping = the operator-grammar instance of no-hidden-assumptions.** Same principle family as ADR-0006 (capture). Precedence becomes global knowledge (like C); per-module fixity (the actual non-locality) is banned.

## Rejected alternatives

| option | why not |
|--------|---------|
| Implicit force (grouping = forcing, full-Lisp style) | Can't build a grouped *description* without forcing it; drags in no-precedence-rules (everything fully parenthesized) |
| Weak / implicit precedence | Non-local parse dependency; violates no-hidden-assumptions |
| User-defined fixity (Haskell-style) | Fixity declared elsewhere = non-local parse; keep a fixed builtin table instead |
| Eager-by-default + trailing-mark force | Flips the thunk axiom to eager — a separate, larger decision, not on the table here |

## Consequences

- The description → value boundary is exactly the set of explicit force sites — greppable, themeable, the language's central distinction made visible.
- **Three semantic shapes:**
  - pure group (still a description; no kind-shift)
  - force-a-name (kind-shift on a name)
  - group-then-force (kind-shift on a composite expression)
- **Sampling notation (ADR-0005) is force-in-equate-position** — falls out of force meaning what it already means.
- The spec owes a **published precedence table.** Global knowledge, like C's.

## Current surface spelling (liquid — S-layer, not load-bearing)

The current surface chooses `$x` prefix for force, `(e)` for pure grouping, `\(e)` for string interpolation (so `$` stays reserved for force), and `!` is freed for actor-send. These glyphs may change as the surface evolves; the K-decision is that the force boundary is explicit and global precedence is fixed — not which characters spell it. See `ROADMAP.md` for the surface-layer liquidity policy.

## Revisit if

- The fixed table proves too restrictive for a domain wanting custom operators → consider **scoped fixity that travels with the operator's import** (still local; fixity arrives with the operator, never free-floating per-module).
- The current force glyph causes force points to be missed in real code → reconsider the surface spelling at the S-layer (does NOT require a K-ADR change; the semantic commitment stands).
