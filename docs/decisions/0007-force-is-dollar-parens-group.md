# ADR-0007 · Force is `$`; parens group without forcing; fixed global precedence

- **Status:** Accepted
- **Date:** 2026-05-31
- **Supersedes:** the force-notation portion of ADR-0005 (which tentatively kept `!`)
- **Related:** 0005 (reactive sampling notation), 0006 (same no-hidden-assumptions principle, applied to the operator grammar); CBPV foundation; algebraic-effects/actor lineage (frees `!`)

## Context

Force is the surface mark for the CBPV description→value kind-shift — the most-used, most load-bearing operator in the language. Two candidates were open: `!x` prefix (`design.md`) and `(x)` surrounding (`description-value.md`). Separately, weak/implicit precedence and user-defined fixity are **non-local parse dependencies** (you can't resolve `a ⊕ b ⊗ c` without knowing declarations possibly from another module) — the same hidden-channel problem ADR-0006 evicted from closures, sneaking back through the operator grammar.

## Decision

Three coupled parts:

1. **Force is `$` (prefix).** `$x` forces a name, `$(e)` forces a grouped expression, `f $(g x)` applies `f` to the *value* of `g x`.
2. **Parens `( )` group *without* forcing** — pure structure, no kind-shift. `(a + b)` is the *description* of `a + b` (still lazy). Grouping and forcing are distinct glyphs doing distinct jobs.
3. **Precedence is a fixed global builtin table; no user-defined fixity.** Bare `a + b * c` parses via the table; explicit grouping parens override it.

## Rationale

- **Collision-free.** `$` has no unary meaning in the C/ML/Haskell families, so `$x` never needs *type* to disambiguate it from `not` (the `!x` problem — type-dependent, non-local). And it **frees `!` for actor-send** (`c ! msg`, the library-lineage idiom), clearing the cross-lineage glyph clash.
- **`$` already connotes the right thing.** Shell `$x` = "value of x"; Haskell `$` = "apply". Both human and agent priors read `$x` as "the value of x" — exactly the kind-shift. A prefix sigil announces "operator applied, kind changed" (the CBPV legibility criterion) better than parens, which whisper "grouping".
- **Group-vs-force separation is the cleanest resolution of the whole syntax thread.** The two jobs that kept colliding — *structure* (no kind-shift) and *forcing* (the kind-shift) — get distinct glyphs; neither overloads the other. Every paren is pure structure; every `$` is pure kind-shift.
- **Explicit grouping + fixed table = the operator-grammar instance of no-hidden-assumptions.** Precedence becomes global knowledge (like C), resolvable locally; per-module fixity (the actual non-locality) is banned. Same principle family as ADR-0006.

## Rejected alternatives

| option | why not |
|--------|---------|
| `!` as force | collides with unary `not` → type-dependent local disambiguation; also wants the actor-send glyph. `$` clears both |
| `(x)` surrounding-parens force (full Lisp) | forcing = grouping ⇒ can't build a grouped *description* without forcing it; drags in no-precedence-rules (everything fully parenthesized) |
| weak / implicit precedence (no explicit grouping) | non-local parse dependency; the reported "just makes things weird"; violates no-hidden-assumptions |
| user-defined fixity (Haskell-style) | fixity declared elsewhere = non-local parse; keep a fixed builtin table instead |
| eager-default + trailing `name()` force | flips the thunk axiom to eager — a separate, larger decision, not on the table here |

## Consequences

- The **description→value boundary is exactly the set of `$` sites** — greppable, themeable, the language's central distinction made visible.
- **Cost:** `$` is visually quieter than `!` (whispers "value" vs `!`'s "consequences happen here"). Recover prominence via **editor theming** (highlight force points), not glyph drama.
- **Three shapes, three meanings:** `(e)` group, stay a description (lazy) · `$x` force a name · `$(e)` group then force.
- **Reactive sampling notation (ADR-0005) is now `x = $y`** (sampled) vs `x = y` (live). Note: `x = (y)` *groups* y and stays live — parens do **not** force — so it is **not** a sample. (0005 updated.)
- **Actor-send keeps `!`** as visibly *library* sugar, distinct from core force `$`.
- **String interpolation must avoid `$`** (reserved for force). Use `\(expr)` (Swift-style), as the design doc already did (`"count: \(n)"`), not `${expr}`.
- The spec owes a **published precedence table**; it is global knowledge, like C's.

## Revisit if

- The fixed table proves too restrictive for a domain wanting custom operators → consider **scoped fixity that travels with the operator's import** (still local if the fixity is imported alongside the operator), never free-floating per-module fixity.
- `$`'s quietness causes force points to be missed in real code → reconsider a louder glyph — but **not** `!` (the `not` collision stands).
