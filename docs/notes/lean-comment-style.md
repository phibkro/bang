# Lean comment convention (BANG)

> The project's adopted commenting/doc convention, grounded in the
> [Mathlib documentation-style guide](https://leanprover-community.github.io/contribute/doc.html).
> The repo is already ~90% aligned (661 `/--` docstrings, 201 `/-!` section blocks,
> near-zero history-in-comments). This file records the rule + the one structural gap to close.

## The convention

```
1. /-- … -/ on every def, theorem, and content-bearing lemma. The FIRST SENTENCE is
   the CONTRACT/intent — the mathematical meaning or the invariant — a full sentence
   ending in '.'. Do NOT restate the code. Backtick `Lean.Names`; **bold** named theorems.
2. /-! ## N … -/ for section headers (atx #/##/### with the delimiters on their own lines).
   The TOP-OF-FILE BANNER is /-! # … -/ (NOT a plain /- … -/): only /-! renders into hover
   + doc-gen4, so a plain banner makes the §-map orientation INVISIBLE to generated docs.
3. -- inline ONLY for PRESENT rationale at a point of subtlety (why this cutoff, why this
   branch). Never narrate history or absence — that lives in git (CLAUDE.md doc-discipline).
4. Cross-refs (ADR-NNNN, paper keys, §N) stay — they are this repo's traceability — but go
   AFTER the contract sentence, not instead of it.
5. KEEP: the numbered §N sectioning, contract-first docstrings, near-zero history-in-comments.
   ADJUST: only rule 1's first-sentence discipline + rule 2's banner form.
```

## Why these two adjustments (the only real gaps)

- **Banner `/- → /-!`.** doc-gen4 (and `lean_hover_info` via the LSP) render `/-!` module docs but **ignore a plain `/- … -/` banner**. Our richest orientation — the `§`-maps at the top of `Core.lean`/`Spec.lean`/`Operational.lean` — is exactly there, so today it is lost to any generated/hover view. Promoting the banner delimiter surfaces it.
- **First-sentence-is-the-contract.** Some docstrings open with narrative/ADR context before the contract. Mathlib's rule (the subject leads): the first sentence should stand alone as "what this is," with the narrative/cross-refs after.

## Adoption status

- **Convention: adopted now** (this file; referenced from `CLAUDE.md` and the
  `codebase-maintenance` instance — docs rung). New/edited declarations follow it.
- **Banner promotion (`/- → /-!`): DEFERRED** — a mechanical ~20-module sweep that touches
  every `Bang/*.lean` banner. Do it as one discrete pass once the LR re-index settles (it
  would otherwise collide with in-flight proof edits). Optional enforcement later: Mathlib's
  `docBlame`/`docBlameThm` linters for docstring coverage, and/or a banner-form check.
- **Pairs with doc-gen4 / lean-lsp-mcp** (the Lean symbol-intelligence path): both consume
  `/--` + `/-!`, so this convention is what makes those tools' output rich.
