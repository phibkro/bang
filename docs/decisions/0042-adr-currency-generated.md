# ADR-0042 — The ADR decided-ledger is generated from frontmatter (drift unrepresentable)

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: The ADR index + resolved-questions ledger is GENERATED from per-ADR frontmatter; onboarding consults the generated ledger before opening a design question.
- **Depends-on**: 0026

- **Layer**: C (tooling / doc-discipline — the decided-ledger's single source of truth)
- **Date**: 2026-06-24

## Context

The "what's-decided" ledger lived in **two** hand-maintained places —
`docs/decisions/README.md` (the index table) and `docs/notes/OPEN_QUESTIONS.md`
(the per-question statuses) — both *copies* of facts whose authoritative home is
the individual ADR files. Two copies of a fact is a representable illegal state
(the DB update anomaly): they drift.

They did. **Q19** was marked `· OPEN` in OPEN_QUESTIONS even though **ADR-0040
resolved it** — and the README's own prose said 0040 "Answers Q19". A grilling
session then re-derived an already-decided question because the ledger lied.
(The same sweep surfaced two more: Q3 and Q8 had `✓ RESOLVED` body headers but
stale `OPEN`-less index lines.) This is exactly the failure CLAUDE.md's
"Single source of truth" + the generate>test>convention ladder exist to prevent.

## Decision

The decided-ledger is a **pure function of the ADR frontmatter** — generated, not
hand-maintained. Drift moves from "caught if someone notices" to **unrepresentable**.

1. **Frontmatter schema.** Each `docs/decisions/NNNN-*.md` carries a machine block
   after its H1, fenced by `<!-- adr-frontmatter -->`:
   `Status` · `Summary` · `Supersedes` · `Amends` · `Resolves` (Q-numbers) ·
   `Depends-on`. Inverse links (Superseded-by, Amended-by) are **not declared** —
   the generator derives them from other ADRs' `Supersedes`/`Amends`. The ADR
   **body** stays the source of truth for the full rationale; the frontmatter is
   the one-line + relationship projection of it.
2. **The generator** — `tools/gen-adr-index.py` — parses the frontmatter +
   H1 title, derives inverse links, and emits the index table + a
   resolved-questions table into the README between
   `<!-- BEGIN/END GENERATED ADR INDEX -->` markers (hand-written preamble above
   the markers is preserved). It is idempotent and supports `--check`.
3. **The gate.** `just adr-check` runs `--check`: (a) the README generated region
   matches a fresh regen; (b) a **bidirectional cross-reference** — every Q
   marked `✓ RESOLVED (ADR-n)` in OPEN_QUESTIONS declares `Resolves: Qn` on
   ADR-n, and every ADR `Resolves: Qn` corresponds to a non-OPEN Qn; and (c) a
   **Status-consistency** leg — an ADR's machine-frontmatter Status must agree
   (first word) with its prose `**Status**` narrative bullet, since the two are
   two copies of a fact that changes (Accepted→Superseded). Wired into
   `just verify`. (b) is the exact check that would have failed on the Q19 drift;
   (c) guards the residual dual-Status copy the frontmatter sweep introduced.
4. **Onboarding trigger.** Before grilling or opening a design question, read the
   generated ledger first — a question with an ADR is closed (CLAUDE.md doc
   discipline + `development-lifecycle.md`).

## Why this model

- **The top rung of the ladder.** `generate` makes drift unrepresentable;
  `test` (the `--check` gate) catches it at CI; `convention` (hand-sync) is the
  anti-pattern we were on. We now run the top two rungs, not the bottom.
- **The ADR body stays canonical.** The frontmatter is a *projection*, not a
  second copy of the rationale — the rich "why" remains in the body where it is
  the only copy.
- **Lenient parser, mechanical rewrite avoided.** The H1 forms (`ADR-N ·`,
  `ADR-N —`, `N —`) and bullet styles (`**Status:**` vs `**Status**:`) varied
  across 33 ADRs; the parser normalises them, so the sweep only *adds* a clean
  frontmatter block rather than rewriting every header.

## Rejected alternatives

- **Test-rung only** (keep both hand-maintained tables, add a lint that they
  agree) — rejected: it catches drift but still keeps two copies of the fact, so
  a writer must remember to update both. `generate` removes the second copy.
- **Convention only** (a doc-discipline note saying "remember to update the
  index") — rejected: this is the regime that produced the Q19 drift. Hope is not
  a mechanism.
- **Bulk-load all ADRs into context** (skip the ledger; let a session read every
  ADR to learn what's decided) — rejected for **Context Rot**: ~42 ADRs of
  coherent prose dilute attention more than a compact generated table, and cost
  the token budget. The generated ledger is the progressive-disclosure index;
  the bodies are pulled on demand.

## Revisit if

- The frontmatter schema can't express a relationship that recurs (e.g. a
  *partial* supersession — currently kept in prose, as with ADR-0023's "supersedes
  ADR-0022 **D3**" only — would want a first-class field if it recurs).
- ADRs move out of `docs/decisions/` or stop being one-file-per-decision.
- A second consumer of the frontmatter appears (e.g. a docs site), which would
  argue for emitting structured data (JSON) the README renders from, not just the
  README table.
