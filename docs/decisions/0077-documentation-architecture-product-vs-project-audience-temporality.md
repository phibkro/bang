# ADR-0077 · Documentation architecture: product vs project docs, placed by (audience × temporality) — a doc's home, lifecycle, and maintenance rung follow from its coordinate

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: Documentation is placed on two axes — **audience** (consumer/user vs contributor/agent-builder) × **temporality** (a timeless snapshot vs time-indexed work). **PRODUCT docs** = consumer × snapshot: the artifact as-it-is, ideally GENERATED from code (can't drift), publishable (`docs/reference/language.md`, PRD, README, ONBOARDING). **PROJECT docs** = contributor × time-indexed, sub-split by TENSE: **DONE** (immutable — CHANGELOG, ADRs = a past decision + rationale, git history), **NOW** (volatile — CONTEXT, active `paths/`), **NEXT** (revisable — ROADMAP, the OKF question ledger, project-roadmap). A doc's (audience, tense) coordinate determines its home, lifecycle, and maintenance rung. Conflating coordinates (a "future feature" line in the product reference, a "current status" line in a timeless doc) is a category error that drifts. This makes EXPLICIT the taxonomy already implicit in the repo's doc-discipline rules.
- **Depends-on**: 0076, 0026
- **Relates-to**: ADR-0078 (where knowledge lives — the sibling "git-native" decision), Q34 (module docs), the OKF question ledger (`docs/notes/questions/`), CONTRIBUTING.md (operationalizes this for new teammates)

- **Status:** Accepted (operator-approved 2026-07-07)
- **Date:** 2026-07-07
- **Layer:** meta / documentation architecture (no code; governs where docs live + how they're maintained)
- **Builds on:** ADR-0076 (tooling by construction — product docs are GENERATED from code, a pure derivation), ADR-0026 (stratification — the same verified-core/tested-superset shape recurs: product = the stable published face, project = the moving work behind it). Lineage: Diátaxis (the product-doc quadrants: tutorial/how-to/reference/explanation); the repo's own CLAUDE.md doc-discipline rules (history→git · volatile→CONTEXT · decisions→ADR · always-useful→CLAUDE.md).

## Context

Documentation grows unruly and drifts. The repo already has doc-discipline rules (CLAUDE.md: "History lives
in git, not docs"; "Volatile state → CONTEXT"; "Genuine decisions → ADR"; "Always-useful → CLAUDE.md";
"On-demand → docs/notes") — but they're an IMPLICIT taxonomy, applied by feel. Migrating the design-question
ledger to OKF files (one file per question, generated index) forced the question the rules never named
outright: **where does a given piece of documentation belong, and why?** Answering it once, explicitly,
tells every future doc (and every new teammate) where to go.

## Decision

Place documentation by two axes:

```
                 PRODUCT (the artifact, a snapshot)        PROJECT (the work, time-indexed)
audience          consumer / user                           contributor / agent-builder
temporality       timeless per version                      has a TENSE (past / now / next)
maintenance       GENERATED from code (drift unrepresentable) past=immutable · now=volatile · next=revisable
publishable?      YES — the consumer-facing face            mostly internal working knowledge
lives in          docs/reference/ · PRD · README · ONBOARDING ┌ DONE:  CHANGELOG · ADRs · git history
                                                             ├ NOW:   CONTEXT.md · active paths/
                                                             └ NEXT:  ROADMAP · OPEN_QUESTIONS (OKF ledger) · project-roadmap
```

- **A doc's home = its (audience, tense) coordinate.** That coordinate also fixes its LIFECYCLE (product
  regenerates with the code; project-DONE is immutable-once-written; project-NOW is volatile; project-NEXT
  is curated) and its MAINTENANCE RUNG (product → generate; project-DONE → git preserves it; project-NOW →
  hand-update; project-NEXT → curate + validate).
- **Frontmatter convention.** Where a doc is structured (the OKF ledger, ADRs), it may carry `layer:
  product | project` and a tense marker. The question ledger already carries `status: open | decided |
  superseded` — which IS the tense (open = NEXT, decided/superseded = DONE). Views generate off it.
- **The physical tree split** (`docs/product/` vs `docs/project/`) is the natural endpoint but is DEFERRED:
  the taxonomy + the frontmatter convention are the decision; the file moves are a mechanical follow-up.

## Rejected / not-now

- **One undifferentiated docs pile** — the status quo that drifts; a doc with no coordinate has no home,
  no lifecycle, no maintenance owner.
- **A full `docs/product/` ↔ `docs/project/` tree reorg NOW** — deferred. Pinning the taxonomy + frontmatter
  convention is cheap and immediately useful (it tells you where new docs go); the physical move touches
  every path-ref and is best done as its own pass.
- **Treating ADRs as product docs** — an ADR is project/DONE (a past decision + rationale, contributor-
  facing), not a consumer snapshot. It's referenced forward but authored once, immutably.

## Consequences

- Every new doc gets a coordinate → a known home, lifecycle, and maintenance rung. No more "where does this
  go?" by feel.
- Product docs stay GENERATED (the snapshot can't drift from the code); project-DONE stays in git (history
  preserved); project-NOW stays thin + volatile (CONTEXT); project-NEXT stays curated + validated (the OKF
  ledger with its tie-graph).
- Directly informs `CONTRIBUTING.md` (a new teammate learns the map: use-it → product; build-it → project,
  and which tense).

## Revisit if

The physical `docs/product/` ↔ `docs/project/` split is undertaken (decide the tree + repoint refs); OR a
consumer-facing documentation SITE is built (GitHub Pages over the product docs — the product face
published, still git-native — see ADR-0078).
