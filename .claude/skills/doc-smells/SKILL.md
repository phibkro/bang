---
name: doc-smells
description: Detect + fix "doc smells" — the documentation analog of code smells (duplication, history-in-a-status-doc, drift, god-doc, prose-duplicating-structure, orphan refs, speculative docs, wrong-altitude, contradiction). Every smell is ONE disease — a derived fact that isn't generated or tested against its source, so it drifts. Use when a doc feels bloated/stale, at the G2 CONTEXT/ROADMAP prose survey, or as a maintenance step. Fixes by climbing the derivation ladder: delete what git owns, link what SSoT owns, generate what's structured, keep only the volatile now.
---

# /doc-smells — detect and fix documentation rot

**The one idea:** docs are a **derivation of the code** (the root). A doc smell is a *derived
fact that isn't generated or tested against its source* — so it is free to drift. Every smell
below is a symptom of that one disease (a fact stuck on the **survey** rung when it could be
**generated** or **tested**), and the cure is always the same move: **climb the
derivation-strength ladder** (`generate > test > survey`) — pull each fact up a rung, don't
"write it better."

## Smell catalog (doc smell ⟷ code smell ⟷ fix)

| Doc smell | ⟷ Code smell | Detect signal | Fix (climb the rung) |
|---|---|---|---|
| **duplication / redundancy** | copy-paste (DRY violation) | the same fact stated in ≥2 docs | SSoT — one home; others **link or generate** |
| **history-in-a-status-doc** | mutable var accumulating stale state | dated "what happened" entries · a "…now also DONE" chain in a *current-state* doc | **delete** — git log / CHANGELOG / the commit own history; the "now" doc **moves** to the new edge, never grows |
| **drift / staleness** | a comment that lies · dead code | doc names a file / flag / number / status that has changed | **generate or test** the fact (a generator, or a fitness tie/link/gate check) |
| **god-doc / bloat** | god object · long method · low cohesion | one doc = position + product + plan + roster, loaded whole every time | **split by purpose** + load on-demand; leave a pointer |
| **prose-duplicating-structure** | magic numbers · hardcoding | a hand-written list restating types / an index / a table | **generate** the block from the root |
| **orphan / dangling ref** | dead link · broken import · dangling pointer | `[x](path)` / `[[wikilink]]` to a moved or deleted target | link-check / tie-validation (a **fitness test**) |
| **speculative / aspirational** | speculative generality (YAGNI) | documenting features / plans that don't exist yet, or over-detailing a future | document what **IS**; keep plans terse + falsifiable |
| **wrong-altitude (mislevel)** | leaky abstraction · wrong layer | a volatile detail in an always-loaded doc, or a core invariant buried in a note | place by **audience × temporality × frequency** |
| **contradiction** | inconsistent state · race | two docs that **disagree** (worse than duplication — can't tell which is true) | SSoT + **pick-one-flag-the-other**, never average |

## Detect — scan a target doc

1. **Name the doc's CHARTER** — its one job, from the reference index or its own header (e.g. CONTEXT = "where we are RIGHT NOW"). Every section that doesn't serve that charter is a smell candidate.
2. **For each section ask: "where is the SSoT for this fact?"** Lives elsewhere (git, the PRD, a PATH, a generated index, the code) → duplication / history / drift. Genuinely volatile-and-here → keep.
3. **Cheap grep signals:**
   - dated headers (`202\d-`) or past-tense narration in a *current-state* doc → **history** smell.
   - section names that match other docs (Product / Paths / Questions / Agents / …) → **duplication**.
   - `[...](path)` and `[[...]]` refs → run an **orphan** check (does the target exist?).
   - hand-maintained lists of structured data (ADRs, symbols, types) → **prose-duplicating-structure**.
   - length ≫ charter (a "current position" doc in the hundreds of lines) → **god-doc / bloat**.

## Fix — climb the rung, don't rewrite

- **duplication** → replace the copy with a one-line **link** to the SSoT home.
- **history** → **delete** it (the commit / CHANGELOG / git log is its record). The status doc's lead **moves**; it never accretes a chain of past edges.
- **drift** → if the fact can be generated/tested, wire that (a generator or a fitness check); otherwise fix it and record its SSoT so it can't recur.
- **god-doc** → extract each concern to its on-demand home; leave a pointer, not the content.
- **prose-structure** → generate the block from its root (types / index / table).
- **keep ONLY** the genuinely-volatile *now* — and generate even that where possible (e.g. a `just proof-state` block beats a hand-typed status line).

## Report format

Per target doc: **charter** (one line) · a table of **found smells** (smell · location · SSoT-home · fix) · the **keep** set (what genuinely belongs) · a **line-count before → projected after**. Then apply the fixes (or hand back the list if the user wants to review first).

## Anti-triggers

A doc already at its charter; a genuinely-volatile note; a "duplication" that is a deliberate
**generated** derivation (a link/ref, not a hand-copy — that's the CURE, not the smell). Scale the
pass to the rot: a lean doc needs no surgery, and surveying nothing is correct when a doc is already
one-job-clean. Do not over-prune — deleting a fact with no SSoT elsewhere is *destroying* it, not
climbing the ladder; verify the SSoT home exists before you cut.
