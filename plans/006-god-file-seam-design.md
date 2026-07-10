# Plan 006: Produce the seam map for splitting the two god files (design doc only — zero code moves)

> **Executor instructions**: Follow this plan step by step. Run every
> verification command and confirm the expected result before moving to the
> next step. If anything in the "STOP conditions" section occurs, stop and
> report — do not improvise. When done, update the status row for this plan
> in `plans/README.md` — unless a reviewer dispatched you and told you they
> maintain the index.
>
> **Drift check (run first)**: `git diff --stat f1cb2cf..HEAD -- Bang/Frontend/TypeCheck.lean Bang/Backend/AbstractMachine.lean docs/notes/`
> Line numbers below will drift with any change to the two files; treat the
> section HEADERS (quoted below) as the anchors, not the line numbers.

## Status

- **Priority**: P3
- **Effort**: L (bounded: the deliverable is one design note, not a refactor)
- **Risk**: LOW (docs-only by construction)
- **Depends on**: none (but the actual split it designs must NOT begin before the parked LR census unit lands — see STOP conditions)
- **Category**: tech-debt
- **Planned at**: commit `f1cb2cf`, 2026-07-10

## Why this matters

Two modules are ~10× the repo's median module size: `Bang/Frontend/TypeCheck.lean` (5740 lines) and `Bang/Backend/AbstractMachine.lean` (6849 lines). Together they are ~40% of the codebase. Costs: navigation and review touch many subsystems at once, single-file Lean re-elaboration time grows with file size (the `just check` inner loop), and parallel agent work on disjoint subsystems inside one file forces one-writer serialization. A split executed *without* a designed seam risks the worse outcome: circular imports, types moved to the wrong stratum, or a broken import-direction invariant (there is a fitness gate, `arch-check`, enforcing import direction per ADR-0048).

This plan produces the **seam map** — a reviewed design note proposing the split boundaries, with evidence — so the eventual refactor is a mechanical, behavior-identical landing. It moves no code.

## Current state

- `Bang/Frontend/TypeCheck.lean` — checker + elaborator. Internal structure already marked by `/-! ## … -/` section headers; the major ones (from a header scan at `f1cb2cf`, with line anchors):
  - `45` The bidirectional checker (pure fragment)
  - `182` Inference types `IVTy`/`ICTy` (ADR-0075)
  - `421` HM inference substrate — unification + let-generalization
  - `1536` HKT helpers (ADR-0082)
  - `2491` Type-directed elaboration over `Surf`
  - `3120` Modules (ADR-0093) — merge-to-flat, PURE half
  - `3931` Stage ⑤c — source LAWS discharge
  - `~5200+` the `#guard` corpora (several sections)
- `Bang/Backend/AbstractMachine.lean` — evalD + the calculated machine + bridges; major headers:
  - `106` The state store (ADR-0031 D1)
  - `131` The transaction heap store (ADR-0031 D4)
  - `190` The custom store (ADR-0085)
  - `225` The denotational source `evalD`
  - `363` The machine — derived, not designed
  - `545`–`703` Store ↔ HStack correspondences + disjointness invariants
  - `2158` The calculation is correct (proven)
  - `3447` The ◊3 diff-test battery
  - `3592` The D1-A bridge: `evalD ≡ Source.eval`
- Architecture constraints that BIND any proposed seam (quote these in the note):
  - Import direction is enforced by the `arch-check` fitness leg (ADR-0048's "import-direction V") — run `nix develop --command just fitness` to see it fire; read `tools/` for the script (grep `arch-check` in `justfile`).
  - The stratification principle (`CLAUDE.md`): verified core vs. tested superset with an explicit seam — a split must not move tested-stratum code into a module the verified stratum imports.
  - The repo treats module extraction as risky after one incident: an imported `abbrev` failed to reduce in a large module in a way it didn't in a fresh file (`Membership ?m X` unification failure) — extraction can CHANGE elaboration behavior. The note must flag which proposed cuts move `abbrev`s/notation.
- Doc conventions for the deliverable:
  - Design notes live in `docs/notes/`, with **frontmatter** (a fitness gate rejects notes without it) — copy the frontmatter shape of `docs/notes/ctr-design.md` (fields incl. `status:`).
  - `docs/notes/README.md` is GENERATED — after adding the note, find and run the regen recipe (`nix develop --command just --list | grep -i -E "note|index"`, likely `notes-index`; also re-run `just changelog`-adjacent regens only if fitness demands).
  - A new note gets a one-line row in `CLAUDE.md`'s Reference index table (match the existing rows' format: bold trigger phrase + path).

## Commands you will need

| Purpose | Command | Expected on success |
|---|---|---|
| Enter dev shell | `nix develop` | banner |
| Section inventory | `grep -n "^/-! " Bang/Frontend/TypeCheck.lean` (and the other file) | header list |
| Import graph of a symbol | `grep -rn "<symbol>" Bang/ --include="*.lean" -l` | consumer list |
| Fitness gates (frontmatter, refs, arch) | `nix develop --command just fitness` | exit 0 |
| Full gate | `nix develop --command just verify` | exit 0 (docs-only changes: fitness is the binding leg) |

## Scope

**In scope** (create/modify):
- `docs/notes/god-file-seams.md` (create — the deliverable)
- `docs/notes/README.md` (regenerate via recipe, never hand-edit)
- `CLAUDE.md` (one index-table row)
- `plans/README.md` (status row)

**Out of scope** (do NOT touch):
- **Any `.lean` file. This plan moves zero code.** If while analyzing you find a "trivial" extraction — resist; the incident history says extractions change elaboration.
- `paths/` — opening a PATH for the eventual refactor is the operator's call.

## Steps

### Step 1: Inventory with dependency evidence

For each major section of each file (headers above), determine what it EXPORTS that later sections/other files consume: pick the 3–5 load-bearing names per section (defs/types referenced outside the section), locate consumers via grep. Produce a section → consumers table. Key questions the table must answer:
- Does the `#guard` corpus region of TypeCheck.lean depend on anything except the public checker entry points (`checkProg`/`checkAndLower`/`parseProg`/`buildEnv`)? (If yes-only, the corpora are the cheapest extraction.)
- Is the HM substrate (421–1536) consumed by anything except the elaborator sections below it?
- In AbstractMachine.lean: do the proof sections (545+, 2158+, 3592+) consume the executable sections (106–544) only through a narrow set of definitions?

**Verify**: the table exists in your draft with grep-sourced consumer lists (not guesses); spot-check 3 entries by opening the consuming line.

### Step 2: Propose the cuts

Draft `docs/notes/god-file-seams.md` with frontmatter (copy `ctr-design.md`'s), containing:
1. The section inventory + dependency table (Step 1).
2. **Proposed module set**, each with: name in DOTTED module form since the files don't exist yet (e.g. `Bang.Frontend.TypeCheck.Infer`, `Bang.Frontend.TypeCheck.Corpus`, `Bang.Backend.AbstractMachine.Stores` — match the repo's existing `Bang/Core/Semantics/Subst.lean` precedent for a carved-out submodule), line-range provenance, and its import list drawn ONLY from the dependency table.
3. **Import-direction proof sketch**: show each proposed edge is consistent with the arch-check V (state the direction rule you found in the arch-check script and check each edge against it).
4. **Risk register**: every `abbrev`/`notation`/`macro` crossing a proposed cut (grep for them; the imported-abbrev incident above is why); every `partial def` whose termination context might change; the two files' `#guard`s (compiled guards must keep compiling in whichever module they land).
5. **Cut ORDER**: safest-first sequence (likely: corpora out of TypeCheck first — pure consumers; stores out of AbstractMachine second), with the explicit criterion that each landing is behavior-identical (`just verify` green, census/axiom state unchanged — cite the repo rule: gate the committed sha on a clean tree).
6. **What deliberately stays**: sections whose extraction is negative-value (e.g. the derived machine + its correctness proof plausibly belong together — the calculation IS the module).
7. An explicit **"this note is a proposal — the split needs an ADR + operator sequencing after the parked LR census unit lands"** closing paragraph (the census unit at branch `feat-lr-carrier-stackinc-wip` touches `Bang/Meta/BinaryLR.lean`, which imports the machine — splitting under it invites rebase pain).

**Verify**: every proposed module lists its imports, and every import traces to a row in the Step-1 table.

### Step 3: Wire the note into the doc system

Frontmatter present; regenerate `docs/notes/README.md` via the repo recipe; add the `CLAUDE.md` index row (one line, e.g. `| **God-file seam map** (TypeCheck/AbstractMachine split proposal · cut order · abbrev-risk register) | docs/notes/god-file-seams.md |`).

**Verify**: `nix develop --command just fitness` → exit 0 (this catches missing frontmatter, stale generated index, dangling refs). Then `nix develop --command just verify` → exit 0.

## Test plan

Docs-only: the fitness gate IS the test (frontmatter, generated-index freshness, reference integrity). The design's own quality gate is Step 2's verify line (imports ⊆ evidence table).

## Done criteria

- [ ] `docs/notes/god-file-seams.md` exists with frontmatter, dependency table, proposed modules + import lists, risk register, cut order, stays-put list
- [ ] Zero `.lean` files modified (`git diff --stat f1cb2cf..HEAD -- '*.lean'` → empty for this plan's commits)
- [ ] `docs/notes/README.md` regenerated (not hand-edited); `CLAUDE.md` row added
- [ ] `nix develop --command just fitness` and `just verify` exit 0
- [ ] `plans/README.md` status row updated

## STOP conditions

Stop and report back (do not improvise) if:

- You find yourself editing a `.lean` file for any reason — scope breach by definition.
- The dependency analysis reveals a genuine CYCLE between major sections (section A's exports consumed by B and B's by A) — that's a design finding requiring operator input on which side owns the shared types; report the cycle, don't paper over it with a proposed `Common.lean` dumping ground.
- The arch-check script's import rule can't be determined from `tools/` — report; the proof sketch in Step 2.3 is load-bearing and must not be guessed.

## Maintenance notes

- The follow-up (NOT this plan): an ADR proposing the split per the note, then mechanical landings in the note's cut order, each gated behavior-identical. Sequence after the parked LR census unit (task #37 on the board) lands.
- Reviewer should scrutinize: the abbrev/notation risk register (the known elaboration-changes-on-extraction failure mode), and whether the proposed module names match the existing tier-folder convention.
- If plans 002/003 landed first, their new guards sit in the corpus region — the seam map's corpus-extraction proposal should account for them (they only consume public entry points, so they move with the corpus).
