# Plan 014 — Developer reference and onboarding system

- **Status:** IN REVIEW — Phase 0/1 plus feedback fixes F-006–F-008 implemented and verified on draft PR #141, awaiting review/landing
- **Priority:** P1 documentation architecture
- **Effort:** XL, delivered as independently gated vertical slices
- **Depends on:** current architecture roots and existing Vocs/tour/reference generators
- **Decision contract:** ADR-0108
- **Research basis:** code-first exploration on 2026-07-13; existing docs compared only after the independent model was drafted

## Destination

A git-native, generated-where-possible documentation and learning system in the existing Vocs site that enables a brand-new human or coding agent to understand BANG's language and implementation, choose a role-specific route, complete a bounded first change, and state the evidence behind its behavior.

Success is demonstrated by newcomer tasks and drift gates, not by page count.

## Phase 0 — product contract settled

**Source of truth:** ADR-0108. The executable constraints are:

| Dimension | Settled direction |
|---|---|
| Primary newcomer | General language implementer; specialist proof/backend/tooling/docs/agent routes branch after the common journey. |
| Publishing boundary | One public Vocs site with a curated stable contributor section; volatile `CONTEXT.md`, active paths, scratch research, and operational state remain repo-only. |
| Media | Caption-led deterministic generated assets with transcripts and reduced-motion/static fallbacks; narration is optional. |
| Program journey | Tiny thunk/force precursor → logger-counting handler example; logger-counting anchors the first cross-medium vertical slice. |

The first-hour and first-day graduation evidence, rejected alternatives, storage contract, and revisit triggers live in ADR-0108 rather than being duplicated here.

Before parallel implementation begins, create the Wayfinder issue map from the phase sequence below, with explicit research/prototype/grilling blockers. Phase 1 root repair may begin without waiting for media or trace prototypes.

## Agent orchestration

The parent agent is the **integrator and evidence owner**: it owns the Wayfinder map, assigns file ownership, verifies worktree isolation immediately after spawn, integrates by pathspec, and gates committed content. Subagents return artifacts and evidence; their summaries are never accepted as gates.

Run at most **two expensive agents concurrently** on workstation. The host's cgroup policy and the recorded 7+-session thrash incident make broad agent fleets an availability risk, not a speedup.

### Roles

| Agent | Default mode | Owns |
|---|---|---|
| architecture-verifier | read-only | code/ADR truth table; stale-claim and evidence audit |
| learning-designer | read-only or isolated prototype | newcomer outcomes, lesson order, retrieval exercises, stranger-test rubric |
| docs-generator-engineer | isolated writer | fact schema, extractors/renderers, drift gates |
| docs-site-engineer | isolated writer | Vocs IA, components, Playwright/accessibility |
| visualization-engineer | isolated writer | D2 sources/rendering and program-journey UI |
| media-engineer | isolated writer | Remotion/ffmpeg pipeline, captions/transcripts/posters |
| role specialist | read-only reviewer | surface/kernel/proof/backend correctness for its route |
| adversarial reviewer | read-only | evidence labels, stale architecture, accessibility, false-green checks |

### Wave protocol

1. Parallel read-only research is allowed freely within the two-agent compute ceiling.
2. Prototype agents produce throwaway or isolated artifacts for operator reaction; they do not edit canonical pages.
3. A writing wave assigns **one writer per file** and one verified worktree per writer. Overlapping writers are serialized.
4. The integrator reviews diffs and runs the narrow gate before accepting an artifact.
5. A separate read-only reviewer attempts to refute the committed result.
6. Only then does the integrator run the cross-cutting/full gate and advance the map.

Every delegation names: destination, allowed paths, forbidden paths, source-of-truth inputs, expected artifact, validation command, stop conditions, and structured result fields (`files`, `claims`, `commands`, `risks`, `open_questions`).

## Phase 1 — repair the roots before adding branches

**Status:** IMPLEMENTED and verified (`lake build`, `just fitness`, `just verify`, focused CLI batteries, and the Vocs production build); not yet committed or merged.

### Deliverables

- Correct `README.md` architecture, current-state phrasing, tier layout, and proof-method terminology.
- Replace `ONBOARDING.md`'s broad reading list with a 15-minute executable start and role selector; retain setup troubleshooting as a linked reference.
- Rebuild `docs/architecture/core-overview.md` around current tiers and actual import edges. Remove completed migration narrative to git/ADRs.
- Add a generated “architecture assertions” gate checking target names, tier paths, theorem-arrow labels, and current engine defaults.
- Fix the import-graph generator so fan-in/tier data reflects current `public import`/module syntax; add a falsify-once fixture.

### Why first

New visuals amplify whatever model they visualize. Current root pages still teach WasmFX-primary, old module names, and an obsolete checkpoint; producing video before correcting these would make drift more expensive.

## Phase 2 — establish a reusable documentation fact model

Refactor the monolithic reference generator into extractors plus renderers:

```text
Lean/source/examples/CLI/ADRs
       ↓ extract + validate
   docfacts/*.json
       ↓ renderers
reference pages · D2 labels · tour fixtures · glossary · command matrix · video captions
```

### Fact families

- surface forms, types, precedence/rules, diagnostics, prelude signatures;
- module/tier/import graph and public symbols;
- engine pipeline and evidence status per arrow;
- examples with source, expected result, engines supported, concepts, refusal class;
- headline theorems and axiom sets from `Audit.lean`;
- CLI commands/flags/exit contracts;
- ADR status and “implemented/proposed/superseded” state kept distinct.

Use JSON Schema (or a small TypeScript/Zod schema in the site build) and deterministic generators. Existing Python extractors may remain; do not rewrite them merely for language consistency.

### Key invariant

A claim displayed as **Proven**, **Differential-tested**, **Generated**, **Implemented**, or **Proposed** must have a source pointer and a validating command. Styling alone may never assign evidence status.

## Phase 3 — reference information architecture

Create a Diátaxis-inspired but project-specific tree:

```text
Start
  15-minute quickstart
  choose your contributor route
Learn
  mental models
  guided language tour
  program journey
Reference
  language
  compiler/CLI service
  kernel and theorem map
  machines/backends
  glossary
Contribute
  frontend route
  proof route
  backend route
  tooling route
  docs/examples route
  agent route
Architecture
  current system snapshot
  evidence/trust boundaries
  decision index (project/DONE)
Project (clearly separated)
  current context / active paths / roadmap
```

Generate sidebar entries from a page manifest carrying audience, lifecycle, prerequisites, and status. Keep one Vocs site and one git-native source; the split is navigational, not another store.

## Phase 4 — onboarding journeys and labs

### Common 15-minute route

1. Preflight reports Nix/dev-shell/build-cache state and warns not to parallelize the first Lake setup.
2. Run `1 + 2` through env/oracle/compiled engines.
3. Run a minimal thunk/force example and predict before revealing output.
4. Run a custom-effect handler swap; inspect `check --json` and `query dump`.
5. View the same program's generated pipeline/evidence diagram.
6. Select a role route.

### Role labs

Each route contains 3–5 short lessons and ends with a bounded pull-request-shaped change:

- **Frontend:** add/modify a syntax fixture, follow every `Surf` traversal, run formatter/check/query gates.
- **Proof:** inspect one `Spec` headline, find implementation theorem and axiom report, close or adapt a tiny lemma in scratch.
- **Backend:** trace one constructor from `Source.step` through `evalD`, `compile/exec`, and emitter; add a differential fixture.
- **Tooling:** add a query projection or diagnostic fixture without creating a second checker.
- **Docs/examples:** add a gated example and generated lesson metadata; verify site/accessibility.
- **Agent:** orient, identify ADR/path, isolate a worktree, use symbols/query/impact, run the smallest gate, then full gate.

Every lesson uses prediction → action → immediate feedback → short explanation → retrieval check. Record completion locally; no account system is required.

## Phase 5 — diagrams and interactive implementation visualizations

### D2 diagram set

Store authored sources under `docs/diagrams/*.d2`; generate accessible SVG plus text descriptions:

1. system context (developer, BANG CLI, Lean, Wasmtime/WASI);
2. source journey with evidence-colored arrows;
3. dependency V and tier responsibilities;
4. CBPV value/computation bridge;
5. effect label vs capability identity;
6. CK handler stack: abort vs resume;
7. `evalD` stores ↔ calculated HStack correspondence;
8. verified/tested/host seam;
9. contribution knowledge/gate lifecycle.

Pin D2 in `flake.nix`; add `just diagrams` and `just diagrams --check`. Keep Mermaid for truly generated import graphs unless D2 gains a reliable generated layout path; do not manually duplicate the import DAG.

### Interactive “program journey”

Add a trace exporter that emits stable JSON fixtures for a small program:

- tokens / surface AST;
- elaborated and lowered core;
- selected CK configurations (fresh counter, focus, frames);
- `evalD` state/custom/transaction stores;
- CalcVM instructions and machine state;
- emitted WAT excerpts and observed value;
- evidence metadata for each transition.

Render this in a small client-side SVG/HTML component embedded in Vocs. Controls: next/back, scrub, auto-play, engine toggle, stack/store inspection, reduced-motion mode. Start with checked-in generated fixtures; live arbitrary tracing can come later.

A Lean/CLI exporter is preferable to parsing pretty-printed debug text. If exposing traces would perturb frozen APIs, use a leaf executable outside the verified library and differential-gate its observations.

## Phase 6 — animated explainers and terminal media

Create six 60–180 second explainers, each reusing D2 assets and/or program-journey JSON:

1. “Description until forced”;
2. “Runtime as a handler cartridge”;
3. “Label for typing, identity for dispatch”;
4. “Calculate the VM; do not invent it”;
5. “Two proof arrows: equivalence vs compilation”;
6. “Verified core, tested superset, real-world IO seam.”

### Toolchain

- **Remotion** in an independent `web/explainers/` app for deterministic React/SVG video composition.
- **ffmpeg** pinned in Nix for WebM/MP4 encoding and metadata checks.
- D2-generated SVG and the shared trace JSON as inputs.
- WebVTT captions and Markdown transcripts generated from a timed script manifest.
- Optional **VHS/asciinema** only for terminal demonstrations; terminal recordings are generated from scripts and are supplementary.

Render poster SVG/PNG and reduced-motion alternatives. Commit source and small web-optimized outputs only; use GitHub release assets or an approved CDN for larger video files if repository budget requires it. Human narration is a separate operator-approved production step; caption-led versions ship first so accessibility and reproducibility do not wait on audio.

## Phase 7 — connect the existing tour/run service

- Replace overloaded tour lessons with smaller concept fixtures and prerequisite metadata.
- Connect the existing `/run` service behind an optional editor after static lessons remain functional.
- Add retrieval checks and “show pipeline” links backed by the trace fixtures.
- Preserve the current build invariant: lesson code/output comes from gated examples, never hand-copied.
- Run user code only within the existing jail/limits; the documentation build must not depend on the service being online.

## Phase 8 — validation and maintenance

### Automated gates

- link/dead-route checks fail rather than warn for maintained product pages;
- `just docs-check`: generated fact drift, D2 render drift, lesson fixture existence, evidence-source pointers;
- Playwright smoke tests for navigation, interactive stepper, keyboard operation, reduced motion, and mobile layout;
- axe-core accessibility checks; captions/transcripts/posters required for every video;
- code examples run across declared engines and expected refusals are tested as refusals;
- architecture freshness: every module classified, import graph nonempty, fan-in sanity poles, no retired names in current snapshots;
- newcomer scripts tested from a clean or simulated-cold environment without parallel Lake races.

### Human validation

Run three stranger tests after prototype, beta, and completion:

- one developer unfamiliar with Lean;
- one Lean/proof developer unfamiliar with BANG;
- one coding agent given only the new start page.

Measure time to first successful run, ability to answer the five mental-model questions, time to locate the correct change site, and whether the participant chooses the correct evidence/gate. Feed failures into lessons/generators, not an unstructured findings appendix.

## Inclusion rationale

Included because it changes how developers reason or work:

- CBPV split, rows/grades, label/identity, handler dispositions;
- elaboration-to-core and module flattening;
- source/evalD/CalcVM/env/Wasm distinctions;
- logical relation vs forward simulation;
- evidence ladder and project knowledge lifecycle;
- role-specific edit/gate recipes.

Included only in advanced routes:

- full typing-rule derivations, LR indexing, freshness carriers, substitution lemmas;
- detailed WasmGC representation and bignum helpers;
- research `Reify` subsystem and rejected design history.

Excluded from the current snapshot except as a labelled horizon:

- unimplemented multi-package workspace;
- post-v1 general/multishot/concurrency machinery;
- superseded dispatch/cap representations;
- exhaustive lemma catalogs (doc-gen/API search owns these);
- volatile issue-by-issue validation history in the product language reference.

## Recommended implementation sequence

1. Operator decisions / Wayfinder map if needed.
2. Root accuracy repairs and architecture-generator fix.
3. Fact schema and evidence badges.
4. Quickstart + role selector prototype.
5. D2 macro diagrams.
6. Program-journey trace spike for one fixture.
7. One complete role route and one explainer as a vertical slice.
8. Stranger test; revise the system.
9. Expand remaining routes/diagrams/videos.
10. Connect live run service, harden accessibility and release gates.

The vertical slice should prove the pipeline before scaling content: one canonical example → generated facts → text lesson → D2 diagram → interactive trace → captioned video → executable lab → CI gate.
