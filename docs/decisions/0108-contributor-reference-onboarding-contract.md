# ADR-0108 · Contributor reference and onboarding contract

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: The contributor-reference system optimizes first for a general language implementer, while branching into specialist human and agent routes; uses one public Vocs site with a curated product/contributor split and keeps volatile work state repo-only; ships deterministic caption-led generated media with transcripts and reduced-motion fallbacks, without requiring narration; and teaches one journey through two fixtures — a tiny thunk/force precursor followed by the logger-counting handler example. These choices settle Plan 014 Phase 0 and make Phase 1 executable.
- **Depends-on**: ADR-0077 (documentation placement by audience × temporality), ADR-0078 (git-native knowledge and GitHub workflow)
- **Relates-to**: `plans/014-developer-reference-onboarding-system.md`, existing Vocs/tour/reference generators

- **Date**: 2026-07-13
- **Deciders**: operator
- **Layer**: meta / contributor documentation product contract

## Context

Plan 014 identified four product choices that had to be settled before implementation: the primary newcomer, the public/private boundary, the media contract, and the canonical teaching fixture. Leaving them open would make the information architecture, lesson outcomes, asset pipeline, and vertical slice under-specified.

The repository already supplies the constraints:

- ADR-0077 separates stable product snapshots from time-indexed project work.
- The Vocs site, generated language reference, executable tour fixtures, and run service are existing roots; a second documentation system would duplicate them.
- `examples/logger-counting/main.bang` already agrees across the env, oracle, and compiled engines, but introduces too many concepts to be the first syntax lesson.
- Documentation claims must remain available without motion or audio and must be reproducible from git-native sources.

## Decision

| Dimension | Chosen contract | Graduation evidence |
|---|---|---|
| Primary newcomer | Optimize the common route for a **general language implementer**. Proof, backend, tooling/docs, and coding-agent routes branch after the shared mental model. | First hour: run and inspect one effectful program across engines. First day: complete a bounded frontend/tooling-shaped change, locate its source of truth, and run the correct narrow and full gates. |
| Publishing boundary | Use **one public Vocs site** with clear Start, Learn, Reference, Contribute, and Architecture sections. Publish stable specialist and agent routes; keep `CONTEXT.md`, active `paths/`, scratch research, and operational work state repo-only. | A newcomer can distinguish stable product/contributor reference from volatile project state without navigating a second site. |
| Media | Ship **caption-led deterministic generated media**: D2/SVG sources, Remotion where animation earns its cost, captions, Markdown transcripts, posters, and reduced-motion/static alternatives. Narration is optional, never a release gate. Small web outputs may live in git; larger outputs use release assets or an approved CDN. | Every motion asset has a source, transcript/captions, static fallback, and a validating build command. |
| Program journey | Use a **two-fixture progression**: a tiny thunk/force precursor first, then logger-counting for handler installation, runtime-as-handler, and three-engine agreement. Reuse the logger fixture across the first vertical slice's generated facts, diagram, interactive trace, media, and lab. | The first fixture teaches description/observation without handler load; the second demonstrates the architecture and evidence ladder without inventing a separate example per medium. |

Plan 014 remains the executable sequencing document. This ADR is the source of truth for the four product choices above.

## Rejected alternatives

- **Agent-first common route** — agents get a dedicated route, but optimizing the shared first hour for repository mechanics would weaken the human learning journey and make language understanding secondary.
- **Proof-first or backend-first common route** — both are important specialist paths, but their prerequisites overload the common entry and narrow the contributor funnel.
- **Publish all project state** — exposes volatile context and active work beside stable reference, recreating ADR-0077's category error.
- **Product-only public site** — hides stable implementation and contribution knowledge that external contributors need.
- **A separate contributor site** — creates a second navigation, build, and maintenance system without a distinct source of truth.
- **Narration-required video** — makes correction and release depend on recording capacity; captions and transcripts are required regardless.
- **No encoded media** — leaves the requested animation/visual learning path untested; generated caption-led media keeps it reproducible.
- **Logger-counting as the only fixture** — maximizes reuse but overloads the first thunk/force lesson.
- **Nested-handler or transaction fixture first** — each demonstrates a deeper mechanism but carries too much initial concept load.

## Consequences

- Plan 014 advances from product discovery to executable Phase 1 root repair.
- The first vertical slice has a fixed audience, information boundary, asset contract, and fixture pair.
- Specialist routes remain first-class, but they share one common mental-model and evidence vocabulary.
- Volatile project state may be linked from repository contributor docs, but it is not mirrored into the stable public learning tree.
- Media tooling must be pinned and gated before generated motion assets are accepted.

## Revisit if

- stranger tests show the general-implementer route blocks most real newcomers;
- the contributor material requires authentication or a genuinely different deployment boundary;
- narration capacity becomes durable enough to make audio a maintained product artifact; or
- the logger fixture cannot expose a stable trace without perturbing the verified interfaces.
