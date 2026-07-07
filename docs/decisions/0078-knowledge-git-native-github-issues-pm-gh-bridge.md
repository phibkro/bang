# ADR-0078 · Knowledge is git-native (agent-visible, generated + validated); GitHub Issues is the PM layer; a gh-bridge resolves issue-edges into the tie-graph — one graph, two well-chosen stores, no third tool

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: DOCS stay **git-native** (the OKF question ledger + ADRs + notes, in the main repo) because the top priority is **AI-agent-visibility** — an agent reads the repo directly; git files are diffable, PR-reviewed, generated-from-frontmatter, and coupled with the code. A hosted docs tool (Linear/Notion/Jira) would take docs OFF git and regress that priority. **GitHub Issues** is the PM layer — already in use, excellent GraphQL/REST/`gh` API, integrates with the repo (PR-closes-issue, `#N` linkification), and fits the project's scale (Linear/Jira are team-velocity tools = ahead of need; the repo already retired issues-as-files TO GitHub). The two stores are unified NOT by moving one into the other but by a **gh-BRIDGE**: the OKF `see-also: ["#44"]` issue-edges are resolved via `gh` (validate the issue exists, pull its live title/status, render it in the tie-graph) — one queryable graph (questions ↔ ADRs ↔ issues) from two well-chosen stores + a thin bridge. The anti-tangle principle: the tangle risk is a THIRD tool; the fix is the bridge, not replacement.
- **Depends-on**: 0076, 0077
- **Relates-to**: the OKF question ledger (`gen-questions-index`), the gh-bridge roadmap item (`docs/roadmap/project-roadmap.md`), CONTRIBUTING.md (the contributor workflow this defines)

- **Status:** Accepted (operator-approved 2026-07-07)
- **Date:** 2026-07-07
- **Layer:** meta / knowledge + PM tooling (governs where knowledge lives + how GitHub is integrated)
- **Builds on:** ADR-0076 (the compiler/knowledge as a queryable, generated, validated service), ADR-0077 (product vs project — WHERE knowledge lives; this decides the STORE + the PM coupling). Lineage: OKF (agent-maintainable git-native knowledge); the GitHub GraphQL/`gh` API; the "dependencies by attack surface, not count" principle.

## Context

The docs-as-data direction raised whether to adopt a hosted project-management/docs tool (Linear, Jira +
Confluence, Notion) that unifies issue-tracking with internal documents — since the two are coupled and
cross-reference extensively (an issue cites a design question, a question cites an ADR, an ADR cites
issues). The stated fear: a tool that DECOUPLES them, or a THIRD tool bolted alongside git, creates a more
tangled web. The stated top priority (operator, repeatedly): **the documentation must be accessibly visible
to AI agents.** That priority is the tiebreaker.

## Decision

1. **Docs are GIT-NATIVE.** The OKF question ledger, ADRs, and notes live in the main repo. Rationale: an
   agent reads repo files natively (in-context, no API round-trip / auth); the files are diffable,
   PR-reviewed, generated-from-frontmatter, and coupled with the code they describe. A hosted docs tool
   trades all of that away — and specifically regresses agent-visibility, the top priority. (OKF is
   "agent-maintainable" precisely BECAUSE it is git files.)
2. **GitHub Issues is the PM layer.** Already in use; excellent GraphQL + REST + `gh` CLI + webhooks;
   integrates with the repo (PR-closes-issue, `#N` linkification, permalinks); supports external
   contributors, boards, milestones, notifications that flat files cannot. It fits the project's SCALE —
   Linear/Jira exist for teams with sprint/velocity machinery (ahead of need here), and the repo already
   tried issues-as-files and retired that TO GitHub Issues (that lesson is banked).
3. **Unify via a gh-BRIDGE, not a third tool.** The coupling (issues ↔ docs in one referenceable graph)
   does NOT require moving one store into the other. The OKF frontmatter already records issue-edges
   (`see-also: ["#44"]`); a generator RESOLVES them via `gh` (validate `#44` exists, pull live title +
   open/closed status, render it as a node in the tie-graph beside Q- and ADR-nodes). Result: ONE queryable
   graph — questions ↔ ADRs ↔ issues — assembled from two well-chosen stores joined by a thin bridge. Docs
   own the doc-graph (git); GitHub owns the issue-graph (API); the generator joins them.

### GitHub feature integration (the survey — how we use GitHub, and what we DON'T)

```
USE
  Issues        the PM layer (the work). Labels = status/area; the queryable backbone of the gh-bridge.
  Milestones    one milestone per PROJECT (project-roadmap DAG: tokenizer ✓ · parser-combinator · …) —
                GitHub Milestones mirror the product-axis checkpoints; issues group under them.
  Projects (v2) kanban / roadmap board over issues (GraphQL-queryable) — the visual PM view.
  Pull Requests code review + PR-closes-issue; the change gate.
  Actions (CI)  run `just verify` / `just fitness` on every PR — the verify gate as CI, so "gate the
                committed content" is enforced by the platform, not just locally. HIGH-VALUE integration.
  gh CLI / GraphQL  the programmatic bridge — resolves #N edges, powers issue-aware generators.
DON'T
  Wiki          a SEPARATE `.wiki.git` repo → decoupled from the code, NOT agent-visible in the main tree,
                not PR-reviewed with the change. It re-introduces the exact fragmentation we're avoiding.
                Repo markdown already renders on GitHub; keep docs in the main tree.
  Discussions   a hosted forum — the git-native OKF ledger serves the design-discussion role better for the
                agent-visibility priority. (Reconsider only for EXTERNAL community Q&A.)
LATER
  Pages         publish the GENERATED product docs (language.md, …) as a consumer site — still git-native
                (built FROM the repo), the "product face" of ADR-0077. When a consumer audience exists.
  Releases      tag + artifacts at ◊6.
```

## Rejected / not-now

- **Linear / Notion / Jira for docs (unify-up)** — docs leave git → regress agent-visibility (the top
  priority); adds a heavy new dependency + auth surface; Jira+Confluence is itself two-products-bolted (the
  tangle). Linear's API is excellent, but excellent-API is not the deciding axis — git-nativeness is.
- **The GitHub Wiki** — separate repo, decouples from code, not agent-visible in the main tree.
- **Issues-as-files (unify-down fully)** — loses GitHub's PM UX (assignees, boards, external contributors,
  notifications); already tried + retired.

## Consequences

- Docs stay agent-native + generated + validated (the tie-graph, dangling-edge-fails); PM stays on GitHub
  with its API; a gh-bridge makes issue-edges first-class in the graph (a roadmap item).
- CI (Actions) runs the verify gate on PRs — the gate becomes platform-enforced.
- Directly defines the contributor workflow in `CONTRIBUTING.md`: issue → branch → PR → the fitness gate;
  docs edited as git files; the gh-bridge for cross-references.

## Revisit if

The project grows to team-scale (real sprint/velocity needs → reconsider Linear, weighed against
agent-visibility); OR a consumer-doc SITE is wanted (GitHub Pages over the product docs); OR the gh-bridge
shows the issue-edges need richer modeling than resolution (then reconsider the store boundary).
