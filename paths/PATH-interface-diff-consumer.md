# PATH-interface-diff-consumer — consume checked interfaces without inventing artifact reuse

> Compare two public dump snapshots, propagate checked type/shape movement over the resolver DAG,
> and stop visibly where dump v1 cannot attribute a changed public law contract to its owner.

## Seam

- **From checkpoint**: `PATH-stable-interface-effect-rendering` made checked effect identities stable
  enough to compare while retaining `cacheKeySafe:false` and `separateCompilationReady:false`.
- **To checkpoint**: a build-tool author can compare two dump files and see per-module interface
  status plus reverse-transitive recheck candidates; no compiler work is actually skipped.
- **Contract preserved**: the tool is an external consumer of the additive dump-v1 contract, not a
  new `bang query` verb, schema field, cache, scheduler, checker, lowered artifact, or linker.

## Layer

- [ ] Kernel  [ ] Compiler  [ ] Surface language  [x] Meta (tool consumer/tests/docs)

## Actor journey / observable outcome

- **Actor / need**: a build-tool author has old/new `bang query dump` snapshots and wants to know
  which modules' checked type/shape work is structurally re-derivable after a change.
- **Public starting point**: `python3 tools/interface-diff.py old-dump.json new-dump.json`.
- **Terminal observation**: complete export records distinguish preserved/moved interfaces; moved,
  added, removed, and dependency-changed seeds propagate through validated `moduleDeps`, with each
  surviving module reporting `recheckCandidate` and `invalidatedBy`.
- **Adverse / recovery route**: a public law-body edit in `Lib` preserves its name-only interface but
  moves global law evidence for `Mid`'s handler. The tool returns JSON `indeterminate`, exit 2, the
  named `module-owned-public-law-contract` gap, and zero skipped checks.
- **Downstream journey released**: a separate schema increment can decide whether public law identity
  belongs in module exports or law rows; artifact/store work remains blocked on independent lowering.

## Feeds the constraint

- **Binding constraint now**: five measurement increments exposed stable facts but no consumer proved
  that the schema could drive even a scoped invalidation decision.
- **How this path feeds it**: consume the exact public facts at the actor's seat, demonstrate honest
  type/shape fanout, and turn the first missing decision fact into a concrete schema successor.

## Prospective systemic review

| concern | horizon + evidence | likelihood / impact / late cost | disposition now | reopen trigger |
|---|---|---|---|---|
| 64-bit digest is treated as equality or cache authority | first consumer; metadata says unsafe | high / critical / high | **compare complete projected exports and cross-check the digest** | a collision-safe/versioned key lands |
| “preserved” becomes “skip” | no independent checked/code artifact exists | high / critical / high | **emit `actualChecksSkipped:false` and `artifactReuseAuthorized:false` in-band** | an independently validated artifact exists |
| law-body contract change is missed | realized cross-module `Lib`/`Mid` fixture | high / critical / high | **return indeterminate exit 2; retain the schema gap** | module-owned public-law identity lands |
| declared law has no realization and is absent from `laws` | `lawInstancesOf` emits instances, not declarations | high / critical / high | **name the blind spot; successor must cover declared public laws** | declared-law ownership fact lands |
| source-order permutation moves equal public exports | interface payload preserves export list order | medium / medium / medium | **accept safe false invalidation; do not diverge from producer digest semantics here** | canonical interface payload is reviewed |
| topology changes make the view toy-only | add/remove/import edits are ordinary | high / high / medium | **union before/after closure; gate added and removed modules** | dependency kinds acquire distinct semantics |
| additive dump growth breaks the consumer | dump-v1 forward-compatibility contract | medium / high / medium | **project known fields and gate unknown fields at three nesting levels** | `schemaVersion` changes |
| law row reordering creates false gaps | rows are relational facts | medium / medium / low | **sort known-field projections as a multiset** | stable law IDs replace compatibility tuples |
| coarse import edges over-invalidate unused imports | `moduleDeps` intentionally collapses import/use | realized / medium / medium | **report structural candidates, not minimal semantic work** | use-sensitive dependency facts land |
| subprocess composition is premature infrastructure | current projects are small; existing validator is public tool code | low / low / low | **reuse `module-impact.py`, measure before refactoring a library** | representative comparisons cross a latency budget |

## Baseline, falsifier, and evidence

- **Baseline / red observation**: module interfaces and reverse closures existed separately; a tool
  author still had to invent their join and might equate one preserved digest with safe reuse.
- **Smallest tracer bullet**: a pure two-file JSON consumer composed with the existing validated
  `module-impact.py`, plus a three-deep `@entry → Mid → Lib` fixture.
- **Positive evidence**: a body-only edit preserves every interface; a public signature edit moves
  `Lib` and marks `Lib`, `Mid`, and `@entry`; adding/removing `Side` updates topology candidates.
- **Sensitivity/control evidence**: complete exports and digests must agree; additive unknown fields
  at dump/interface/export levels are ignored under schema v1.
- **Strongest falsifier**: `Lib.Gate`'s public law body changes while its interface export (law name
  only) is unchanged; the global law fact moves but has no stable module relation key. No per-module
  complete invalidation verdict is emitted.
- **Broader convergence gate**: focused query battery, generated tool/reference docs, repository
  fitness, full build/batteries, and persistent read-only advisor review.
- **Assumptions / exclusions**: status is scoped to checked public type/shape plus resolver topology.
  A declared law with no discovered handler/realization is invisible in dump v1's instance-only
  `laws` table; public-export source order is significant and permutation may cause false invalidation.
  No claim covers complete semantic contracts, law ownership, hole-marker normalization, source/body
  identity, parsing/checking actually skipped, independently lowered code, linking, cache hits,
  persistence, collision-safe keys, scheduling, timing, or speedup.

## Plan

1. [x] Ask the persistent advisor to rank the first fact consumer and pre-name its falsifier.
2. [x] Implement a forward-compatible two-dump consumer over complete exports and validated fanout.
3. [x] Gate body/signature, transitive, add/remove, unknown-field, and public-law-body journeys.
4. [x] Persist the schema finding, complete skeptical review, run convergence, and publish.

## Status

- [x] Started 2026-07-18
- [ ] In flight: none
- [ ] Blockers: none
- [x] Completed 2026-07-18
- Focused evidence: `tools/test-query.sh` — **194 passed, 0 failed** with Python + jq available.
- Convergence evidence: the exact staged tree passed the 1,550-job verification build, 1,452-job
  battery build, all **31/31** batteries, live proof audit, and repository fitness. The persistent
  advisor's skeptical review requested a digest/export disagreement gate and explicit treatment of
  declared laws without handlers and public-export order sensitivity; all three are now tested or
  retained as named limitations.
- Retained failed gate / successor: dump v1 law rows expose changed bodies globally but cannot stably
  attribute a public contract change to its module—and emit nothing for a declared law with no
  realization. Choose declared-law identity in exports versus module-owned declared-law facts in a
  separate schema-reviewed increment; do not add a field merely to make this tracer green. Public
  export order also remains a named safe false-invalidation source.
- Reopen / observe: any output interpreted as actual reuse, any complete invalidation verdict while
  `gap` is non-null, or any schema addition folded into this path.

## Owner

- Agent / human: Codex, with persistent read-only Fable 5 strategic advisor in Herdr
