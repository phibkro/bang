# Project roadmap — features grounded in the programs that demand them

> The **product** axis, complementary to `ROADMAP.md` (the ◊-map = the PROOF/verification
> spine: kernel → CalcVM → LR → compiler → release) and `docs/roadmap/bang-northstar-roadmap.md`
> (research keyframes). This map answers a different question: **what real programs can you
> write, and which features does each one pull into existence?**

## The premise — projects are the checkpoints, features are the edges

bang already runs on a demand-driven method (the tracer-bullet discipline: *"the surface
DEMANDS kernel features, so kernel work is demand-driven"*). The tokenizer *pulled* strings +
recursion + termination-checking into being — they weren't built speculatively. This roadmap
**formalizes that method as its structure**:

```
PROJECTS  are the checkpoints        (a real, recognizable program that must RUN)
FEATURES  are the edges between them  (what a project requires, pulled into existence to reach it)
```

**Why**: it grounds every feature in a real problem that demands it — the antidote to a wish-list
where features are justified by taste or completeness. "We need polymorphism BECAUSE the parser-
combinator library can't be written without it" beats "polymorphism would be nice." A feature with
no project pulling it is a signal to question the feature, not schedule it.

**It's a DAG, not a line** — and it *dogfoods ADR-0076* (the module dependency graph is an acyclic,
generated DAG; bang's own roadmap is bang-shaped). A project is DONE when its required features land
AND it runs (a `#guard`ed example, like `examples/tokenizer.bang`).

## Committed sequence (decided 2026-07-07)

```
1  ▸ PARSER-COMBINATOR LIBRARY   ← THE NEXT MILESTONE. The acceptance test for the polymorphism in
     flight — commits the plan to: finish the ICTy re-rep (bare higher-order) + bite-1 generic data,
     with a parser-combinator library as the proof. The tokenizer's generalization (retires its own
     #50 mono-limit finding). Self-hosting payoff: bang's parser as a bang library.
2  ▸ SPREADSHEET (reactivity)     next candidate — lights up the distinctive DORMANT feature. NB the
     reactive MECHANISM is already proven (`reactiveCell` runs + a liveness law in the Audit gate,
     ADR-0005); the project EXTENDS it to a reactive-programming surface (not build-from-scratch).
     Rehearses incremental compilation (same hash-staleness shape, ADR-0076).
── wishlist (further out, roughly in dependency order) ──
   kv-store (STM — full payoff needs post-v1 concurrency) · web server · graphics (2048) · OS/distributed
```

**Near-term tooling (docs-as-data · ADR-0078):**
- **the gh-BRIDGE** — extend `gen-questions-index` to RESOLVE `see-also: [#N]` issue-edges via `gh`
  (validate the issue exists, pull live title/open-closed status, render it in the tie-graph beside Q- and
  ADR-nodes). Makes issues ↔ questions ↔ ADRs ONE queryable graph from two stores (git docs + GitHub
  issues) — no third tool. The unification move of ADR-0078.
- **CI gate (GitHub Actions)** — run `just verify` / `just fitness` on every PR, so "gate the committed
  content" is platform-enforced, not just local.
- **GitHub Milestones ↔ this DAG** — one milestone per PROJECT (tokenizer ✓ · parser-combinator · …), so
  the product-axis checkpoints live in GitHub too; issues group under them.
- **complete the ledger migration** — Q1–Q34 into OKF files, `OPEN_QUESTIONS.md` a fully generated
  multi-view index (in flight).

**Visual progress tracker + doc site (the operator's glanceable, low-reading view · ADR-0077 product face):**
A "video-game tracker" — a GENERATED VIEW over data we already have (proof-state · the project-DAG · the
question ledger · GitHub issues/milestones via `gh`), rendered VISUALLY: a progress MAP (◊-map + this DAG as
a level-map: done ✓ / current / locked) · HEALTH BARS (proof-state headlines clean, burndown) · a QUEST LOG
(issues under milestones) · a PULSE feed (recent landings / CHANGELOG — the Linear-pulse analog). Build
spectrum, cheapest first:
- **Zero-build TODAY (GitHub-native):** Projects (v2) roadmap/board + Milestones (one per PROJECT, progress
  bars) + the Insights → **Pulse** tab (merged PRs, closed issues — the activity pulse). Glanceable, no new
  dependency. The immediate tracker.
- **Custom dashboard site (richer, game-like):** an **Astro** site (content-collections — the surveyed
  state-of-art: typed frontmatter → validated → generated) on **GitHub Pages**, rendering BOTH the
  structured docs (the product face) AND a dashboard page (the level-map / health-bars / pulse). Cost: adds
  a Node/Astro build toolchain. Auto-rebuilds on push via Actions.
- **Incremental feedback:** GitHub Actions posts a status update on each landing (issue-close / PR-merge /
  milestone-complete) — the notification pulse — and the site rebuilds.

## The graph (projects ▸ the features they pull ▸ what they stress)

```
DONE ─────────────────────────────────────────────────────────────────────────────────────
  ✓ tokenizer            strings · recursion · termination-checking          (examples/tokenizer.bang)

FRONTIER — pull POLYMORPHISM / HIGHER-ORDER (being built now: the IVTy/ICTy re-rep, PATH-polymorphism)
  parser-combinator lib  higher-order (compose) · polymorphism · row-poly     stresses the CURRENT frontier
  JSON codec             recursive ADTs · Outcome/error handling · strings    grounds the SCHEMA/contract story (Q37)
  2048 (logic)           polymorphic List · refinement types (2^x invariant)  make-illegal-states-unrepresentable
                         · randomness (state capability)                       (the exponent = a power-of-2 by construction)

KERNEL-EXERCISERS — pull UNDER-USED kernel features
  key-value store        STM (the ONE privileged primitive — under-exercised   stresses STM/transactions directly
    w/ transactions      in v1) · concurrency · persistence
  spreadsheet /          REACTIVITY (`=`, ADR-0005/6 — the distinctive         stresses the reactivity operator;
    reactive dataflow    operator) · dependency DAGs · incremental recompute   same shape as incremental compilation

EXTERNAL SEAM — pull IO / FFI-as-effect (Q37)
  2048 (graphical)       FFI-as-effect (raylib) · effectful recursion (#48)    the interactive-program capability
  web server             network-effect · STM/concurrency · request/response   MORE effect-shaped than a game; hits
                         ADTs · routing · capability-per-connection            STM + the capability model head-on
  language toolchain     queryable-compiler (ADR-0076 #2) · incremental        THE dogfood — bang builds bang's tools;
                         compilation (content-addressed) · module system       compiler-as-core, everything else a VIEW:
                         │                                                       LSP · MCP (compiler-as-agent-server) ·
                         └─ views: LSP · MCP · CLI · formatter · linter ·        CLI · canonical formatter · linter/
                            static analysis · build tool                         static-analysis · incremental build

NORTHSTAR — pull CONCURRENCY / DISTRIBUTION (the set destination: OS / distributed systems)
  chat / actor system    actors (`!`, actor-send) · message-passing · dist.    stresses the actor model
  replicated log / Raft   consensus · network · capability security · STM       the distributed-systems capstone
  OS / unikernel         hardware FFI · scheduling-as-effect · memory grades    the ultimate northstar; effects ARE
                         (QTT, Q30/Q33) · capability isolation                  the OS abstraction (syscall=effect,
                                                                                driver=handler, STM=the concurrency base)
```

## How to read / use it

- **Pick the next feature by picking the next PROJECT.** The feature work is then justified and
  scoped by what the project concretely needs — not by completeness.
- **A project surfaces papercuts that become features** (the tokenizer → #50 multi-arg limit →
  polymorphism motivation). The papercut IS the demand signal.
- **The tiers are roughly dependency-ordered** but it's a DAG: the language toolchain, for instance,
  needs the module system (frontier) AND IO (external seam), so it sits late even though pieces of it
  (the queryable checker, source spans, located errors — landed) start early.
- **The northstar (OS / distributed) is where the effect system pays off** — capability security
  (Q37), STM concurrency, actors, and the FFI seam all converge. Every earlier project is a rehearsal
  for one of its sub-problems.

## Relationship to the other roadmaps

```
ROADMAP.md                       the ◊-map — PROOF milestones (kernel frozen · CalcVM · LR · compiler · release)
docs/roadmap/bang-northstar-…    research KEYFRAMES (the K-series)
docs/roadmap/project-roadmap.md  THIS — the PRODUCT axis: programs ▸ features, demand-driven, a DAG
```

The proof-map answers *"is it correct?"*; this map answers *"what can you build, and why that feature
next?"* They're orthogonal axes on the same project — a feature is scheduled when a PROJECT pulls it
(this map) and lands when its PROOF obligations clear (the ◊-map).

## Revisit

Add a project when a real program would stress a capability no current project reaches; retire the
"features" framing of a slice once its project runs (the `#guard`ed example is the checkpoint met).
Candidate additions not yet placed: a regex engine (higher-order + polymorphism), a small theorem
prover / type-checker in bang (the ultimate self-hosting dogfood), a game-of-life (a lighter grid
project). Ties `docs/notes/OPEN_QUESTIONS.md` (Q37 FFI-as-effect, Q38 module≟effect, Q31 refinement),
ADR-0076 (tooling by construction — the toolchain project's architecture), ADR-0026 (stratification).
