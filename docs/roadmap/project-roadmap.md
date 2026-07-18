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

## Committed sequence (updated 2026-07-18)

```
✓  ▸ PARSER-COMBINATOR LIBRARY   higher-order composition + polymorphism now run as a corpus example.
✓  ▸ SEMANTIC CONTRACTS          named effect contracts, laws, swappable handlers, pledges, and
                                 stateful quota policy run across the execution routes.
✓  ▸ ONE-SHOT PERMIT             one opt-in value quantity rejects duplicate/forgotten consumption;
                                 grade-0 erasure and the joined evidence card are concrete on Wasm.
✓  ▸ EVIDENCE-SEAM INTEGRITY     operation/subject validity split, stable declaration IDs, resolved
                                 B018 parity/location, quiet route, and frozen-packet replay are green.
   ↷ ORGANIC CORRECTION          DEFERRED BY OPERATOR 2026-07-18, not completed: one unfamiliar developer
     still must run the repaired public journey before ◊6/release (`PATH-organic-resource-validation`).
0  ▸ SPREADSHEET (reactivity)     ← LIVE EDGE: live/stale behavior and the stable formula DAG are now
     observable; repeated evaluation is not yet measured. NB the
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
- **Doc-SITE generator (DEFERRED — only when the docs go multi-page as the ADR-0077 product face; the
  dashboard is a separate single page, already live):** candidates, all taking git-native markdown+frontmatter
  (respects ADR-0078) → a static site on Pages: **Astro Starlight** (mature, big plugin ecosystem incl.
  `starlight-llms-txt` → llms.txt / `starlight-md-txt` → raw-markdown URLs — concrete agent-friendliness) ·
  **vocs** ("Minimal Docs for Agents & Humans" — wevm/viem team; minimal, MDX, TS-Twoslash, agent-branded —
  its ethos matches our human-or-agent thesis; Twoslash is TS-specific so less of an edge for `.bang`) · plain
  Astro content-collections. All add a Node toolchain — hence deferred until multi-page. **CHEAP AGENT WIN
  available NOW, no SSG:** generate an **`llms.txt`** (the emerging LLM-doc-index standard) from the git docs —
  same generator pattern as `gen-questions-index`.

## The graph (projects ▸ the features they pull ▸ what they stress)

```
DONE ─────────────────────────────────────────────────────────────────────────────────────
  ✓ tokenizer            strings · recursion · termination-checking          (examples/tokenizer.bang)
  ✓ parser combinators   higher-order · polymorphism · generic data          (examples/parser-combinators/)
  ✓ semantic contracts  laws · named/swappable handlers · policy state      (examples/codec-contract/,
                                                                                stage-swap/, stateful-quota/)
  ✓ one-shot permit     local 0/1/omega · refusal · erased Wasm · evidence  (examples/resource-contract/)

COMPLETED SEAM — the resource description is safe to consume (PATH-contract-query-integrity)
  evidence integrity    subject validity · stable qualified IDs · B018       automation + outsider recovery;
                        parity/location · quiet documented route              fixed before compatibility hardened

DEFERRED LOOP — real unfamiliar use remains required before ◊6 (PATH-organic-resource-validation)
  organic validation    goal-only public journey · chronological trace ·      external correction before another
                        consent · adjudicated findings                         release claim; no validation credit yet

FRONTIER — next projects that pull new capability
  JSON codec             recursive ADTs · Outcome/error handling · strings    grounds the SCHEMA/contract story (Q37)
  2048 (logic)           polymorphic List · refinement types (2^x invariant)  make-illegal-states-unrepresentable
                         · randomness (state capability)                       (the exponent = a power-of-2 by construction)

LIVE PROJECT / KERNEL-EXERCISER — pull an UNDER-USED kernel feature
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

## Route to the north star — paved road, live edge, intended line

This is the zoomed-out route, not a promise that every branch is linear. Each horizon advances only
when the project at its left produces evidence for the feature work at its right.

| horizon | project evidence | capability it earns | systemic-review posture |
|---|---|---|---|
| **paved** | tokenizer, parser combinators, semantic contracts, one-shot permit, compiled examples | real surface; polymorphism; laws and swappable realizations; local quantities; verified/tested execution chain to Wasm | preserve these as the stable semantic-description substrate |
| **deferred pre-◊6 loop** | first unassisted outsider run against repaired contract evidence | external correction loop over a trustworthy machine view | consciously deferred, not complete; prevent leakage/overclaiming and adjudicate observed friction before release claims |
| **now** | checked interfaces render semantic effect names through capability types and nested thunk rows | unrelated earlier effects preserve an unchanged interface; nested-row changes move it; same-named module effects remain distinct; runtime labels and the flat body remain global | keep both 64-bit probes cache-unsafe and the interface explicitly not separate-compilation-ready; next isolate lowered module identity/body/link constraints before designing a store |
| **toolchain project** | BANG tools consume the compiler fact graph | incremental/content-addressed compilation, module graph, LSP/MCP/CLI as views | preserve schema evolution and observation points now; build the scheduler when this consumer measures it |
| **systems wedge** | allocator → cooperative scheduler → filesystem → driver | resource protocols, one-shot scheduling, persistence/location, least-authority IO | scope each rung only when reached; local quantities preserve the allocator door without pre-building ownership |
| **distributed branch** | actor/chat system → replicated log/Raft | sendability, message passing, network capability security, deterministic replay | stays beside the cooperative-OS path until a project requires actor transfer or multi-shot behavior |
| **north star** | verified xv6/unikernel running real workloads | the description/realization thesis at OS scale: effects as syscalls, handlers as runtimes/drivers, grades as resource/capability boundaries | success is an evidence chain, not feature count |

The operator consciously changed the immediate ordering to **spreadsheet evidence now**, while retaining
external correction as an open pre-◊6/release obligation rather than pretending it happened. Evidence
repair is paved. The systems ladder is the destination-bearing branch; the toolchain and distributed projects are
rehearsals for its dependency, authority, observability, and concurrency problems rather than a
detour into completeness.

## How to read / use it

- **Pick the next feature by picking the next PROJECT.** The feature work is then justified and
  scoped by what the project concretely needs — not by completeness.
- **Before freezing the PATH, run the prospective systemic review.** Project pull answers “why this
  capability?”; expected regret answers “which small preventative work becomes expensive if omitted
  now?” (`docs/notes/prospective-systemic-review.md`).
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
