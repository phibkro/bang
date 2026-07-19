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

## Committed sequence (updated 2026-07-19)

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
✓  ▸ SPREADSHEET (reactivity)     live/stale behavior, stable formula DAG, measured recomputation, and
                                  within-observation reuse run end to end; the natural two-operation
                                  capability wall was then closed in concrete Wasm.
✓  ▸ QUERYABLE TOOLCHAIN SPINE    resolver DAG → invalidation measurement → core/interface/body identity
                                  → first BANG fact consumer → canonical artifact + integrity boundary;
                                  inert top-level descriptions now make module execution honest.
✓  ▸ COMPILED BROWSER PACK        JSON, calculator, N-Queens, and sim-KV A/B execute as provenance-pinned
                                  WasmGC+EH artifacts in Chromium and byte-match the live kernel oracle.
?  ▸ NEXT NORTH-STAR LANE         operator-sequenced fork: allocator systems wedge · lattice-store/CALM
                                  distributed branch · wgcexec pure+state verified floor. No evidence
                                  selects one default, and none substitutes for the deferred outside loop.
── wishlist (further out, roughly in dependency order) ──
   kv-store (STM — full payoff needs post-v1 concurrency) · web server · graphics (2048) · OS/distributed
```

**Tooling/product-face state (docs-as-data · ADR-0077/0078):** the previously proposed CI, generated
question ledger, `llms.txt`, dashboard, multi-page Vocs site, Site/Pages workflows, role-oriented
onboarding, and production route smoke are shipped. The docs site now includes the compiled-browser
journey rather than merely describing a future playground. Two optional GitHub-native projections remain
unbuilt—the live `gh` issue-edge bridge and project milestones—but neither binds a product journey. Open
them only when issue/milestone state becomes a real consumer input rather than duplicating GitHub for
completeness.

## The graph (projects ▸ the features they pull ▸ what they stress)

```
DONE ─────────────────────────────────────────────────────────────────────────────────────
  ✓ tokenizer            strings · recursion · termination-checking          (examples/tokenizer.bang)
  ✓ parser combinators   higher-order · polymorphism · generic data          (examples/parser-combinators/)
  ✓ semantic contracts  laws · named/swappable handlers · policy state      (examples/codec-contract/,
                                                                                stage-swap/, stateful-quota/)
  ✓ one-shot permit     local 0/1/omega · refusal · erased Wasm · evidence  (examples/resource-contract/)
  ✓ spreadsheet        live/stale samples · formula DAG · measured calls ·  (examples/reactive-*/)
                       scoped reuse · multi-operation cap on concrete Wasm
  ✓ compiled demos     fixed JSON/calc/N-Queens/sim-KV artifacts execute     (web/docs/static/compiled-demos/)
                       in the deployed browser path and match live oracles

COMPLETED SEAM — the resource description is safe to consume (PATH-contract-query-integrity)
  evidence integrity    subject validity · stable qualified IDs · B018       automation + outsider recovery;
                        parity/location · quiet documented route              fixed before compatibility hardened

DEFERRED LOOP — real unfamiliar use remains required before ◊6 (PATH-organic-resource-validation)
  organic validation    goal-only public journey · chronological trace ·      external correction before another
                        consent · adjudicated findings                         release claim; no validation credit yet

FRONTIER — available projects that pull new capability
  JSON codec ✓           recursive ADTs · Outcome/error handling · strings    shipped; now part of browser pack
  2048 (logic)           polymorphic List · refinement types (2^x invariant)  make-illegal-states-unrepresentable
                         · randomness (state capability)                       (the exponent = a power-of-2 by construction)

AVAILABLE PROJECT / KERNEL-EXERCISER — pull an UNDER-USED kernel feature
  key-value store        STM (the ONE privileged primitive — under-exercised   stresses STM/transactions directly
    w/ transactions      in v1) · concurrency · persistence
  spreadsheet ✓          REACTIVITY (`=`, ADR-0005/6) · dependency DAGs ·      shipped through measured recomputation
    reactive dataflow    scoped reuse · capability-backed memo state           and concrete-Wasm capability closure

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
| **paved** | tokenizer, parser combinators, semantic contracts, one-shot permit, reactive spreadsheet, queryable toolchain spine, compiled browser pack | real surface; polymorphism; laws/swappable realizations; local quantities; observable dependency/artifact boundaries; verified/tested execution chain to Wasm and browser | preserve these as the stable semantic-description substrate |
| **deferred pre-◊6 loop** | first unassisted outsider run against repaired contract evidence | external correction loop over a trustworthy machine view | consciously deferred, not complete; prevent leakage/overclaiming and adjudicate observed friction before release claims |
| **operator-sequenced fork** | allocator project **or** lattice-store/CALM probe **or** wgcexec pure+state floor | systems destination progress **or** distributed momentum **or** deeper checked backing beneath the public compiled stratum | design-first in isolated lanes; compare kill shots before choosing consolidation order; none counts as external validation |
| **toolchain project** | BANG tools consume the compiler fact graph | incremental/content-addressed compilation, module graph, LSP/MCP/CLI as views | preserve schema evolution and observation points now; build the scheduler when this consumer measures it |
| **systems wedge** | allocator → cooperative scheduler → filesystem → driver | resource protocols, one-shot scheduling, persistence/location, least-authority IO | scope each rung only when reached; local quantities preserve the allocator door without pre-building ownership |
| **distributed branch** | actor/chat system → replicated log/Raft | sendability, message passing, network capability security, deterministic replay | stays beside the cooperative-OS path until a project requires actor transfer or multi-shot behavior |
| **north star** | verified xv6/unikernel running real workloads | the description/realization thesis at OS scale: effects as syscalls, handlers as runtimes/drivers, grades as resource/capability boundaries | success is an evidence chain, not feature count |

The spreadsheet, evidence-integrity, toolchain-artifact, inert-declaration, and compiled-demo rotations
are now paved. External correction remains an open pre-◊6/release obligation rather than something an
internal lane can simulate. The next internal move is therefore an explicit three-way operator fork:
systems destination, distributed rehearsal, or verified-floor depth. The systems ladder remains the
destination-bearing branch; toolchain and distributed projects rehearse its dependency, authority,
observability, and concurrency problems rather than forming a completeness detour.

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
