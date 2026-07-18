<!-- note-status: active -->
# bang-lang development lifecycle

> How work flows through the project. The frame for picking the right tool /
> doc / cadence at each moment. Inspired by Lean's verified-software ethos,
> agile's iteration discipline, and DevOps' feedback-loop instrumentation —
> adapted for verified-PL research where the artifact IS the proof.

## The two pipelines

bang-lang is two projects in one repo:

```
RESEARCH (slow, deep)                ENGINEERING (fast, shallow)
─────────────────────                ────────────────────────────
literature   ─ survey ─►              theorem statement ─ define ─►
open question ─ specify ─►            opaques replaced
THEOREM STATEMENT  ←─────────────────┘  proof body filled
       │  (the boundary object;             │
       │   ADRs preserve the why)           │  audit (#print axioms)
       │                                    │  burndown
       ▼                                    ▼
proof discharged              build green + clean axiom set
       │                                    │
       └──────────► PAPER ◄─────────────────┘
                  (or theorem)
```

**The theorem statement is the contract** between the two pipelines.
Once frozen (`Bang/Spec.lean`), engineering can proceed without re-deriving
design. Research can iterate on what to prove without breaking what's already
built.

## Phases (cyclic, not strictly linear)

```
1. DISCOVERY      research-leaning      identify question, survey literature
2. DESIGN         research → eng        freeze theorem statements + ADRs
3. CONSTRUCTION   engineering           turn opaques into defs, prove sorrys
4. VALIDATION     cross-cutting         #print axioms + lake build + audit
5. INTEGRATION    engineering           cross-module coherence; module split
6. MAINTENANCE    operations            docs current, deprecations, gardening
```

A typical PATH-*.md unit cycles through 2-3 of these phases. ◊-checkpoints
in `ROADMAP.md` are stable poses at the end of an integration phase.

## Product increments — actor-terminal tracer bullets

The phases above describe kinds of work; they do not define product completion. An actor-visible
feature advances through the smallest **vertical tracer bullet** that reaches a terminal user
observation through the real public surface:

```text
actor need → public entrypoint → parse/check/lower → semantic + execution route
           → visible result/evidence → realistic mistake → diagnosis/recovery
```

Each product PATH names:

- the actor and starting public surface;
- the terminal observation that changes what the actor can accomplish;
- the smallest adverse or mistake-and-recovery case that could falsify usability of the route;
- the proof, differential, schema, CLI, or artifact evidence that supports the observation; and
- assumptions, exclusions, and the observation that would reopen acceptance.

Internal layers going green are necessary evidence, not product acceptance. A feature closes only
when its actor reaches the terminal outcome end-to-end; proof-only or infrastructure work instead
names the downstream actor journey it releases. Begin with the thinnest coherent bullet, then thicken
coverage, performance, and generality when observations demand them.

Maps and plans label each material claim **executable**, **designed**, or **planned**. A precise future
journey is still planned until its public gate exists and runs; design detail is not delivery evidence.

An executable journey test and user research are different evidence. The journey test deterministically
checks a public terminal outcome and recovery route. Agentic usability inspection probes discovery and
workflow hypotheses. Organic user testing supplies human behavior and context. None may be silently
renamed as another; the current calibration method lives in `.claude/skills/agentic-user-testing/`.

This makes the product lifecycle:

```text
intent + actor outcome → baseline/falsifier → design + systemic review
  → vertical tracer bullet → evidence + independent convergence
  → observe/maintain → explicit successor when inputs or findings change
```

## Feedback loops (macro → micro)

Tight inner loops; staged outer loops. The aim is **silence has meaning** at
each level — quiet implies clean.

```
LOOP                CADENCE          TOOL                          WHAT IT CHECKS
────                ───────          ────                          ──────────────
in-editor            keystroke        VS Code Lean LSP              goal state, type info, hover
per-file             1-10 sec         just check FILE                single-file Lean errors
per-snippet          1-5 sec          just eval (stdin)              type / value of an expression
per-commit           tens of sec      git pre-commit hook            no admit / no stray axioms
per-build            seconds (warm)   just verify                    selfcheck + build + audit
                     minutes (cold)
per-audit            seconds          just axioms                    #print axioms per theorem
per-PATH scope       hours to days    prospective systemic review    future debt classified before scope freezes
per-product PATH     hours to days    public journey + adverse case  actor reaches a terminal outcome and can recover
per-PATH             hours to days    PATH-*.md status block         checkpoint definition met
per-checkpoint       days to weeks    ROADMAP.md ◊ progression       architecture coherent
per-OPEN_QUESTION    weeks            OPEN_QUESTIONS.md revisits     design pivot ready or not
per-paper            months           research output                novel contribution holds up
```

**Use the tightest loop that can detect the issue.** Don't wait for `just
verify` when `just check Bang/Spec.lean` would have caught it in 2 seconds.

## Quality gates (invariants — what we never violate)

| Invariant | Enforced by | Where defined |
|---|---|---|
| `lake build` green | CI / `just verify` | `Bang.lean` root + lakefile |
| No `admit` outside Audit | `tools/git-hooks/pre-commit` | `tools/git-hooks/pre-commit` |
| No `axiom` outside `Bang/Spec.lean` family | pre-commit hook | same |
| `#print axioms` ⊆ {propext, Classical.choice, Quot.sound} | `Bang/Audit.lean` + `just axioms` | proof-engineer subagent |
| Theorem statements frozen | discipline (proof-engineer) | `docs/notes/spec-proof-discipline.md` |
| Rows = idempotent `Finset` | ADR-0001; type system | `Bang/Core/IR.lean` (post-Q1: Lattice + OrderBot) |
| Kernel = 5 primitives | ADR / CLAUDE.md invariant 5 | `CLAUDE.md` |
| Every `Bang/**/*.lean` is a `module` (or an allowlisted exception) | `tools/check-all-modules.sh` (`just fitness`) | the inline exception allowlist (currently `Bang/Frontend/Surface/PropTest.lean`, temp — retired by #80) |
| ADR for reversible decisions | discipline + PR review | `docs/decisions/README.md` |
| Open questions tracked (not silently dodged) | proof-engineer discipline | `docs/notes/OPEN_QUESTIONS.md` |
| Single source of truth (no fact duplicated) | discipline + code review | this doc |

## Prospective systemic review (the expected-regret judgment gate)

Before a PATH plan freezes, ask: **how likely is it that not doing this work now will become an
issue, and how much more expensive will correction be after the seam hardens?** The detailed method,
lenses, evidence standard, and lifecycle triggers live in `prospective-systemic-review.md`.

Every material concern receives one disposition: **implement now**, **preserve the smallest useful
door**, **defer with an observable trigger**, or **reject**. Public schemas/IDs/diagnostics, persisted
formats, security boundaries, and checkpoint/release changes require the full review. Routine local,
reversible edits need only the five-question delta screen; do not manufacture process artifacts when
there is no material future pressure.

This is a judgment gate, not a new quality invariant or a completeness checklist. Project pull still
decides what to build. The review catches preventative work whose later migration, authority, or
cross-layer cost would otherwise be invisible.

## Proportional evidence and retained successors

Every change keeps an observable outcome, the cheapest useful falsifier, relevant evidence, exclusions,
and a reopen or recovery condition. The evidence shape scales with the claim:

| change | minimum path |
|---|---|
| actor-visible feature | public end-to-end journey, adverse/recovery case, narrower checks, docs, observation owner |
| defect | reproducer first, minimal repair, regression plus adjacent route parity, release observation |
| refactor | characterized behavior and a sensitivity control that would notice meaningful drift |
| optimization | named workload and measured deficit before implementation; semantic/safety gates remain |
| governance or methodology | bounded experiment with baseline, hypothesis, canary scope, safety invariants, independent review, observation window, and rollback |

A failed gate or material review is not rewritten into an eventual pass. Retain the failed observation
in the PATH and create a named successor step when correction changes the evidence boundary. Keep ordinary
red/green/refactor moves inside one work package; promote them to explicit successor nodes only when they
release another owner, change a shared contract, cross an authority boundary, or preserve a consequential
failed review.

## Recursive, multi-model project improvement

The project lifecycle may improve itself, but cannot self-ratify by redefining its success criteria.
Treat process changes as the governance experiments above. Compare observed cycle time, escaped defects,
recovery quality, or review yield against a baseline; retain a rollback when added ceremony does not pay.

Use model/provider diversity to probe correlated blind spots across research, design, implementation,
maintenance, and skeptical review. Frame independent reviewers on the same governing question before
showing them a preferred answer. Fuse propositions, counterexamples, and executable evidence—never votes,
model reputation, or averaged confidence. Model identity grants neither authority nor assurance.

Cross-provider delegation must use the operator-approved dispatcher and a bounded brief: observable
outcome, governing artifacts, read/write and disclosure scope, required evidence, non-goals, falsifier,
stop conditions, requested/runtime model provenance, and fallback. Read-only prevents mutation, not
disclosure. A denied, stalled, substituted, or contradictory consultation remains an observation rather
than disappearing behind the eventual result.

### Small-project default: continuous owner + strategic advisor

For a project small enough that one implementation context can still hold its map, prefer **one
continuous implementation owner** across end-to-end tracer bullets. Persist the high-level state in
`CONTEXT.md`, the active `PATH`, and the governing Q/ADR between bullets; do not make handoff summaries
the only project memory. Add one persistent **read-only strategic advisor** (ideally a different model
provider) when its independent map-level challenge is worth the coordination cost. In Herdr, keep that
advisor observable in a secondary tab rather than spawning opaque consultations repeatedly.

The cadence is:

```text
owner orients from durable map → scopes one tracer + falsifiers → implements through the public journey
→ converges and persists evidence → reports landed facts, exclusions, and residual coupling to advisor
→ advisor ranks/challenges the next constraint → owner verifies that advice against artifacts and repeats
```

The advisor does not edit, approve, or supply delivery evidence. Its report contains a ranked next move,
the strongest counterargument, likely scope creep, and the observation that would change its ranking.
The owner remains accountable for inspecting code, running gates, updating the map, and deciding whether
the recommendation follows from evidence. Delegate additional workers only when work is genuinely
separable and their expected parallel gain exceeds merge, waiting, and context-transfer cost.

This is a bounded governance experiment, not a permanent role topology. Observe context pressure,
cycle time, escaped defects, review yield, and time spent waiting or reconciling summaries. Fall back to
one owner with bounded consultations when the advisor becomes low-yield or cumbersome; widen to explicit
feature owners only when the repo no longer fits one continuous context. No advisor agreement counts as
organic user evidence or independent verification.

The comparative evidence behind this adoption and its canary/rollback conditions are recorded in
`semantic-packages-lifecycle-review.md`.

## Value alignment (soft invariants — preferences)

These are not enforced mechanically; they shape decisions when the strict
rules don't decide.

```
correctness > sunk cost              don't keep a wrong proof because it took time
calculation > design                  if a machine can be derived, derive it
minimality > generality               5 primitives over 6
explicit > implicit                   no hidden state, no implicit force, no autosubscribe
single source of truth                two copies of a fact will diverge
surface uncertainty                   `sorry` with a clear comment > a wrong proof
research-software seam discipline     each theorem statement has an engineering artifact
follow the literature                 borrow shape from Biernacki / Torczon / Bahr-Hutton
```

## Design philosophy — the through-line

The invariants (above, and in `CLAUDE.md`) are not a grab-bag; they express **one sensibility**, worth
stating so a fresh designer can grok the *why* fast. bang is **"make the bad state unrepresentable"
(the SOUL) applied recursively to language design**:

- **Stratify: verified core + tested superset + an explicit seam.** The single load-bearing model
  (`CLAUDE.md`, ADR-0028). It recurs at three levels — correctness (ADR-0026 ladder), tooling (Lean
  spine / diff-tested surface), language (total / `Div` fragment). Descent is *always marked*.
- **Minimal kernel, everything-as-library.** Five primitives; paradigms, runtimes, even *unsafety and
  divergence* are effects + handlers (Q16), not language features. Add a primitive only when
  irreducible (ADR + invariant #5). A pseudoinstruction (alias/macro over a composite) is not a primitive.
- **Correctness is a chosen ladder, not a binary** (ADR-0026). verified > tested > unsafe, dispatched
  per-obligation. You do *not* prove everything — you prove the core (sound floor, by construction, the
  Rust-like part) and *test* the superset (assert + `plausible`). The moat is two-level.
- **Constraints are generative.** The effect row is not only a restriction — it *licenses* capability:
  the `⊥`-row permits compile-time folding (Q15); the `Div`-row gates eager eval; the row is the
  firewall that makes the verified/tested seam safe. An invariant is what lets the optimiser fire.
- **Proof rides the reference** (invariant #1). Anything that runs has an oracle — a proof, a
  differential test, or fuel. Never an execution path with nothing behind it.
- **Calculate, don't hand-design** (ADR-0009/0016). The machine is an *output* of calculation
  (Bahr-Hutton), not verified after the fact.

Read top-down: *stratify* is the shape; *minimal kernel* is how the core stays small; *the ladder* is how
the superset stays honest; *constraints are generative* is why the discipline pays; *proof rides the
reference* and *calculate* are the two non-negotiables underneath.

## The orchestrator's view (the two spines + multi-agent work)

The "two pipelines" frame above (research/engineering) is the *proof* view. The **product turn** (PRD,
2026-06-22) added a second axis a managing orchestrator must hold:

**Two spines, and they are COUPLED.**
```
PRODUCT spine (surface · tested rung)        VERIFICATION spine (kernel/compiler · verified rung)
  the ladder rungs (PRD §3.1):                 the ◊ checkpoints (ROADMAP):
  rung 0 RUNS · rung 1 STATE · rung 2 STACK    ◊2 kernel · ◊3 CalcVM · ◊4 LR · ◊5 compiler
            └──────────────── coupled by ONE-KERNEL-FEATURE-PER-RUNG ────────────────┘
```
They are the stratification's two halves (ADR-0028) — but **not freely parallel**. *Each product rung
pulls a kernel feature*: rung 1 needed resumptive state (Q12 → ADR-0025); rung 2 needs ADTs (Q18 →
ADR-0029). So the product spine is **kernel-first** — it generates requirements *into* the verification
spine. Expect every rung = a kernel ask (kernel + proof) + a surface/lib follow-on. (This corrects the
ROADMAP's earlier "product runs in parallel freely" optimism.)

**The delegation triad** (how a rung gets built):
```
kernel-engineer  →  design the kernel feature + machine + the ADR (the crux: can it be type-preserving?)
proof-engineer   →  discharge the metatheory obligations (preservation/progress), axiom-clean
surface IC       →  parser/lowering/lib + the tested-rung laws (plausible)
```
Sequence them (same file → serialize) or worktree-parallelize (different files → `isolation: worktree`;
the agent's diff auto-merges into main on completion). Fan-out reads, serialize writes.

**Manager discipline (non-negotiable):**
- **Verify artifacts, not summaries.** Run `just verify` + `lake env lean Bang/Audit.lean` *yourself*;
  check the agent's claims against the audit before committing. Pre-compute oracles (hand-trace expected
  values) so you can *check*, not trust.
- **The gate holds every commit:** `no_accidental_handling` 0-axiom + headline theorems ⊆ {propext,
  Classical.choice, Quot.sound}. ◊2 must never regress.
- **`STATEMENT_CHANGE_OK="why"`** to commit new/renamed theorems (additive helper lemmas count).
- **Doc-as-you-go:** every decision → ADR immediately, then propagate (OPEN_QUESTIONS · design-space-map
  · CONTEXT · README index). The maintenance pass catches residue; don't let CONTEXT drift.

**Design forks → the grilling cadence.** When a decision is the *operator's* to make (the proof-power
dial, polymorphism, iso- vs equi-recursive): present a **strawman + 2–4 pointed questions**, let the
answers become an ADR. Don't decide solo what the operator's vision should settle; don't *ask* what you
can derive from existing ADRs. (This session's whole design corpus — ADR-0026..0029 — came from four such
grills.)

> **Before grilling or opening a design question, read the generated decided-ledger**
> (`docs/decisions/README.md`) — a question with an ADR is **closed**; `grep docs/decisions/` first.
> The ledger is generated from ADR frontmatter (`just adr-index`) and gated by `just adr-check`
> (ADR-0042); a grilling session once re-derived an already-decided question (Q19/ADR-0040) because
> the hand-maintained ledger had drifted. Don't repeat it.

**Session economics.** A big design+build stretch should *checkpoint before* a large fresh build. Scope
a rung (write its `PATH-*.md`) so it is cold-start-ready, then hand off — don't start the implementation
on a tired context. `/codebase-maintenance` + a handoff doc is the clean close.

## The session lifecycle

```
SESSION START
─────────────
  Read CLAUDE.md → CONTEXT.md → ROADMAP.md (in order)
  If active path: read paths/PATH-<slug>.md
  If proof work: read docs/notes/spec-proof-discipline.md
  Verify locally: nix develop; just verify

WORKING SESSION
───────────────
  Pick the right loop: file-level / build-level / audit-level
  When scoping a PATH: record its prospective systemic review before freezing the plan
  When a design Q surfaces: log to OPEN_QUESTIONS.md (don't silently mutate)
  When a reversible decision is made: write an ADR
  When stuck: try `just loogle "..."` or invoke the right subagent

SESSION END
───────────
  git status clean
  just verify green
  Update CONTEXT.md if state shifted
  Update PATH-*.md if mid-flight
  /wrap-session for structured handoff
```

## Project lifecycle inspirations

Where each tradition contributes a discipline we've adopted:

| From | What we borrowed |
|---|---|
| **Verified PL research** (CompCert, CakeML, Iris) | Theorem statement as boundary object; audit gate via `#print axioms`; calculate-then-prove (Bahr-Hutton) |
| **Lean / Mathlib** | tactic-rich proof environment; `cache get` discipline; `decide` for finite cases |
| **Agile** | short feedback loops; PATH = mini-iteration; checkpoint = release |
| **DevOps** | reproducible env (Nix flake); pre-commit hooks as guardrails; CI as the strict gate (deferred — no remote yet) |
| **Lean (process)** | single source of truth; remove waste (delete legacy K3 machines at ◊3, not before) |
| **Algebraic-effects research** (Plotkin-Pretnar, Biernacki, Torczon) | row-of-labels effect algebra; small-step + eval contexts; logical relations for compiler correctness |

## When to ESCALATE vs work through

```
ESCALATE (stop, ask the orchestrator):
  - Theorem statement appears wrong (not just hard)
  - PROOF_ORDER blocks meaningful progress
  - An OPEN_QUESTION needs a design choice you can't make solo
  - The cost of continuing is now > the cost of pausing

WORK THROUGH (proof-engineer subagent territory):
  - Sorry'd theorem with clean axiom set → discharge body
  - Compat lemma in the STD block → mechanical
  - Stuck on a specific tactic → try grind / aesop / loogle
```

## Anti-patterns to catch

- **Mutating a theorem statement to make a proof close** — violates the
  research-engineering seam. The statement is the contract.
- **Silently dodging an OPEN_QUESTION** — log it; don't paper over.
- **Adding a feature without an ADR for a reversible choice** — drift accumulates.
- **Letting docs go stale** — CONTEXT.md drift is the worst kind because
  fresh agents land on it. Update or delete; don't lie.
- **Skipping `just verify` "just this once"** — the pre-commit hook will
  catch obvious cheats but not subtle type errors.
- **Adding a CI without a remote** — cargo-cult. Add when there's a remote.

## Where this doc sits

This is the FRAMEWORK. Concrete artifacts that implement each piece:

| Framework element | Implementation |
|---|---|
| Pre-requisite reading | `ONBOARDING.md` |
| Current position | `CONTEXT.md` |
| Long-term map | `ROADMAP.md` |
| Active work | `paths/PATH-*.md` |
| Design memory | `docs/decisions/` (ADRs) |
| Open questions | `docs/notes/OPEN_QUESTIONS.md` |
| Prospective systemic review | `docs/notes/prospective-systemic-review.md` |
| Proof discipline | `docs/notes/spec-proof-discipline.md` |
| Subagent roles | `.claude/agents/*.md` |
| Build / verify | `justfile` + `tools/*.sh` |
| Quality gate | `Bang/Audit.lean` + `tools/audit.sh` |
| Session start | `ONBOARDING.md` |
| Session end | `wrap-session` skill |

If the framework and an artifact disagree, the artifact wins (it's executable;
this is description). Update this doc when reality drifts.
