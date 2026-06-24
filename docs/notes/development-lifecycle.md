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
| Rows = idempotent `Finset` | ADR-0001; type system | `Bang/Core.lean` (post-Q1: Lattice + OrderBot) |
| Kernel = 5 primitives | ADR / CLAUDE.md invariant 5 | `CLAUDE.md` |
| ADR for reversible decisions | discipline + PR review | `docs/decisions/README.md` |
| Open questions tracked (not silently dodged) | proof-engineer discipline | `docs/notes/OPEN_QUESTIONS.md` |
| Single source of truth (no fact duplicated) | discipline + code review | this doc |

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
| Proof discipline | `docs/notes/spec-proof-discipline.md` |
| Subagent roles | `.claude/agents/*.md` |
| Build / verify | `justfile` + `tools/*.sh` |
| Quality gate | `Bang/Audit.lean` + `tools/audit.sh` |
| Session start | `ONBOARDING.md` |
| Session end | `wrap-session` skill |

If the framework and an artifact disagree, the artifact wins (it's executable;
this is description). Update this doc when reality drifts.
