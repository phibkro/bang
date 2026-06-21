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
