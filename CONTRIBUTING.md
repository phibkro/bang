# Contributing to bang-lang

Welcome — human or agent. This is the entry point: it tells you how the project is organized, where
knowledge lives, and how a change gets from an idea to `main`. It **routes** to the authoritative docs
rather than repeating them (single source of truth), so follow the links.

> **One idea underneath everything:** correctness by construction + *generate, don't hand-maintain*. Illegal
> states are made unrepresentable (types over runtime checks); derived facts (docs, indexes, the changelog)
> are generated from a single source so they can't drift. Every rule below is a consequence of that.

---

## 1. Orient (read in this order)

| Read | For |
|---|---|
| **`CLAUDE.md`** | the always-loaded core — invariants (never break these), the glossary, architecture-in-force, the verify command |
| **`CONTEXT.md`** | where the project is **right now** (volatile; the lead is the current position) |
| **`ROADMAP.md`** + **`docs/roadmap/project-roadmap.md`** | where it's going — the ◊ proof-map, and the **product-axis DAG** (projects → the features they pull) |
| **`ONBOARDING.md`** | first-time setup + a tighter reference index |

Everything else is on-demand — the tables in `CLAUDE.md` and `docs/notes/README.md` index it.

---

## 2. The knowledge map — where documentation belongs (ADR-0077)

Docs are placed by **(audience × temporality)**. Knowing a doc's coordinate tells you its home, its
lifecycle, and how it's maintained:

```
             PRODUCT  (the artifact, a snapshot — for USERS)   PROJECT  (the work, time-indexed — for CONTRIBUTORS)
             GENERATED from code · publishable                 ┌ DONE (immutable): CHANGELOG · ADRs · git history
             docs/reference/language.md · PRD · README ·       ├ NOW  (volatile):  CONTEXT.md · paths/
             ONBOARDING                                        └ NEXT (revisable): ROADMAP · project-roadmap ·
                                                                                   OPEN_QUESTIONS (the design ledger)
```

**Deciding where your doc goes:** are you describing the thing as it *is* (→ product, and prefer to
*generate* it from the code) or the *work* of building it (→ project, and which tense — done/now/next)?
Putting a "future feature" line in the product reference, or a "current status" line in a timeless doc, is a
category error that will drift. Full rationale: **ADR-0077**.

---

## 3. Where knowledge lives, and how it's stored (ADR-0078)

**Docs are git-native.** The design ledger, ADRs, and notes are files in this repo — because the top
priority is that documentation be **directly readable by AI agents** (an agent reads the repo; a hosted tool
needs an API round-trip). Git files are also diffable, PR-reviewed, and generated-from-frontmatter.

- **Design decisions** (a fork future work could reverse) → an **ADR** in `docs/decisions/` (copy an existing
  one's shape; record the *rejected* alternatives, not just the choice). The ledger `docs/decisions/README.md`
  is **generated** from ADR frontmatter — don't hand-edit it.
- **Open design questions** (a fork not yet decided) → an **OKF file** in `docs/notes/questions/` (frontmatter:
  `type/title/description/status/area/ties/see-also`). `OPEN_QUESTIONS.md` is a **generated** multi-view index
  (by area, by status, a validated tie-graph) — edit the *question file*, then `just questions-index`. A `ties:`
  edge to a nonexistent question/ADR **fails the build** (dangling edges are unrepresentable).
- **Volatile state** (current position, blockers, active work) → `CONTEXT.md` / `paths/PATH-*.md`.
- **History** → git commits. Don't narrate the past in docs ("we used to X") — the commit message holds it.

**Project management is GitHub Issues** (not a doc file) — issues, milestones, labels, the Projects board.
Issues and docs cross-reference via `#N` in a question's `see-also`; a **gh-bridge** (roadmap) resolves those
into the tie-graph, so issues ↔ questions ↔ ADRs form one queryable graph across two well-chosen stores. Full
rationale (and why *not* the Wiki / Linear / Jira): **ADR-0078**.

---

## 4. Set up

```
nix develop          # ENTER THE DEV SHELL FIRST — bare lake/just/node are NOT on PATH
just verify          # the default gate: selfcheck (Node) + lake build + audit
just                 # list all recipes
```

First `lake` build pulls Mathlib (`lake exe cache get`; network, minutes). See `docs/notes/dev-env.md` for
the flake/scripts/gotchas.

---

## 5. The change workflow

```
issue (GitHub)  →  branch  →  make the change  →  the VERIFY GATE  →  PR (closes the issue)  →  review  →  main
```

- **Branch** off `main` (never commit to `main` directly). Conventional-commit subjects (`feat(scope): …`,
  `docs(scope): …`, `fix(scope): …`) — the CHANGELOG is generated from them.
- **The verify gate** — before you claim done, run it and read the **real exit code**:
  ```
  just verify         # selfcheck + lake build + audit
  just fitness        # the derived-doc gate: adr-check · reference · questions-index · hygiene · changelog · …
  just axioms         # for proof work: #print axioms per headline theorem
  ```
  **Green means:** `lake build` clean, `fitness` exit 0, and (for proofs) each headline theorem's axiom set ⊆
  `{propext, Classical.choice, Quot.sound}`. Gate-traps to avoid: a piped exit code (`cmd | head` is always
  0), and `grep "sorry"`/`grep "error:"` (use `#print axioms` and the build exit code — see `CLAUDE.md` §"How
  to verify").
- **Gate the *committed* content**, on a clean tree — never a summary, a dirty worktree, or your own say-so.

---

## 6. If you are an AI agent

The workflow above holds, plus a hard-won discipline for **agents that write files**:

- **No-git-writes for spawned ICs.** An IC works in its own worktree (`tools/new-worktree.sh <path> <branch>
  main` — never a bare `git worktree add`), builds + gates *there*, and hands the finished files back; the
  manager lands them on `main`. One writer per file. Verify isolation (`git worktree list`); don't assume it.
- **`git add` new files IN the worktree before running `just fitness`** — hygiene checks scan `git ls-files`,
  so untracked files give a **false green**. Gate on tracked content.
- **Gate the artifact, not the claim.** A confident wrong summary is the same failure as a green stub — go
  look at the real build / diff / proof. Verify your *own* claims the same way; welcome being checked.
- **Send a full report** when you finish (what landed, every gate result, judgment calls) — never just go idle.
- **Memory** persists across sessions in the auto-memory dir (one fact per file + a `MEMORY.md` pointer). Save
  the *non-obvious* (a gotcha, a preference, project state) — not what the repo already records.

The `.claude/agents/` role files (`kernel-engineer`, `proof-engineer`, `lean-proof-auditor`) define
specialist agents; the manager/IC split and the full incident log live in the auto-memory.

---

## 7. Never break these (the invariants)

The load-bearing invariants — the kernel's five primitives (thunk · force · effect rows · handlers · STM),
effect rows are **sets**, STM is the only privileged primitive, the machine is *calculated* not hand-designed,
no implicit capture — are in **`CLAUDE.md` §"Invariants — never break these"** and the **`Do NOT`** list.
Read them before touching the kernel. Adding a sixth primitive, ordering rows, or hand-designing the VM is a
spec change requiring an ADR.

---

Questions about *how* to contribute → open a GitHub Discussion or issue. Questions about *what the language
should be* → the design ledger (`docs/notes/questions/`) is where those live and get grilled.
