# bang-lang ONBOARDING

> **Start here on your first session in this repo.** This file walks a new
> contributor (human or agent) through pre-requisite reading, dev environment
> verification, and the daily workflow.
>
> Returning sessions: read `CONTEXT.md` instead — that's the volatile current
> position. This file is for first-time setup + the reference index.

## 1. First-time setup (≤ 10 minutes)

```bash
cd /srv/share/projects/lang-bang
nix develop          # opens Lean 4 dev shell (or auto-via direnv if `direnv allow`)
lake exe cache get   # one-time: pull Mathlib oleans from Azure (multi-GB, minutes)
just install-hooks   # one-time: link pre-commit hook (.git/hooks/pre-commit symlink)
just verify          # selfcheck + lake build + audit  →  expect green
```

If `just verify` exits green and `just burndown` shows the per-module
sorry/axiom counts, you're ready.

**Common stumbles**:
- `nix develop` slow first time (downloads toolchain via elan). Subsequent
  entries are fast.
- `lake exe cache get` is the right way to fetch Mathlib oleans — never
  let `lake build` recompile Mathlib from source. See `docs/notes/dev-env.md`
  on the Mathlib-cache + Nix interaction.
- If `lake build` fails after a `lake update` of a dep, the dep may have
  pulled a newer Mathlib that breaks the cache. Reset
  `.lake/packages/mathlib/` to the manifest's rev or `git checkout
  lake-manifest.json` and rerun.

## 2. Editor

| Editor | Setup |
|---|---|
| **VS Code** (recommended) | Open repo; prompts for `leanprover.lean4` extension (recommended via `.vscode/extensions.json`). Direnv extension picks up the flake. |
| **Cursor / Zed** | LSP-based; works via `.vscode/settings.json` |
| **Neovim** | `lean.nvim` + `nvim-lspconfig` launching `lean --server` |
| **Emacs** | `lean4-mode` |

`.editorconfig` keeps indent (Lean's 2-space, Mathlib convention) consistent.

## 3. Pre-requisite reading (in order)

Read these top-to-bottom on your first session. Skim then return as needed.

1. **`CLAUDE.md`** — invariants, glossary, current architecture-in-force
2. **`CONTEXT.md`** — current position on the map (what's done, what's pending)
3. **`ROADMAP.md`** — long-term checkpoint map (◊1 → ◊6)
4. **`docs/decisions/0016-two-hop-architecture-calcvm-and-wasmfx.md`** —
   the architecture decision currently in force
5. **`docs/notes/spec-handover.md`** — why the wasmfx spec is engineer-ready,
   not still-in-design
6. **`docs/notes/spec-proof-discipline.md`** — proof invariants (sorry rules,
   axiom hygiene, PROOF_ORDER)

Skim on first visit; deep-read when relevant to your task.

## 4. Reference index (on-demand — progressive disclosure)

| Topic | Where | When to consult |
|---|---|---|
| **Project state** | `CONTEXT.md` | Every session start |
| **Long-term map** | `ROADMAP.md` | Planning a new path |
| **Active path doc** | `paths/PATH-*.md` | Resuming in-flight work |
| **Architecture in force** | `docs/decisions/0016-*.md` + ADR README | Touching the kernel or proof spine |
| **ADR index** | `docs/decisions/README.md` | Looking for "why we chose X" |
| **Open design questions** | `docs/notes/OPEN_QUESTIONS.md` | Considering a design pivot or before adopting a fresh assumption |
| **Proof discipline** | `docs/notes/spec-proof-discipline.md` | Before writing any proof body |
| **Tactics survey** | `docs/notes/tactics-survey.md` | When closing a sorry; what to try |
| **K2 calc playbook** | `docs/notes/k2-calculation-playbook.md` | If touching `Bang/Calc*.lean` (legacy K3) |
| **Dev environment** | `docs/notes/dev-env.md` | When something doesn't build |
| **K-keyframe roadmap** | `docs/roadmap/bang-northstar-roadmap.md` | Research-grade roadmap (complementary to ROADMAP.md) |
| **Original design spec** | `docs/spec/bang-lang-{design,description-value}.md` | Reading the language thesis; superseded in part by ADR-0016 |
| **References library** | `references/README.md` | Citing a paper or looking for a lemma source |
| **Per-paper notes** | `references/notes/<key>.md` | Reading a paper for the first time (created on demand) |
| **Lifecycle / feedback loops** | `docs/notes/development-lifecycle.md` | Understanding HOW work flows |
| **Subagent definitions** | `.claude/agents/*.md` | Invoking domain-specific roles |

## 5. Daily workflow

```
ITERATE                                       VERIFY
───────                                       ──────
edit a file                                   just check Bang/Spec.lean
                                              (single-file, fast)
…repeat…
                                              just verify
                                              (full: selfcheck + build + audit)
                                              just burndown
                                              (where are remaining sorrys?)
COMMIT                                        AUDIT
──────                                        ─────
git add ...; git commit -m ...                pre-commit hook runs static
                                              guards automatically
                                              (just install-hooks once)
```

### Tool selection (which `just` recipe when)

| Situation | → Tool |
|---|---|
| editing one file, iterating fast | `just check Bang/Spec.lean` |
| about to commit | `just verify` (full gate) |
| want to see remaining sorry/axiom work | `just burndown` |
| exploring a Lean expression | `echo '#check X' \| just eval` |
| looking for a Mathlib lemma by shape | `just loogle "?n + 0 = ?n"` |
| confirming axiom hygiene per theorem | `just axioms` |
| Mathlib oleans missing or stale | `lake exe cache get` (inside `nix develop`) |
| build is mysteriously broken after `lake update` | reset `.lake/packages/mathlib` to manifest's rev (see dev-env.md) |
| just want the recipe list | `just` (no args) |

**Rule of thumb**: use the tightest loop that can detect the issue. Don't
wait for `just verify` when `just check Bang/Spec.lean` would have caught
it in 2 seconds.

### Editor / LSP feedback (tightest of all)

For continuous proof-state feedback (goals, hover types, error squiggles),
open the file in VS Code with the `leanprover.lean4` extension. The LSP
gives per-keystroke feedback; the `just check` script gives per-file
feedback after editor disagreement; `just verify` is the per-commit gate.

## 6. When to write / update which doc

| What | Where to record it |
|---|---|
| Reversible design decision | New ADR under `docs/decisions/` |
| Deferred design question | `docs/notes/OPEN_QUESTIONS.md` |
| Resolved question | Edit the OPEN_QUESTIONS entry (mark `✓ RESOLVED`) |
| Path start | `paths/PATH-<slug>.md` (copy `_template.md`) |
| Path progress | Update the `PATH-*.md` Status block |
| Path complete | Remove from `CONTEXT.md` Active Paths; commit is the durable record |
| Checkpoint reached | Update `CONTEXT.md` Position; bump `ROADMAP.md` if needed |
| New dev-env tool | `docs/notes/dev-env.md` + a `just` recipe |
| New tactics discovery | Append to `docs/notes/tactics-survey.md` |
| Reading note on a paper | `references/notes/<bib-key>.md` |
| Reference paper added | Drop in `references/papers/<topic>/`, add `refs.bib` entry, update `references/README.md` |

## 7. Session end / wrap-up

```bash
# Verify clean state
git status                # working tree clean?
just verify               # build still green?

# Update orientation docs if state shifted
# - CONTEXT.md if checkpoint moved, path landed, blocker resolved
# - PATH-*.md if mid-flight work needs handoff
# - OPEN_QUESTIONS.md if a Q got answered

# Commit any doc updates
git add -A; git commit -m "docs: end-of-session wrap-up"

# Use the wrap-session skill for a structured handoff
```

The `wrap-session` skill walks through this checklist + produces a compact
handoff for the next agent. Invoke it when the user signals "wrap up",
"that's it for now", "done for today".

## 8. Health-check command

If anything seems off, this single command tells the full story:

```bash
nix develop --command just verify
```

Expect: selfcheck pass → lake build 729+ jobs → tools/audit.sh static
guards pass → axiom-burndown report per theorem. If red anywhere, the
first error message is usually the right place to start debugging.

## 9. Project lifecycle in one sentence

Two pipelines meet at theorem statements: **research** (literature →
question → frozen statement) hands off to **engineering** (statement →
definition → proof → kernel-checked artifact). See
`docs/notes/development-lifecycle.md` for the full framework + feedback
loops + quality gates.
