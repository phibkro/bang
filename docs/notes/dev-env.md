# Dev environment

> How to set up + use the bang-lang dev tooling. Most things "just work"
> after `nix develop`; this doc lists the levers and what each does.

## First-time setup

```bash
cd /srv/share/projects/lang-bang
nix develop          # opens Lean 4 dev shell (or auto-entered via direnv)
lake exe cache get   # one-time: pull Mathlib oleans from Azure (multi-GB)
make verify          # selfcheck + lake build + tools/audit.sh
bash tools/install-hooks.sh   # one-time: link git pre-commit hook
```

Direnv (`.envrc` uses `use flake`) auto-enters the dev shell on `cd` once
`direnv allow` is run.

## Editor

| Editor | What works |
|---|---|
| **VS Code** (recommended) | Open the repo; VS Code prompts to install `leanprover.lean4` (recommended via `.vscode/extensions.json`). Direnv extension picks up the flake env. |
| **Cursor / Zed** | LSP-based; works with `lean.serverEnv` from `.vscode/settings.json` |
| **Neovim** | `lean.nvim` + `nvim-lspconfig` configured to launch `lean --server` |
| **Emacs** | `lean4-mode` |

`.editorconfig` keeps indent (2-space, Mathlib convention) consistent.

## Make targets

| Command | What it does |
|---|---|
| `make verify` | Default. selfcheck + build + audit. |
| `make build` | `lake exe cache get && lake build` (incremental after first run). |
| `make audit` | `tools/audit.sh` — static guards + axiom-set report per theorem. |
| `make selfcheck` | Zero-dep Node smoke test of the row-unifier algorithm. |
| `make clean` | Remove `.lake/` build artifacts. |

## Scripts (`tools/`)

| Script | Purpose |
|---|---|
| `audit.sh` | Static cheat-grep + `lake build` + `lake env lean Bang/Audit.lean`. The full gate. |
| `check.sh [FILE]` | Fast per-file Lean error check. With no arg, full build. With `Bang/Spec.lean`, just that file's errors. Tightest dev feedback loop. |
| `burndown.sh` | Phase B burndown chart — pending `sorry`/`axiom` counts per `Bang/*.lean` file. Visible progress metric. |
| `selfcheck.mjs` | Zero-dep Node smoke test for the row-unifier algorithm. Pre-Lean sanity. |
| `install-hooks.sh` | Symlink `tools/git-hooks/*` into `.git/hooks/`. One-time setup. |
| `git-hooks/pre-commit` | Fast static check on each commit: no `admit`, no axioms outside `Bang/Spec.lean`. Skip with `git commit --no-verify`. |

## Iteration loop (recommended)

For Phase A part 2 / Phase B work:

```bash
# Edit Bang/Spec.lean or Bang/Compat.lean or Bang/Eval.lean ...

bash tools/check.sh Bang/Spec.lean     # fast: just this file's errors
# repeat until clean

make audit                              # full gate before committing
bash tools/burndown.sh                  # see remaining sorrys/axioms

git add -A && git commit -m "..."       # pre-commit hook runs static guards
```

`tools/check.sh Bang/Spec.lean` is faster than `make build` because it
type-checks just one file (still pulling its dependencies via the lake
cache). Use this constantly while editing.

## Audit + #print axioms

The real Phase B gate is `Bang/Audit.lean`. Run it directly:

```bash
nix develop --command lake env lean Bang/Audit.lean
```

Output: each headline theorem's transitive axiom dependencies. Phase B
closes when each set ⊆ `{propext, Classical.choice, Quot.sound}`.

Currently (Phase A part 1) the burndown shows `sorryAx` plus the
specific axioms each theorem touches (e.g. `lr_fundamental` depends on
`[sorryAx, Crel, HasCTy]`). Each axiom is a Phase B target.

## Tools to consider adding (deferred)

| Tool | Why deferred | When to add |
|---|---|---|
| `loogle` (Mathlib type-sig search) | Compatibility with Lean v4.29 unverified; would add as a `lake require`. | When proof bodies start landing and "what's the lemma for X" becomes a daily question |
| `lean4-repl` (JSON-over-stdin REPL) | Useful for AI / programmatic exploration. Compatibility iffy across Lean versions. | If we wire an MCP-Lean bridge or LeanDojo-style interactions |
| `doc-gen4` (HTML API docs) | Spec.lean IS the PRD; HTML docs are the natural artifact. | When Phase A part 2 lands (concrete typing judgments → readable docs) |
| `LeanInfer` (local neural premise selection) | Research-grade; needs binary deps. | When closing dozens of compat lemmas in volume; not yet |
| CI (GitHub Actions) | No remote yet; cargo-cult locally. | When the project goes public or another agent contributes |

## Stale-doc check

If something in this doc no longer matches reality (e.g. a make target
was renamed), `tools/check.sh` and `make verify` are the ground truth.
This doc is hand-maintained.
