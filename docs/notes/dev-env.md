# Dev environment

> How to set up + use the bang-lang dev tooling. Most things "just work"
> after `nix develop`; this doc lists the levers and what each does.

## Why Nix manages elan, NOT Lean itself

Mathlib's olean cache is keyed to the official Lean toolchain build (hash).
If Nix builds Lean itself, the hash diverges and the cache misses — every
build then recompiles Mathlib from source (multi-GB, hours).

Our `flake.nix` deliberately ships **`pkgs.elan` only**, not `pkgs.lean`.
Elan reads `lean-toolchain` and fetches the official Lean release. Mathlib's
Azure-hosted cache stays live; `lake exe cache get` populates oleans in
seconds.

For hermetic reproducibility (e.g. CI), the second path is `lean4-nix` —
slow Mathlib rebuild is fine there because CI doesn't iterate. Keep it out
of the daily dev shell.

## First-time setup

```bash
cd /srv/share/projects/lang-bang
nix develop          # opens Lean 4 dev shell (or auto-entered via direnv)
lake exe cache get   # one-time: pull Mathlib oleans from Azure (multi-GB)
just verify          # selfcheck + lake build + tools/audit.sh
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
| `just verify` | Default. selfcheck + build + audit. |
| `just build` | `lake exe cache get && lake build` (incremental after first run). |
| `just audit` | `tools/audit.sh` — static guards + axiom-set report per theorem. |
| `just selfcheck` | Zero-dep Node smoke test of the row-unifier algorithm. |
| `just clean` | Remove `.lake/` build artifacts. |

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

just audit                              # full gate before committing
bash tools/burndown.sh                  # see remaining sorrys/axioms

git add -A && git commit -m "..."       # pre-commit hook runs static guards
```

`tools/check.sh Bang/Spec.lean` is faster than `just build` because it
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

## Loogle — Mathlib type-signature search

```bash
nix develop --command lake exe loogle "?n + 0 = ?n"
nix develop --command lake exe loogle "Finset _ → Finset _ → Finset _"
```

Returns Mathlib lemmas matching the shape. First invocation builds loogle
(~30s); subsequent runs are instant. Added as a `[[require]]` in
`lakefile.toml`.

> **GOTCHA — loogle's moving `master` ref flakes `lake exe cache get` in a FRESH
> worktree (caught 2026-06-23).** `loogle` is required with no SHA pin (→ `master`).
> In a clean checkout / new `git worktree`, `lake exe cache get` re-resolves it:
> "URL has changed; deleting and cloning again" → `fatal: unable to read tree <sha>`
> → exit 128. `lake build` ALONE is green (loogle already present); only `cache
> get`'s re-clone of the moving ref breaks — which means the pre-commit hook's
> `just verify` (= `cache get && lake build`) fails in a fresh worktree even when
> the code is green. This bit a worktree-isolated agent and trapped ~600 lines of
> hand-verified-green proof UNCOMMITTED (then lost on worktree cleanup).
> **Mitigations:** (1) when the flake is purely `cache get` and you've verified the
> real gate by hand (`lake build` + `lake env lean Bang/Audit.lean`), commit with
> `BANGLANG_SKIP_VERIFY_REASON="loogle cache-get flake; build+axioms hand-verified
> green"` rather than leaving work uncommitted. (2) **Real fix (deferred):** pin
> `loogle` to a SHA (not `master`) in `lakefile.toml`, or pre-seed
> `.lake/packages/loogle`, so fresh worktrees stop hitting it.

## tools/eval.sh — submit Lean snippet, get elaborator output

```bash
echo '#check @Bang.Comp.handle' | bash tools/eval.sh
echo '#print Bang.HasCTy' | bash tools/eval.sh
```

Snippet runs with `import Bang; open Bang` prepended. Useful for
exploration without editing a file. AI agents / scripts can shell out
here for programmatic Lean access without an MCP bridge.

## Tools to consider adding (deferred)

| Tool | Why deferred | When to add |
|---|---|---|
| `lean4-repl` (JSON-over-stdin REPL) | Useful for AI / programmatic exploration. Compatibility iffy across Lean versions. | If we wire an MCP-Lean bridge or LeanDojo-style interactions |
| `doc-gen4` (HTML API docs) | Spec.lean IS the PRD; HTML docs are the natural artifact. | When Phase A part 2 lands (concrete typing judgments → readable docs) |
| `iris-lean` (▷ later modality, MoSeL) | Buys guarded recursion for the LR without rolling our own well-founded recursion. | When the LR mutual defs (Vrel/Srel/Krel/Crel) need concrete bodies — Phase B PROOF_ORDER #1 |
| `grind` (Lean's SMT-style closer, ≥4.28) | Now in our toolchain; just use it. Probably the most impactful tactic for our typing-derivation case work. See `docs/notes/tactics-survey.md`. | Already available — reach for it on goal leaves |
| `aesop` custom rule sets | Tag typing-rule constructors with `@[aesop safe constructors]`; case analysis becomes near-automatic. | When typing rules are concretized in Phase A part 2 |
| `CSLib` (Lean 4 PL library) | Reusable LTS / bisimulation infrastructure. | If our LR proofs find themselves re-implementing standard bisimulation lemmas |
| `LeanInfer` (local neural premise selection) | Research-grade; needs binary deps. | When closing dozens of compat lemmas in volume; not yet |
| CI (GitHub Actions) | No remote yet; cargo-cult locally. | When the project goes public or another agent contributes |

## Stale-doc check

If something in this doc no longer matches reality (e.g. a make target
was renamed), `tools/check.sh` and `just verify` are the ground truth.
This doc is hand-maintained.
