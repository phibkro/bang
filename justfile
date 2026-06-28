# bang-lang task runner. `just` is more ergonomic than make (no .PHONY,
# parameters via {{...}}, listing recipes via `just --list`).
#
# Common usage:
#   just              # list recipes
#   just verify       # selfcheck + build + audit (default gate)
#   just check FILE   # fast per-file error check
#   just burndown     # per-module sorry/axiom count
#
# Real guarantee for Phase B is `lake env lean Bang/Audit.lean` (#print
# axioms per theorem); audit.sh is the cheap static guard.

# Default: list recipes.
default:
    @just --list --unsorted

# First-time setup (idempotent): install hooks + fetch Mathlib oleans + verify.
setup:
    bash tools/setup.sh

# One-shot orient — position, active path, burndown, recent commits, next steps.
orient:
    bash tools/orient.sh

# Default verify gate — selfcheck + build + audit + ADR-ledger currency.
verify: selfcheck build audit adr-check

# Regenerate the ADR decided-ledger (the index + resolved-questions tables in
# docs/decisions/README.md) from each ADR's frontmatter. Drift = unrepresentable.
adr-index:
    python3 tools/gen-adr-index.py

# Gate the ADR ledger: README generated region is current; every Q marked
# RESOLVED(ADR-n) in OPEN_QUESTIONS ⟺ ADR-n declares `Resolves: Qn`; and each
# ADR's sentinel-frontmatter Status agrees with its prose Status bullet.
adr-check:
    python3 tools/gen-adr-index.py --check

# Build the Lean library. First time: pulls Mathlib oleans (multi-GB).
build:
    # #40: cache-get ONLY when mathlib oleans are absent (fresh setup). In a worktree
    # that already has them, skip it — its "URL changed → re-clone" path deletes
    # .lake/packages/mathlib and (with a shared .git/objects across worktrees) raced
    # an auto-gc into corrupting the store on 2026-06-27. Memory: shared-worktree-git-autogc-corruption.
    [ -e .lake/packages/mathlib/.lake/build ] || lake exe cache get
    lake build

# Static + dynamic audit gate (see tools/audit.sh).
audit:
    bash tools/audit.sh

# ◊5 engine probe (OPEN_QUESTIONS Q9): run a stack-switching suspend/resume
# generator on real Wasmtime — leg #2's oracle foundation. Expects `49`.
wasmfx-probe:
    bash tools/wasmfx-probe.sh

# Architecture fitness functions — CLAUDE.md Invariants #3/#5 (five primitives,
# STM-only) + ADR link integrity + ADR decided-ledger currency (gen-adr-index
# --check: README ≡ frontmatter, Status copies agree, Q⟺ADR) + the
# import-direction V (ADR-0046/0047: Core imports neither edge). Fast, no Lean
# build. Also run by `just audit`. adr-check is HERE (not just in `just verify`)
# so docs-only ADR commits — the normal case — get ledger-gated by the hook too.
fitness:
    bash tools/check-primitives.sh
    bash tools/check-bang-root.sh
    bash tools/check-adr-links.sh
    python3 tools/gen-adr-index.py --check
    bash tools/arch-check.sh
    bash tools/check-audit-sync.sh
    python3 tools/check-refs.py
    python3 tools/refs.py check
    python3 tools/gen-gate-index.py --check

# Import-root coherence: every Bang/**/*.lean is imported in Bang.lean, except the
# co-located `-- root-exclude:` allowlist (regression witnesses). Catches a new file
# silently unbuilt (hence ungated). Also run by `just fitness`.
check-bang-root:
    bash tools/check-bang-root.sh

# Reference library (refs.bib = single source of truth; index.json + the README block are derived).
refs-index:
    python3 tools/refs.py build

# Regenerate the gate-composition block in .claude/codebase-maintenance.md from the justfile recipes.
gate-index:
    python3 tools/gen-gate-index.py

# Faceted retrieval over the library: `just refs capability-safety` (matches key/title/topic/grounds).
refs QUERY:
    @python3 tools/refs.py query "{{QUERY}}"

# Bibliography fitness (also run by `just fitness`): PDF↔key · grounds:ADR↔ADR · Lean cite↔key · sha256.
check-bib:
    python3 tools/refs.py check

# Zero-dep Node sanity check on the row-unifier algorithm.
selfcheck:
    node tools/selfcheck.mjs

# Fast per-file Lean error check (no full library rebuild).
#   just check                        # full build
#   just check Bang/Spec.lean         # just that file
check FILE="":
    bash tools/check.sh {{FILE}}

# Generated Lean symbol index (the navigation gap-fill — tilth/stacklit don't do Lean).
# ON-DEMAND: regenerates fresh in <1s, so it never drifts (a file:line index would churn
# every edit, so it is NOT committed/gated). Optional name filter.
#   just symbols                      # all declarations, sorted by name
#   just symbols HasCTy               # only names containing "HasCTy"
#   just symbols --by-file            # per-module structural outline
symbols PATTERN="":
    python3 tools/symbols.py {{PATTERN}}

# Phase B burndown chart — sorry + axiom count per Bang/*.lean.
burndown:
    bash tools/burndown.sh

# Submit a Lean snippet via stdin; get elaborator output.
#   echo '#check @Bang.Comp.handle' | just eval
eval:
    bash tools/eval.sh

# Install git pre-commit hook (symlink into .git/hooks/). One-time per clone.
install-hooks:
    bash tools/install-hooks.sh

# Run loogle Mathlib type-signature search (via the web service, not a build dep — see lakefile.toml).
#   just loogle "?n + 0 = ?n"     ·     agents: prefer the lean_loogle MCP tool
loogle QUERY:
    @curl -sG "https://loogle.lean-lang.org/json" --data-urlencode "q={{QUERY}}" | jq -r 'if .error then "loogle: \(.error)" else (.hits[]? | "\(.name) : \(.type)") end'

# Remove .lake build artifacts (forces full rebuild next time).
clean:
    -rm -rf .lake

# Run the headline-theorem #print axioms gate (per-theorem axiom report).
axioms:
    lake env lean Bang/Audit.lean
