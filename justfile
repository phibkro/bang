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

# Default verify gate — selfcheck + build + audit. `audit` now runs the full
# `just fitness` bundle (#114), which already includes the ADR-ledger `--check`,
# so a separate `adr-check` dep is redundant.
verify: selfcheck build audit

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
    #!/usr/bin/env bash
    set -euo pipefail
    # #40b: NEVER `lake exe cache get` from a LINKED worktree — re-cloning Mathlib in a
    # worktree corrupts the shared .git/objects (2026-06-27/-29). Create IC worktrees via
    # tools/new-worktree.sh (it SEEDS .lake so this branch is never reached). Main checkout
    # with oleans absent → cache-get is the legit first-setup path.
    if [ ! -e .lake/packages/mathlib/.lake/build ]; then
      if [ "$(git rev-parse --git-dir)" != "$(git rev-parse --git-common-dir)" ]; then
        echo "❌ #40b: this linked worktree has no seeded Mathlib oleans."
        echo "   Spawn IC worktrees via tools/new-worktree.sh (seeds .lake), or 'lake exe cache unpack'."
        echo "   Do NOT 'lake exe cache get' here — it corrupts the shared store."
        exit 1
      fi
      lake exe cache get
    fi
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
# import-direction V (ADR-0046/0047: Core imports neither edge). Fast: no Lean
# build on docs/tooling commits — the proof-state leg elaborates Audit.lean ONLY
# when `Bang/` actually moved (sha short-circuit). Also run by `just audit`.
# adr-check is HERE (not just in `just verify`)
# so docs-only ADR commits — the normal case — get ledger-gated by the hook too.
fitness:
    bash tools/check-primitives.sh
    bash tools/check-git-hygiene.sh
    bash tools/check-sha-reachable.sh
    bash tools/check-paths.sh
    bash tools/check-adr-links.sh
    python3 tools/gen-adr-index.py --check
    bash tools/arch-check.sh
    bash tools/check-audit-sync.sh
    bash tools/check-all-modules.sh
    python3 tools/check-refs.py
    python3 tools/refs.py check
    python3 tools/gen-gate-index.py --check
    python3 tools/gen-proof-state.py --check
    python3 tools/gen-import-graph.py --check

# Orientation-doc SHA reachability: every backtick SHA cited as a waypoint in
# CONTEXT.md/ROADMAP.md resolves to a real commit (a rebase/drop makes the prose
# silently false). Foreign hex (other repos, package revs) → tools/sha-allow.txt.
check-sha:
    bash tools/check-sha-reachable.sh

# PATH lifecycle: every active paths/PATH-*.md is reachable from CONTEXT/ROADMAP (done → archive). Also run by fitness.
check-paths:
    bash tools/check-paths.sh

# Reference library (refs.bib = single source of truth; index.json + the README block are derived).
refs-index:
    python3 tools/refs.py build

# Regenerate the gate-composition block in .claude/codebase-maintenance.md from the justfile recipes.
gate-index:
    python3 tools/gen-gate-index.py

# Regenerate the module dependency graph (mermaid + fan-in) in docs/architecture/core-overview.md §2 from the import edges.
import-graph:
    python3 tools/gen-import-graph.py

# Validate the generated module-graph mermaid actually COMPILES (mmdc render). On-demand; the
# build (`just import-graph`) also auto-compiles before writing, so a broken graph never lands.
check-mermaid:
    python3 tools/gen-import-graph.py --validate

# Regenerate CONTEXT.md's proof-state block from the live axiom gate (Bang/Audit.lean
# #print axioms + burndown + git). `--build` forces a fresh olean read (authoritative).
# Tree-aware: reads the proof tree, writes the docs tree's CONTEXT.md.
proof-state:
    python3 tools/gen-proof-state.py --build

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
