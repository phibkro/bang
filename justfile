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

# Default verify gate — selfcheck + build + audit.
verify: selfcheck build audit

# Build the Lean library. First time: pulls Mathlib oleans (multi-GB).
build:
    lake exe cache get && lake build

# Static + dynamic audit gate (see tools/audit.sh).
audit:
    bash tools/audit.sh

# ◊5 engine probe (OPEN_QUESTIONS Q9): run a stack-switching suspend/resume
# generator on real Wasmtime — leg #2's oracle foundation. Expects `49`.
wasmfx-probe:
    bash tools/wasmfx-probe.sh

# Architecture fitness functions — CLAUDE.md Invariants #3/#5 (five primitives,
# STM-only) + ADR index/link integrity. Fast, no Lean build. Also run by `just audit`.
fitness:
    bash tools/check-primitives.sh
    bash tools/check-adr-links.sh

# Zero-dep Node sanity check on the row-unifier algorithm.
selfcheck:
    node tools/selfcheck.mjs

# Fast per-file Lean error check (no full library rebuild).
#   just check                        # full build
#   just check Bang/Spec.lean         # just that file
check FILE="":
    bash tools/check.sh {{FILE}}

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

# Run loogle Mathlib type-signature search.
#   just loogle "?n + 0 = ?n"
loogle QUERY:
    lake exe loogle "{{QUERY}}"

# Remove .lake build artifacts (forces full rebuild next time).
clean:
    -rm -rf .lake

# Run the headline-theorem #print axioms gate (per-theorem axiom report).
axioms:
    lake env lean Bang/Audit.lean
