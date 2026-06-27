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

# Regenerate the counterexample-registry index (docs/notes/counterexamples.md) from the
# Bang/Counterexamples.lean manifest + each witness's doc-comment header. Drift = unrepresentable.
counterexamples:
    python3 tools/gen-cex-index.py

# Gate the cex index: the generated region ≡ committed (pure-text, fast; in `just fitness`).
# The live axiom gate is `just cex-axioms`; the build of the manifest re-verifies sorry-freeness.
cex-check:
    python3 tools/gen-cex-index.py --check

# Counterexample-registry axiom report — `#print axioms` per headline witness theorem.
# PASS ⟺ every set ⊆ { propext, Classical.choice, Quot.sound }. Mirrors `just axioms`/Audit.lean.
cex-axioms:
    lake env lean Bang/Counterexamples.lean

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
# STM-only) + ADR index/link integrity + the import-direction V (ADR-0046/0047:
# Core imports neither edge). Fast, no Lean build. Also run by `just audit`.
fitness:
    bash tools/check-primitives.sh
    bash tools/check-adr-links.sh
    bash tools/arch-check.sh
    bash tools/check-audit-sync.sh
    python3 tools/check-refs.py
    python3 tools/gen-cex-index.py --check

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
