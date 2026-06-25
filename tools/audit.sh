#!/usr/bin/env bash
# audit.sh — belt-and-suspenders CI guard. The real guarantee is Audit.lean
# (#print axioms); this just catches the obvious cheats fast and cheaply.
set -euo pipefail

ROOT="${1:-.}"

# Project Lean sources only — exclude the lake build cache (Mathlib etc.).
SCAN_DIRS=("$ROOT/Bang" "$ROOT/Bang.lean")

fail() { echo "FAIL: $1"; exit 1; }

# 1. Sorry / admit. Phase A keeps `sorry` in theorem BODIES intentionally
# (the burndown chart for Phase B). The real gate is `lake env lean Bang/Audit.lean`
# which reports `#print axioms` per headline theorem. For Phase A we LIST the
# remaining sorrys as a status check (don't fail).
echo "── pending sorry/admit (Phase B burndown) ──"
grep -RnE '\b(sorry|admit)\b' --include='*.lean' "${SCAN_DIRS[@]}" 2>/dev/null \
     | grep -v 'Audit.lean' || echo "  (none — Phase B complete?)"
echo "── end pending list ──"

# 2. No hand-rolled axioms (the trusted three are built-in, never declared).
# Phase A is allowed to use `axiom` as Phase B targets (LR, typing, operational).
# Phase B closes by replacing them with concrete defs; this guard re-engages then.
# For Phase A, the check is "no NEW axioms beyond the Spec.lean Phase A stubs."
# Currently: skip this check; rely on Bang/Audit.lean's `#print axioms` to track.
# TODO Phase B: re-enable by listing the allowed Spec.lean axioms.

# 3. No opaque left in the core spec (Phase A must eliminate these).
if grep -RnE '^[[:space:]]*opaque\b' --include='*.lean' "$ROOT/Bang/Spec.lean" 2>/dev/null; then
  fail "opaque stub still present in Bang/Spec.lean — Phase A incomplete"
fi

# 3a. Architecture fitness functions — make CLAUDE.md invariants structural.
#   - check-primitives: kernel constructor set (Val/Comp/Handler) == allowlist
#     (Invariants #3/#5: five primitives, STM-only; a 6th can't slip in silently).
#   - check-adr-links: docs/decisions/ index↔file bijection + link integrity.
#   - arch-check: import-direction V (ADR-0046/0047) — Core imports neither edge;
#     Frontend and Backend meet only at Core. Keeps the layered seam from tangling.
# Fast, deterministic, no Lean build. All gate on real drift (exit 1); ADR
# cross-ref-to-deleted-history is WARN-only (exit 0). Also runnable via `just fitness`.
echo "── architecture fitness (Invariants #3/#5, ADR integrity, import-direction V) ──"
bash "$(dirname "$0")/check-primitives.sh" "$ROOT"
bash "$(dirname "$0")/check-adr-links.sh" "$ROOT"
bash "$(dirname "$0")/arch-check.sh" "$ROOT"
echo "── end fitness ──"

# 4. Build must be clean.
lake build

echo "Static guards passed. Now run:  lake env lean Bang/Audit.lean"
echo "and confirm every axiom set ⊆ { propext, Classical.choice, Quot.sound }."
