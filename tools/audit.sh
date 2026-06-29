#!/usr/bin/env bash
# audit.sh — belt-and-suspenders CI guard. The real guarantee is Audit.lean
# (#print axioms); this just catches the obvious cheats fast and cheaply.
set -euo pipefail

ROOT="${1:-.}"

# Project Lean sources only — exclude the lake build cache (Mathlib etc.).
# (No root `Bang.lean` barrel: the build closure is the `Bang.+` lake glob.)
SCAN_DIRS=("$ROOT/Bang")

fail() { echo "FAIL: $1"; exit 1; }

# 1. Sorry / admit. Phase A keeps `sorry` in theorem BODIES intentionally
# (the burndown chart for Phase B). The real gate is `lake env lean Bang/Audit.lean`
# which reports `#print axioms` per headline theorem. For Phase A we LIST the
# remaining sorrys as a status check (don't fail).
echo "── pending sorry/admit (Phase B burndown) ──"
grep -RnE '\b(sorry|admit)\b' --include='*.lean' "${SCAN_DIRS[@]}" 2>/dev/null \
     | grep -v 'Audit.lean' || echo "  (none — Phase B complete?)"
echo "── end pending list ──"

# 2. No opaque left in the core spec (Phase A must eliminate these).
if grep -RnE '^[[:space:]]*opaque\b' --include='*.lean' "$ROOT/Bang/Spec.lean" 2>/dev/null; then
  fail "opaque stub still present in Bang/Spec.lean — Phase A incomplete"
fi

# 3. The FULL architecture-fitness bundle (#114). Was a hand-picked 4-of-13 subset
# that silently drifted as new fitness legs landed; now the SSoT — `just fitness`
# is the one list (generated gate-index keeps its prose in sync). No `lake build`
# here: `just verify` runs `build` as its own dep (this is the cheap static guard).
echo "── the full just-fitness bundle (SSoT, #114) ──"
( cd "$ROOT" && just fitness )
echo "── end fitness ──"

echo "Static guards passed. Now run:  lake env lean Bang/Audit.lean"
echo "and confirm every axiom set ⊆ { propext, Classical.choice, Quot.sound }."
