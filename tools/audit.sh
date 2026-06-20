#!/usr/bin/env bash
# audit.sh — belt-and-suspenders CI guard. The real guarantee is Audit.lean
# (#print axioms); this just catches the obvious cheats fast and cheaply.
set -euo pipefail

ROOT="${1:-.}"

fail() { echo "FAIL: $1"; exit 1; }

# 1. No sorry / admit in proof sources.
if grep -RnE '\b(sorry|admit)\b' --include='*.lean' "$ROOT" \
     | grep -v 'Audit.lean'; then
  fail "sorry/admit present"
fi

# 2. No hand-rolled axioms (the trusted three are built-in, never declared).
if grep -RnE '^[[:space:]]*axiom\b' --include='*.lean' "$ROOT"; then
  fail "new axiom declared"
fi

# 3. No opaque left in the core spec (Phase A must eliminate these).
if grep -RnE '^[[:space:]]*opaque\b' --include='*.lean' "$ROOT/Bang/Spec.lean" 2>/dev/null; then
  fail "opaque stub still present in Bang/Spec.lean — Phase A incomplete"
fi

# 4. Build must be clean.
lake build

echo "Static guards passed. Now run:  lake env lean Bang/Audit.lean"
echo "and confirm every axiom set ⊆ { propext, Classical.choice, Quot.sound }."
