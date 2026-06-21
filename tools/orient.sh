#!/usr/bin/env bash
# orient.sh — one-shot orient for fresh sessions.
# Used by `just orient` AND the SessionStart Claude Code hook.
#
# Prints: current checkpoint position, active PATH, burndown summary,
# recent commits, next steps. Tight enough to land cold in <30 seconds.

set -euo pipefail
cd "$(git rev-parse --show-toplevel 2>/dev/null || pwd)"

echo "── bang-lang orient ──"
echo ""

# ── 1. Current position from CONTEXT.md ──────────────────────────────
echo "▸ Position (from CONTEXT.md):"
if [ -f CONTEXT.md ]; then
  awk '/^## Position/{flag=1; next} /^## /{if(flag) exit} flag' CONTEXT.md \
    | grep -v '^```$' | grep -v '^$' | sed 's/^/  /' | head -10
else
  echo "  (no CONTEXT.md)"
fi
echo ""

# ── 2. Active path ────────────────────────────────────────────────────
echo "▸ Active path:"
active_paths=$(ls paths/PATH-*.md 2>/dev/null || true)
if [ -n "$active_paths" ]; then
  for p in $active_paths; do
    echo "  $p:"
    # Pull the Status section
    awk '/^## Status/{flag=1; print; next} /^## /{if(flag) exit} flag' "$p" \
      | head -12 | sed 's/^/    /'
  done
else
  echo "  (none active)"
fi
echo ""

# ── 3. Burndown summary (last 3 lines: TOTAL row + note) ─────────────
echo "▸ Burndown (sorry + axiom counts per module):"
if [ -x tools/burndown.sh ]; then
  bash tools/burndown.sh 2>/dev/null | tail -5 | sed 's/^/  /'
fi
echo ""

# ── 4. Recent commits ────────────────────────────────────────────────
echo "▸ Recent commits:"
git log --oneline -5 2>/dev/null | sed 's/^/  /' || echo "  (no git history)"
echo ""

# ── 5. What to do next ───────────────────────────────────────────────
echo "▸ Next:"
echo "  Read CLAUDE.md (always-loaded core) → CONTEXT.md (current position)"
echo "  Setup check: just verify       Detail:  just burndown"
echo "  First time?  just setup        Help:    just (lists recipes)"
