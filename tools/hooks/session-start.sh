#!/usr/bin/env bash
# tool: role=workflow couples=orient.sh runs-in=hook
source "$(git rev-parse --show-toplevel 2>/dev/null)/tools/tool-log.sh" 2>/dev/null && tool_log "$(basename "$0")" || true
# SessionStart hook — print orient so the agent lands oriented.
# Wired in .claude/settings.json under hooks.SessionStart.
#
# Output flows into the agent's session context. Keep it concise.

set -euo pipefail
cd "${CLAUDE_PROJECT_DIR:-$(git rev-parse --show-toplevel 2>/dev/null)}" || exit 0

# Delegate to the orient script (single source of truth for "current state").
if [ -x tools/orient.sh ]; then
  bash tools/orient.sh 2>/dev/null || true
else
  echo "(tools/orient.sh missing — run `just setup` to bootstrap)"
fi
