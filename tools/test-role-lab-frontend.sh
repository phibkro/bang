#!/usr/bin/env bash
# tool: role=test couples=web/docs/role-lab-content.mjs,web/docs/page-manifest.json runs-in=verify
source "$(git rev-parse --show-toplevel 2>/dev/null)/tools/tool-log.sh" 2>/dev/null && tool_log "$(basename "$0")" || true
# Executable agreement between the generated frontend lab and its content-owned practice fixture.
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"
if [ -z "${BANG_BIN_FRESH:-}" ]; then
  echo "building bang runner…" >&2
  lake build bang >&2
fi
node web/docs/test-role-lab-frontend.mjs
