#!/usr/bin/env bash
# tool: role=test couples=web/docs/role-lab-content.mjs,web/docs/page-manifest.json,web/docs/test-role-lab-coding-agent.mjs runs-in=verify
source "$(git rev-parse --show-toplevel 2>/dev/null)/tools/tool-log.sh" 2>/dev/null && tool_log "$(basename "$0")" || true
# Exact-HEAD coding-agent journey reusing the frontend practice with structured evidence poles.
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"
node web/docs/test-role-lab-coding-agent.mjs
