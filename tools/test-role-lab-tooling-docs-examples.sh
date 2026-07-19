#!/usr/bin/env bash
# tool: role=test couples=web/docs/role-lab-content.mjs,examples/logger-counting,docfacts/examples/logger-counting.json,docs/reference/examples/logger-counting.md runs-in=verify
source "$(git rev-parse --show-toplevel 2>/dev/null)/tools/tool-log.sh" 2>/dev/null && tool_log "$(basename "$0")" || true
# Exact-HEAD example-to-fact-to-public-page journey for the tooling/docs/examples role lab.
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"
node web/docs/test-role-lab-tooling-docs-examples.mjs
