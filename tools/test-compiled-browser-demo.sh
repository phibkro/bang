#!/usr/bin/env bash
# tool: role=test couples=tools/test-compiled-browser-demo.mjs,web/docs/static/compiled-demos,examples/json,examples/calc,examples/nqueens,examples/ndet-sim-kv-a,examples/ndet-sim-kv-b runs-in=verify
# Enroll the Node/kernel ◊5.75 artifact differential in the standard verify battery driver.
set -euo pipefail

ROOT="$(git rev-parse --show-toplevel)"
source "$ROOT/tools/tool-log.sh" 2>/dev/null && tool_log "$(basename "$0")" || true
cd "$ROOT"
node tools/test-compiled-browser-demo.mjs
