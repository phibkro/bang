#!/usr/bin/env bash
# tool: role=test couples=web/docs/role-lab-content.mjs,Bang/Audit.lean,tools/audit_facts.py runs-in=verify
source "$(git rev-parse --show-toplevel 2>/dev/null)/tools/tool-log.sh" 2>/dev/null && tool_log "$(basename "$0")" || true
# Dynamic exact-suggestion completion and kernel axiom evidence for the proof role lab.
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"
node web/docs/test-role-lab-kernel-proof.mjs
