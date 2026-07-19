#!/usr/bin/env bash
# tool: role=test couples=web/docs/role-lab-content.mjs,Bang/Backend/AbstractMachine.lean,Bang/Backend/WasmEmit.lean,tools/emit-rung1-diff.sh runs-in=verify
# Public verify battery for the disposable machine/backend role-lab journey.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
node web/docs/test-role-lab-machine-backend.mjs
