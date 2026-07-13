#!/usr/bin/env bash
# tool: role=wrapper couples=arch-check.py runs-in=manual
set -euo pipefail
exec python3 "$(dirname "$0")/arch-check.py" "$@"
