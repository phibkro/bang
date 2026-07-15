#!/usr/bin/env bash
# tool: role=test couples=onboarding_journey.py runs-in=verify
# Public verify battery for the common contributor journey.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
exec python3 tools/onboarding_journey.py "$@"
