#!/usr/bin/env bash
# check.sh — fast per-file Lean error check.
# Usage:
#   bash tools/check.sh                    # full lake build (incremental)
#   bash tools/check.sh Bang/Spec.lean     # check just one file, terse output
#
# This is the fastest feedback loop while iterating on a single file.
# `lake env lean <file>` builds dependencies of that file (incremental,
# cached) and reports errors / warnings only for that file.

set -euo pipefail
cd "$(dirname "$0")/.."

FILE="${1:-}"

if [ -z "$FILE" ]; then
  echo "→ full lake build"
  lake build 2>&1 | tail -40
  exit ${PIPESTATUS[0]}
fi

if [ ! -f "$FILE" ]; then
  echo "no such file: $FILE" >&2
  exit 1
fi

echo "→ checking $FILE"
out=$(lake env lean "$FILE" 2>&1 || true)
# `lake env lean <file>` prints diagnostics as either
#   error: ...            (bare, e.g. from the elaborator front-end), or
#   <file>:<line>:<col>: error: ...   (the common per-declaration form).
# The previous `^(error|warning):` anchor only matched the FIRST form, so any
# file whose only errors were path-prefixed reported a FALSE green. Match both.
errs=$(echo "$out" | grep -E '(^|: )(error|warning):' | head -40 || true)

if [ -z "$errs" ]; then
  echo "✓ no errors or warnings"
else
  echo "$errs"
fi
