#!/usr/bin/env bash
# tool: role=check couples=Bang/**/*.lean runs-in=manual
source "$(git rev-parse --show-toplevel 2>/dev/null)/tools/tool-log.sh" 2>/dev/null && tool_log "$(basename "$0")" || true
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
set +e
out=$(lake env lean "$FILE" 2>&1)
rc=$?
set -e
# `lake env lean <file>` prints diagnostics as either
#   error: ...            (bare, e.g. from the elaborator front-end), or
#   <file>:<line>:<col>: error: ...   (the common per-declaration form).
# Some Lean versions also print category-tagged forms such as
# `error(lean.unknownIdentifier):`. Match every form for the terse display, but
# use Lean's exit status as the format-independent pass/fail signal.
errs=$(printf '%s\n' "$out" \
  | grep -E '(^|: )(error|warning)(\([^)]*\))?:' \
  | head -40 || true)

if [ "$rc" -eq 0 ] && [ -z "$errs" ]; then
  echo "✓ no errors or warnings"
elif [ -n "$errs" ]; then
  echo "$errs"
else
  # A failing Lean invocation with an unfamiliar diagnostic format must still
  # be visible, never converted into a false green by the display filter.
  # `sed` reads the complete stream; `head` would close early and, under
  # pipefail, could replace Lean's status with printf's SIGPIPE status 141.
  printf '%s\n' "$out" | sed -n '1,40p'
fi

exit "$rc"
