#!/usr/bin/env bash
# eval.sh — submit a Lean snippet, get its elaborator output.
#
# Usage:
#   echo '#check (0 : Nat)' | bash tools/eval.sh
#   echo '#check @Bang.Comp.handle' | bash tools/eval.sh
#   bash tools/eval.sh < snippet.lean
#
# The snippet is prepended with `import Bang.Audit; open Bang` so all our types
# (Val, Comp, Handler, VTy, CTy, ...) are in scope. `Bang.Audit` is the apex
# re-exporter (Spec + Surface + CalcVM → transitively the whole spine); it
# replaced the former `import Bang` barrel when the build closure moved to the
# `Bang.+` lake glob. Build cache makes this fast after the first run.

set -euo pipefail
cd "$(dirname "$0")/.."

tmp=$(mktemp --suffix=.lean)
trap 'rm -f "$tmp"' EXIT

{
  echo "import Bang.Audit"
  echo "open Bang"
  echo ""
  cat -
} > "$tmp"

lake env lean "$tmp" 2>&1
