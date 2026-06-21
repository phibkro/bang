#!/usr/bin/env bash
# eval.sh — submit a Lean snippet, get its elaborator output.
#
# Usage:
#   echo '#check (0 : Nat)' | bash tools/eval.sh
#   echo '#check @Bang.Comp.handle' | bash tools/eval.sh
#   bash tools/eval.sh < snippet.lean
#
# The snippet is prepended with `import Bang; open Bang` so all our types
# (Val, Comp, Handler, VTy, CTy, ...) are in scope. Build cache from
# `lake exe cache get` makes this fast after first run.

set -euo pipefail
cd "$(dirname "$0")/.."

tmp=$(mktemp --suffix=.lean)
trap 'rm -f "$tmp"' EXIT

{
  echo "import Bang"
  echo "open Bang"
  echo ""
  cat -
} > "$tmp"

lake env lean "$tmp" 2>&1
