#!/usr/bin/env bash
# tool: role=check couples=Bang/**/*.lean runs-in=manual
source "$(git rev-parse --show-toplevel 2>/dev/null)/tools/tool-log.sh" 2>/dev/null && tool_log "$(basename "$0")" || true
# burndown.sh — Phase B burndown chart.
# Counts pending `sorry` code tokens (theorem-body stubs) and `axiom`
# declarations (signature stubs) per Lean file in Bang/, plus a total. Lean
# comments are stripped by the shared lexer before counting, so prose cannot
# inflate the chart.
#
# The real gate is `just axioms`, which evaluates the `#print axioms` census
# against a fail-closed policy. This script gives a fast visual progress check.

set -euo pipefail
cd "$(dirname "$0")/.."
SCAN_ROOT="${1:-Bang}"

echo "Phase B burndown — pending closures in $SCAN_ROOT/"
echo "──────────────────────────────────────────────────────────"
printf "%-40s %6s %6s %6s\n" "FILE" "sorry" "axiom" "total"
echo "──────────────────────────────────────────────────────────"

total_s=0
total_a=0
while IFS= read -r f; do
  read -r s a < <(python3 - "$f" <<'PY'
import re
import sys

sys.path.insert(0, "tools")
from leanlex import strip_comments

text = strip_comments(open(sys.argv[1], encoding="utf-8").read())

# `strip_comments` is the shared Lean-aware foundation. Mask string contents
# as a second pass so prose in diagnostics/examples is not counted as code.
chars = list(text)
i = 0
while i < len(chars):
    if chars[i] != '"':
        i += 1
        continue
    chars[i] = ' '
    i += 1
    escaped = False
    while i < len(chars):
        ch = chars[i]
        if ch == '\n':
            escaped = False
            i += 1
            continue
        chars[i] = ' '
        if ch == '"' and not escaped:
            i += 1
            break
        if ch == '\\' and not escaped:
            escaped = True
        else:
            escaped = False
        i += 1
text = ''.join(chars)
print(len(re.findall(r"\bsorry\b", text)),
      len(re.findall(r"(?m)^\s*axiom\b", text)))
PY
  )
  t=$((s + a))
  total_s=$((total_s + s))
  total_a=$((total_a + a))
  printf "%-40s %6d %6d %6d\n" "$f" "$s" "$a" "$t"
done < <(find "$SCAN_ROOT" -name '*.lean' | sort)

echo "──────────────────────────────────────────────────────────"
printf "%-40s %6d %6d %6d\n" "TOTAL" "$total_s" "$total_a" "$((total_s + total_a))"
echo ""
echo "Note: source-token counts are a progress chart, not a trust gate."
echo "For the fail-closed headline policy, run: nix develop --command just axioms"
