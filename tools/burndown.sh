#!/usr/bin/env bash
# burndown.sh — Phase B burndown chart.
# Counts pending `sorry` (theorem-body stubs) and `axiom` (signature stubs)
# per Lean file in Bang/, plus a total.
#
# The real gate is `lake env lean Bang/Audit.lean` (#print axioms per
# theorem). This script gives a fast visual progress check.

set -euo pipefail
cd "$(dirname "$0")/.."

echo "Phase B burndown — pending closures in Bang/"
echo "──────────────────────────────────────────────────────────"
printf "%-40s %6s %6s %6s\n" "FILE" "sorry" "axiom" "total"
echo "──────────────────────────────────────────────────────────"

total_s=0
total_a=0
for f in Bang/*.lean; do
  s=$(grep -cE '\bsorry\b' "$f" 2>/dev/null) || s=0
  a=$(grep -cE '^[[:space:]]*axiom\b' "$f" 2>/dev/null) || a=0
  t=$((s + a))
  total_s=$((total_s + s))
  total_a=$((total_a + a))
  printf "%-40s %6d %6d %6d\n" "$f" "$s" "$a" "$t"
done

echo "──────────────────────────────────────────────────────────"
printf "%-40s %6d %6d %6d\n" "TOTAL" "$total_s" "$total_a" "$((total_s + total_a))"
echo ""
echo "Note: 'sorry' counts include comment mentions; for the precise axiom"
echo "burndown per theorem, run: nix develop --command lake env lean Bang/Audit.lean"
