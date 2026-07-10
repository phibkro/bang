#!/usr/bin/env bash
# tool: role=test couples=examples/*/main.bang,examples/*/expected.txt runs-in=verify
# check-examples-env.sh — the DIFFERENTIAL gate for the EXPERIMENTAL env engine (ADR-0094).
#
# Same corpus as check-examples.sh, but run through `bang run … --engine=env` (the environment
# machine evalE/readback) and diffed against the SAME expected.txt (which is the oracle's output).
# A byte-identical pass across the whole corpus is the empirical companion to the machine-checked
# correspondence `evalE_agrees_evalD`: the proven ≡ holds on every real program we ship. A mismatch
# FAILS — either a bug in the experimental engine or a genuine oracle/env divergence to surface.
#
# Sibling of check-examples.sh (not folded in) so the experimental engine's gate is opt-in and
# clearly separate from the default-engine run oracle. Retired/merged when env becomes non-experimental.
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"
bang=".lake/build/bin/bang"

# Honor run-batteries.sh's single up-front build (BANG_BIN_FRESH) like the other
# batteries; standalone (`just check-examples-env`) still (re)builds — incremental.
if [ -z "${BANG_BIN_FRESH:-}" ]; then
  echo "building bang runner…" >&2
  lake build bang >&2
fi

pass=0
fail=0
for dir in examples/*/; do
  main="$dir/main.bang"
  expected="$dir/expected.txt"
  name="$(basename "$dir")"
  [ -f "$main" ] || continue
  if [ ! -f "$expected" ]; then
    echo "✗ $name — no expected.txt"; fail=$((fail + 1)); continue
  fi
  got="$("$bang" run "$main" --engine=env 2>/dev/null)" || true
  want="$(cat "$expected")"
  if [ "$got" = "$want" ]; then
    echo "✓ $name → $got"; pass=$((pass + 1))
  else
    echo "✗ $name — expected [$want], got [$got]"; fail=$((fail + 1))
  fi
done

echo "──────────────────────────────"
echo "examples (--engine=env): $pass passed, $fail failed"
[ "$fail" -eq 0 ]
