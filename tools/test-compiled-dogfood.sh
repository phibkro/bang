#!/usr/bin/env bash
# tool: role=test couples=examples/calc,examples/json,examples/reactive-spreadsheet runs-in=verify
source "$(git rev-parse --show-toplevel 2>/dev/null)/tools/tool-log.sh" 2>/dev/null && tool_log "$(basename "$0")" || true
# test-compiled-dogfood.sh — the --compiled DIFFERENTIAL gate for the dogfood programs (#135).
#
# The calc/json diagnosis (docs/notes/calcjson-compiled-diagnosis.md) proved both DOGFOOD programs
# run on the COMPILED engine (`bang run --compiled` = exec∘compile inside Lean) byte-identical to
# `bang run` (env) and their expected.txt — calc = 11021193, json = 163 — and that the stale
# "compiled hangs" findings dissolved with #95 (knot-sharing). This battery makes that a STANDING
# gate so a future regression in the compiled path (a re-entrant-parser knot slowdown, a lowering
# drift) fails `just verify` instead of silently rotting into another stale finding.
#
# What it asserts, per program:
#   1. `--compiled` stdout == expected.txt  (the run-oracle SoT, same shape as check-examples).
#   2. `--compiled` stdout == `--engine=env` stdout  (the DIFFERENTIAL — the compiled machine and the
#      default env machine must agree on the same program; a divergence is a compiled-path bug).
# Calc and JSON retain the original diagnosis contract (recursive first-class-cap traversal and pure
# multi-module parse). The reactive spreadsheet additionally keeps the first actor-visible reactivity
# tracer honest on the compiled route: named State inputs, thunk recomputation, and early sampling must
# agree with the same oracle.
#
# GOTCHA (set -euo pipefail): an unguarded `$(cmd)` capture dies SILENTLY on a nonzero exit (a
# truncated false-green). Every run below captures standalone with `&& … || …` around the exit, and
# the FINAL line asserts the expected check COUNT — a silently-truncated run is caught by "did we
# reach the count". A `timeout` wraps each run (the compiled re-entrant parser is single-digit
# seconds per the diagnosis; a hang — the regression this gate exists to catch — trips the timeout
# and reads as a MISMATCH, never a hang that wedges the whole `verify`).
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"
bang=".lake/build/bin/bang"

if [ -z "${BANG_BIN_FRESH:-}" ]; then
  echo "building bang runner…" >&2
  lake build bang >&2
fi

# Per-run wall-clock ceiling. The diagnosis measured calc ≈ 8s, json ≈ 2s on the compiled engine;
# 90s is generous headroom that still trips a genuine hang (the #95-class regression) loudly.
TIMEOUT="${COMPILED_DOGFOOD_TIMEOUT:-90}"

# The dogfood programs the diagnosis proved pass --compiled. calc's first-class-cap EFFECT and
# json's pure parse are BOTH covered; hostio-echo is excluded (host-IO needs the driver, not a
# pure compiled run — ADR-0104).
PROGRAMS=(calc json reactive-spreadsheet)

pass=0
fail=0

check() {
  local name="$1" got="$2" want="$3"
  if [ "$got" = "$want" ]; then
    echo "✓ $name"; pass=$((pass + 1))
  else
    echo "✗ $name — expected [$want], got [$got]"; fail=$((fail + 1))
  fi
}

for name in "${PROGRAMS[@]}"; do
  main="examples/$name/main.bang"
  expected_file="examples/$name/expected.txt"
  if [ ! -f "$main" ];         then echo "✗ $name — missing $main"; fail=$((fail + 1)); continue; fi
  if [ ! -f "$expected_file" ]; then echo "✗ $name — missing $expected_file"; fail=$((fail + 1)); continue; fi
  expected="$(cat "$expected_file")"

  # `--compiled` run (guarded: a nonzero exit / timeout yields an empty capture that MISMATCHES, not
  # a silent script death).
  compiled="$(timeout "$TIMEOUT" "$bang" run --compiled "$main" 2>/dev/null)" && : || compiled="__COMPILED_FAILED__"
  # `--engine=env` run — the differential reference (the default engine).
  env_out="$(timeout "$TIMEOUT" "$bang" run --engine=env "$main" 2>/dev/null)" && : || env_out="__ENV_FAILED__"

  check "$name-compiled-vs-expected" "$compiled" "$expected"
  check "$name-compiled-vs-env"      "$compiled" "$env_out"
done

echo "──────────────────────────────"
echo "compiled-dogfood: $pass passed, $fail failed"
# COUNT ASSERTION (false-green defense): each program contributes two checks. A silently-truncated run
# that skipped a check leaves pass+fail below the derived count and fails loud rather than reading green.
expected_checks=$(( ${#PROGRAMS[@]} * 2 ))
if [ "$((pass + fail))" -ne "$expected_checks" ]; then
  echo "✗ INTERNAL: ran $((pass + fail)) checks, expected $expected_checks — a run was silently skipped/truncated" >&2
  exit 1
fi
[ "$fail" -eq 0 ]
