#!/usr/bin/env bash
# tool: role=test couples=examples/logger-counting,docfacts/examples/logger-counting.json runs-in=verify
source "$(git rev-parse --show-toplevel 2>/dev/null)/tools/tool-log.sh" 2>/dev/null && tool_log "$(basename "$0")" || true
# test-docfacts-logger.sh — executable evidence for the logger-counting docfact.
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"

python3 tools/docfacts_logger.py --check

bang=".lake/build/bin/bang"
if [ -z "${BANG_BIN_FRESH:-}" ]; then
  echo "building bang runner…" >&2
  lake build bang >&2
fi

source_path="examples/logger-counting/main.bang"
expected_path="examples/logger-counting/expected.txt"
workdir="$(mktemp -d --tmpdir bang-docfacts-logger-XXXXXX)"
trap 'rm -rf "$workdir"' EXIT

pass=0
fail=0
engine_count=0
check_count=0

check_file() {
  local name="$1" got="$2" want="$3"
  check_count=$((check_count + 1))
  if cmp -s "$got" "$want"; then
    echo "✓ $name"
    pass=$((pass + 1))
  else
    echo "✗ $name — byte mismatch"
    diff -u "$want" "$got" || true
    fail=$((fail + 1))
  fi
}

run_engine() {
  local name="$1"
  shift
  local out="$workdir/$name.out"
  engine_count=$((engine_count + 1))
  if "$bang" run "$@" "$source_path" >"$out" 2>"$workdir/$name.err"; then
    check_file "$name-vs-expected" "$out" "$expected_path"
  else
    local status=$?
    echo "✗ $name — exited $status"
    cat "$workdir/$name.err"
    check_count=$((check_count + 1))
    fail=$((fail + 1))
  fi
}

run_engine env --engine=env
run_engine oracle --engine=oracle
run_engine compiled --compiled

check_json="$workdir/check.json"
if "$bang" check --json "$source_path" >"$check_json" 2>"$workdir/check.err" \
    && [ "$(jq -r '.ok' "$check_json")" = true ]; then
  echo "✓ check-json-ok"
  pass=$((pass + 1))
else
  echo "✗ check-json-ok"
  cat "$workdir/check.err"
  fail=$((fail + 1))
fi
check_count=$((check_count + 1))

query_json="$workdir/query.json"
if "$bang" query dump "$source_path" >"$query_json" 2>"$workdir/query.err" \
    && [ "$(jq -r '.ok' "$query_json")" = true ] \
    && [ "$(jq '.decls | length' "$query_json")" -gt 0 ]; then
  echo "✓ query-dump-ok-nonempty"
  pass=$((pass + 1))
else
  echo "✗ query-dump-ok-nonempty"
  cat "$workdir/query.err"
  fail=$((fail + 1))
fi
check_count=$((check_count + 1))

expected_engines=3
expected_checks=5
if [ "$engine_count" -ne "$expected_engines" ] || [ "$check_count" -ne "$expected_checks" ]; then
  echo "✗ INTERNAL: ran $engine_count/$expected_engines engines and $check_count/$expected_checks checks" >&2
  exit 1
fi

echo "──────────────────────────────"
echo "docfacts-logger: $pass passed, $fail failed; engines=$engine_count checks=$check_count"
[ "$fail" -eq 0 ]
