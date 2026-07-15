#!/usr/bin/env bash
# tool: role=test couples=examples/logger-counting,examples/logger-silent,docfacts/examples/logger-counting.json runs-in=verify
source "$(git rev-parse --show-toplevel 2>/dev/null)/tools/tool-log.sh" 2>/dev/null && tool_log "$(basename "$0")" || true
# test-docfacts-logger.sh — executable evidence for the logger handler-swap docfact.
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"

python3 tools/docfacts_logger.py --check

bang=".lake/build/bin/bang"
if [ -z "${BANG_BIN_FRESH:-}" ]; then
  echo "building bang runner…" >&2
  lake build bang >&2
fi

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
  local variant="$1" engine="$2" source_path="$3" expected_path="$4"
  local out="$workdir/$variant-$engine.out"
  local err="$workdir/$variant-$engine.err"
  engine_count=$((engine_count + 1))
  if "$bang" run "--engine=$engine" "$source_path" >"$out" 2>"$err"; then
    if [ -s "$err" ]; then
      echo "✗ $variant-$engine — unexpected stderr"
      cat "$err"
      check_count=$((check_count + 1))
      fail=$((fail + 1))
    else
      check_file "$variant-$engine-vs-expected" "$out" "$expected_path"
    fi
  else
    local status=$?
    echo "✗ $variant-$engine — exited $status"
    cat "$err"
    check_count=$((check_count + 1))
    fail=$((fail + 1))
  fi
}

check_services() {
  local variant="$1" source_path="$2"
  local check_json="$workdir/$variant-check.json"
  if "$bang" check --json "$source_path" >"$check_json" 2>"$workdir/$variant-check.err" \
      && [ ! -s "$workdir/$variant-check.err" ] \
      && [ "$(jq -r '.ok' "$check_json")" = true ]; then
    echo "✓ $variant-check-json-ok"
    pass=$((pass + 1))
  else
    echo "✗ $variant-check-json-ok"
    cat "$workdir/$variant-check.err"
    fail=$((fail + 1))
  fi
  check_count=$((check_count + 1))

  local query_json="$workdir/$variant-query.json"
  if "$bang" query dump "$source_path" >"$query_json" 2>"$workdir/$variant-query.err" \
      && [ ! -s "$workdir/$variant-query.err" ] \
      && [ "$(jq -r '.ok' "$query_json")" = true ] \
      && [ "$(jq '[.decls[] | select(.name == "Log" and .kind == "effect" and any(.shape.ops[]; .name == "log" and .type == "Int -> Int"))] | length' "$query_json")" -eq 1 ]; then
    echo "✓ $variant-query-dump-log-op"
    pass=$((pass + 1))
  else
    echo "✗ $variant-query-dump-log-op"
    cat "$workdir/$variant-query.err"
    fail=$((fail + 1))
  fi
  check_count=$((check_count + 1))
}

for variant in logger-counting logger-silent; do
  source_path="examples/$variant/main.bang"
  expected_path="examples/$variant/expected.txt"
  for engine in env oracle compiled; do
    run_engine "$variant" "$engine" "$source_path" "$expected_path"
  done
  check_services "$variant" "$source_path"
done

if [ "$(python3 - <<'PY'
from pathlib import Path
counting = Path('examples/logger-counting/main.bang').read_text()
silent = Path('examples/logger-silent/main.bang').read_text()
print('yes' if counting.count('log(msg) => 1') == 1 and counting.replace('log(msg) => 1', 'log(msg) => 0') == silent else 'no')
PY
)" = yes ]; then
  echo "✓ logger-handler-clause-only-swap"
  pass=$((pass + 1))
else
  echo "✗ logger-handler-clause-only-swap"
  fail=$((fail + 1))
fi
check_count=$((check_count + 1))

expected_engines=6
expected_checks=11
if [ "$engine_count" -ne "$expected_engines" ] || [ "$check_count" -ne "$expected_checks" ]; then
  echo "✗ INTERNAL: ran $engine_count/$expected_engines engines and $check_count/$expected_checks checks" >&2
  exit 1
fi

echo "──────────────────────────────"
echo "docfacts-logger: $pass passed, $fail failed; engines=$engine_count checks=$check_count"
[ "$fail" -eq 0 ]
