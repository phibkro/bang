#!/usr/bin/env bash
# tool: role=test couples=tools/check-examples.sh,tools/check-examples-env.sh runs-in=verify
# Falsification gate for issue #173: matching stdout must not hide runner failure.
set -euo pipefail

# The test invokes itself through this symlink as a controlled bang runner. It emits
# the exact oracle output for every example, then simulates a late runner failure.
if [ "$(basename "$0")" = "fake-bang" ]; then
  main=""
  for arg in "$@"; do
    case "$arg" in
      */main.bang) main="$arg" ;;
    esac
  done
  if [ -z "$main" ]; then
    echo "fake-bang: no main.bang argument" >&2
    exit 74
  fi
  cat "$(dirname "$main")/expected.txt"
  exit 73
fi

source "$(git rev-parse --show-toplevel 2>/dev/null)/tools/tool-log.sh" 2>/dev/null && tool_log "$(basename "$0")" || true
cd "$(git rev-parse --show-toplevel)"

example_count=0
for dir in examples/*/; do
  [ -f "$dir/main.bang" ] && example_count=$((example_count + 1))
done
if [ "$example_count" -eq 0 ]; then
  echo "test-example-exit-status: no examples discovered" >&2
  exit 1
fi

workdir="$(mktemp -d --tmpdir bang-example-exit-status-XXXXXX)"
trap 'rm -rf "$workdir"' EXIT
fake_bang="$workdir/fake-bang"
ln -s "$PWD/tools/test-example-exit-status.sh" "$fake_bang"

checks=0
failures=0
check_gate() {
  local gate="$1"
  local summary="$2"
  local output status diagnostic_count

  if output="$(BANG_BIN="$fake_bang" BANG_BIN_FRESH=1 bash "$gate" 2>&1)"; then
    status=0
  else
    status=$?
  fi

  if [ "$status" -eq 0 ]; then
    echo "✗ $gate accepted matching stdout from a runner that exited 73" >&2
    failures=$((failures + 1))
  elif ! grep -Fqx "$summary" <<<"$output"; then
    echo "✗ $gate did not report the complete falsification count" >&2
    echo "  expected summary: $summary" >&2
    echo "  actual output:" >&2
    printf '%s\n' "$output" >&2
    failures=$((failures + 1))
  else
    diagnostic_count="$(grep -c '^✗ .*status \[73\]$' <<<"$output" || true)"
    if [ "$diagnostic_count" -ne "$example_count" ]; then
      echo "✗ $gate reported $diagnostic_count exit-status diagnostics for $example_count examples" >&2
      failures=$((failures + 1))
    else
      echo "✓ $gate rejected $example_count/$example_count matching-output runs with status 73"
    fi
  fi
  checks=$((checks + 1))
}

check_gate "${ORACLE_GATE:-tools/check-examples.sh}" \
  "examples: 0 passed, $example_count failed"
check_gate "${ENV_GATE:-tools/check-examples-env.sh}" \
  "examples (--engine=env): 0 passed, $example_count failed"

echo "──────────────────────────────"
echo "example exit-status gates: $((checks - failures))/$checks passed"
[ "$checks" -eq 2 ] && [ "$failures" -eq 0 ]
