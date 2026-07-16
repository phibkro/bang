#!/usr/bin/env bash
# tool: role=test couples=tools/test-query.sh,tools/test-fmt.sh runs-in=verify
# Falsifier for success-path stdout captures: a proxy emits the real expected bytes, then mutates
# only the producer exit status. The real gates must accept the exit-0 control and reject exit 23.
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"
real_bang="$PWD/.lake/build/bin/bang"

if [ -z "${BANG_BIN_FRESH:-}" ]; then
  echo "building bang runner…" >&2
  lake build bang >&2
fi

tmpdir="$(mktemp -d)"
trap 'rm -rf "$tmpdir"' EXIT
proxy="$tmpdir/bang-status-proxy"

cat > "$proxy" <<'PROXY'
#!/usr/bin/env bash
set -euo pipefail

target=0
case "${FAKE_MODE:?}" in
  query) [ "$#" -eq 2 ] && [ "$1" = query ] && [ "$2" = dump ] && target=1 ;;
  fmt)   [ "$#" -eq 1 ] && [ "$1" = fmt ] && target=1 ;;
  *) echo "unknown FAKE_MODE: $FAKE_MODE" >&2; exit 97 ;;
esac

if [ "$target" -eq 0 ]; then
  exec "${REAL_BANG:?}" "$@"
fi

if output="$("$REAL_BANG" "$@")"; then
  real_status=0
else
  real_status=$?
fi
printf '%s\n' "$output"
[ "$real_status" -eq 0 ] || exit "$real_status"
exit "${FAKE_EXIT:?}"
PROXY
chmod +x "$proxy"

checks=0
fail=0

run_control() {
  local mode="$1" gate="$2"
  local output status
  if output="$(REAL_BANG="$real_bang" FAKE_MODE="$mode" FAKE_EXIT=0 \
      BANG_BIN="$proxy" BANG_BIN_FRESH=1 bash "$gate" 2>&1)"; then
    status=0
  else
    status=$?
  fi
  checks=$((checks + 1))
  if [ "$status" -eq 0 ]; then
    echo "✓ $mode-exit-zero-control"
  else
    echo "✗ $mode-exit-zero-control — proxy changed stdout behavior: $output"
    fail=$((fail + 1))
  fi
}

run_mutant() {
  local mode="$1" gate="$2" marker="$3"
  local output status
  if output="$(REAL_BANG="$real_bang" FAKE_MODE="$mode" FAKE_EXIT=23 \
      BANG_BIN="$proxy" BANG_BIN_FRESH=1 bash "$gate" 2>&1)"; then
    status=0
  else
    status=$?
  fi
  checks=$((checks + 1))
  if [ "$status" -ne 0 ] && [[ "$output" == *"$marker"* ]] && [[ "$output" == *"got [23]"* ]]; then
    echo "✓ $mode-nonzero-producer-rejected"
  else
    echo "✗ $mode-nonzero-producer-rejected — expected a status assertion failure, gate=$status: $output"
    fail=$((fail + 1))
  fi
}

# The exit-0 controls mutation-test the falsifier: the proxy path itself preserves exact stdout.
# The paired exit-23 runs change only status and must make the production gates fail closed.
run_control query tools/test-query.sh
run_mutant query tools/test-query.sh dump-stdin-exit
run_control fmt tools/test-fmt.sh
run_mutant fmt tools/test-fmt.sh file-and-stdin-exit

[ "$checks" -eq 4 ] || { echo "✗ expected 4 checks, ran $checks"; exit 1; }
[ "$fail" -eq 0 ]
