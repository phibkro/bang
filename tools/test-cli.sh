#!/usr/bin/env bash
# tool: role=test couples=none runs-in=verify
# test-cli.sh — the non-interactive gate for `bang`'s TOP-LEVEL CLI hygiene (issue #66/#67).
#
# Two concerns, both CLI-surface (not covered by test-repl.sh/test-fmt.sh/test-check-json.sh,
# which each gate one subcommand's own behavior): (1) `--help`/`--version` — a help/version
# REQUEST is a success (issue #66's --help-exits-1 fix), not folded into any one subcommand's
# usage path; (2) every non-zero RUNTIME outcome (oom/escapedCap/stuck/compiled-collapse) gets
# a human-readable stderr message ALONGSIDE its exit code (issue #67) — the exit code stays the
# machine contract, the message is the "the error teaches" half.
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"
bang=".lake/build/bin/bang"

echo "building bang runner…" >&2
lake build bang >&2

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

contains() {
  local name="$1" haystack="$2" needle="$3"
  if [[ "$haystack" == *"$needle"* ]]; then
    echo "✓ $name"; pass=$((pass + 1))
  else
    echo "✗ $name — expected to find [$needle] in [$haystack]"; fail=$((fail + 1))
  fi
}

# ── --help / -h : a help request is a SUCCESS (issue #66), text on STDOUT ──
help_out="$("$bang" --help 2>/dev/null)" && help_exit=0 || help_exit=$?
check "help-long-exit" "$help_exit" "0"
contains "help-long-stdout-usage" "$help_out" "USAGE:"
help_stderr="$("$bang" --help 2>&1 >/dev/null)" || true
check "help-long-stderr-empty" "$help_stderr" ""

got_h_exit=0
"$bang" -h >/dev/null 2>&1 || got_h_exit=$?
check "help-short-exit" "$got_h_exit" "0"

# ── --version / -v : prints a version, exit 0 ──
ver_out="$("$bang" --version 2>/dev/null)" && ver_exit=0 || ver_exit=$?
check "version-long-exit" "$ver_exit" "0"
contains "version-long-stdout-has-bang" "$ver_out" "bang "
got_v_out="$("$bang" -v 2>/dev/null)" && got_v_exit=0 || got_v_exit=$?
check "version-short-exit" "$got_v_exit" "0"
check "version-long-and-short-agree" "$got_v_out" "$ver_out"

# ── RUNTIME MESSAGES (issue #67): each non-zero outcome names the outcome + a next step ──
# oom (exit 2) — a genuinely-diverging `Div` recursion exhausts the fuel ceiling.
oom_tmp="$(mktemp /tmp/bang-cli-test-oom-XXXXXX.bang)"
printf 'let rec loop : Int -> Int ! {Div} = fun n => $loop (n + 1) in $loop 0' > "$oom_tmp"
oom_stderr="$("$bang" run "$oom_tmp" 2>&1 >/dev/null)" && oom_exit=0 || oom_exit=$?
rm -f "$oom_tmp"
check "oom-exit" "$oom_exit" "2"
contains "oom-message-names-outcome" "$oom_stderr" "out of fuel"
contains "oom-message-names-issue" "$oom_stderr" "#61"

# escapedCap (exit 3) — a `{get}` thunk forced after its `state` handler already returned.
esc_stderr="$("$bang" eval --no-typecheck 'let c = (state 0 in {get}) in $c' 2>&1 >/dev/null)" && esc_exit=0 || esc_exit=$?
check "escaped-exit" "$esc_exit" "3"
contains "escaped-message-names-outcome" "$esc_stderr" "escaped its handler"
contains "escaped-message-names-adr" "$esc_stderr" "ADR-0063"

# stuck (exit 4, --no-typecheck only) — forcing a non-thunk value.
stuck_stderr="$("$bang" eval --no-typecheck '$3' 2>&1 >/dev/null)" && stuck_exit=0 || stuck_exit=$?
check "stuck-exit" "$stuck_exit" "4"
contains "stuck-message-names-typecheck-flag" "$stuck_stderr" "--no-typecheck"

# compiled collapse (exit 5) — the SAME escape program, run on the calculated machine, which
# cannot sub-classify WHICH terminal it hit.
compiled_stderr="$("$bang" eval --no-typecheck --compiled 'let c = (state 0 in {get}) in $c' 2>&1 >/dev/null)" && compiled_exit=0 || compiled_exit=$?
check "compiled-collapse-exit" "$compiled_exit" "5"
contains "compiled-collapse-message-says-which" "$compiled_stderr" "does not sub-classify"

echo "──────────────────────────────"
echo "cli: $pass passed, $fail failed"
[ "$fail" -eq 0 ]
