#!/usr/bin/env bash
# tool: role=test couples=examples/*/main.bang runs-in=verify
# test-annotate.sh — the non-interactive gate for `bang rewrite annotate` (#82 item 1).
#
# Mirrors test-rewrite.sh's shape (build once, exercise the binary, diff, tally pass/fail). The
# pure per-decl outcome logic (`buildAscription`/`rowHasOnlyBuiltins`/`roundTripsClean`) is already
# gated at the Lean `#guard` level (Bang/Frontend/Annotate.lean, including the `{e4}` user-label
# case #guard-level — task #40's hard constraint) — this file gates the CLI SURFACE: the
# diff-default/-w contract (`annotate` registers in the SAME rewrite architecture `fmt`/`rename`
# use), the already-annotated no-op case, and the "effect creep becomes diff-visible" story (a
# NON-EMPTY builtin row — `Div`, via ordinary recursion — shows up as a diff-visible ascription
# for a fresh caller).
#
# GOTCHA (set -euo pipefail, per test-rewrite.sh's own documented lesson): an unguarded
# `$(cmd1 | cmd2)` capture can kill this script SILENTLY mid-run. Every capture below either runs
# standalone (no pipe) with an explicit `&& … || …` exit-capture, or pipes into `grep` with
# `|| true` on the capture. The FINAL line asserts the expected check COUNT.
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

tmpdir="$(mktemp -d)"
trap 'rm -rf "$tmpdir"' EXIT

# ── fixtures ──

# a `letD` lacking an ascription (`triple`, a plain Int VALUE), a `letRecD` already carrying one
# (mandatory, no-op), and a trailing use so the file type-checks.
cat > "$tmpdir/plain.bang" <<'BANG'
let rec double : Int -> Int = fun n => n + n
let triple = $double 1 + 1
let main = triple
BANG

# a `letD` referencing a `Div`-declared recursive function — its row is NOT `{}` (Div propagates
# to every call site until discharged), so annotate produces a genuinely NON-EMPTY row ascription
# end to end. This is the diff-visible "effect creep" story made concrete: a caller of a Div-typed
# function gets `Int ! {Div}` the moment its own ascription is added or re-derived.
cat > "$tmpdir/divrow.bang" <<'BANG'
let rec fact : Int -> Int ! {Div} = fun n => if n < 2 then 1 else n * ($fact (n - 1))
let result = $fact 5
let main = result
BANG

# ══ 1. `bang rewrite annotate` — the happy path: infers + splices a missing ascription ══

before_md5="$(md5sum "$tmpdir/plain.bang" | cut -d' ' -f1)"
got_diff="$("$bang" rewrite annotate "$tmpdir/plain.bang" 2>/dev/null)" && got_diff_exit=0 || got_diff_exit=$?
after_md5="$(md5sum "$tmpdir/plain.bang" | cut -d' ' -f1)"
check "annotate-happy-exit" "$got_diff_exit" "0"
check "annotate-happy-file-untouched-without-w" "$after_md5" "$before_md5"
check "annotate-happy-diff-adds-triple-ascription" "$(printf '%s' "$got_diff" | grep -c '+let triple : Int' || true)" "1"

# the stderr SUMMARY names `triple` as annotated and `double` as already-annotated (`main` is
# ALSO a plain `letD` lacking an ascription, so it's annotated too, not already-annotated).
got_summary="$("$bang" rewrite annotate "$tmpdir/plain.bang" 2>&1 >/dev/null)" && got_summary_exit=0 || got_summary_exit=$?
check "annotate-happy-summary-exit" "$got_summary_exit" "0"
check "annotate-summary-mentions-triple" "$(printf '%s' "$got_summary" | grep -c '+ triple' || true)" "1"
check "annotate-summary-mentions-double-already" "$(printf '%s' "$got_summary" | grep -c 'double — already annotated' || true)" "1"

# -w actually applies the ascriptions, and the file still runs to the SAME value (annotate cannot
# change behavior — see Bang/Frontend/Annotate.lean's own module header).
got_run_before="$("$bang" run "$tmpdir/plain.bang" 2>/dev/null)" && got_run_before_exit=0 || got_run_before_exit=$?
"$bang" rewrite annotate "$tmpdir/plain.bang" -w >/dev/null 2>&1
got_run_after="$("$bang" run "$tmpdir/plain.bang" 2>/dev/null)" && got_run_after_exit=0 || got_run_after_exit=$?
check "annotate-w-preserves-value" "$got_run_after" "$got_run_before"
check "annotate-w-preserves-exit" "$got_run_after_exit" "$got_run_before_exit"
check "annotate-w-triple-now-ascribed" "$(grep -c 'let triple : Int' "$tmpdir/plain.bang" || true)" "1"

# ══ 2. re-running on an ALREADY-annotated file: every decl reports already-annotated, no diff ══

got_nochange="$("$bang" rewrite annotate "$tmpdir/plain.bang" 2>/dev/null)" && got_nochange_exit=0 || got_nochange_exit=$?
check "annotate-rerun-nochange" "$got_nochange" "(no changes)"
check "annotate-rerun-nochange-exit" "$got_nochange_exit" "0"

# ══ 3. EFFECT CREEP BECOMES DIFF-VISIBLE (#82's headline story) — a genuinely non-empty row ══

got_div_diff="$("$bang" rewrite annotate "$tmpdir/divrow.bang" 2>/dev/null)" && got_div_diff_exit=0 || got_div_diff_exit=$?
check "annotate-div-row-exit" "$got_div_diff_exit" "0"
check "annotate-div-row-visible-on-result" "$(printf '%s' "$got_div_diff" | grep -c '+let result : Int ! {Div}' || true)" "1"
check "annotate-div-row-visible-on-main" "$(printf '%s' "$got_div_diff" | grep -c '+let main : Int ! {Div}' || true)" "1"

# -w applies it, and the recursive call still evaluates to the SAME value (120 = 5!).
"$bang" rewrite annotate "$tmpdir/divrow.bang" -w >/dev/null 2>&1
got_div_run="$("$bang" run "$tmpdir/divrow.bang" 2>/dev/null)" && got_div_run_exit=0 || got_div_run_exit=$?
check "annotate-div-row-w-preserves-value" "$got_div_run" "120"
check "annotate-div-row-w-preserves-exit" "$got_div_run_exit" "0"
check "annotate-div-row-w-visible-in-file" "$(grep -c 'let result : Int ! {Div}' "$tmpdir/divrow.bang" || true)" "1"

# ══ 4. Usage / exit-code hygiene ══

got_unreadable_exit=0
"$bang" rewrite annotate /no/such/file.bang >/dev/null 2>&1 || got_unreadable_exit=$?
check "annotate-unreadable-file-exit" "$got_unreadable_exit" "2"

# stdin route works (no file: reads stdin, `-w` is meaningless without a path — see next check).
got_stdin="$(cat "$tmpdir/plain.bang" | "$bang" rewrite annotate 2>/dev/null)" && got_stdin_exit=0 || got_stdin_exit=$?
check "annotate-stdin-exit" "$got_stdin_exit" "0"
check "annotate-stdin-nochange" "$got_stdin" "(no changes)"

got_w_no_file_exit=0
printf 'let x = 3\n' | "$bang" rewrite annotate -w >/dev/null 2>&1 || got_w_no_file_exit=$?
check "annotate-w-requires-file-exit" "$got_w_no_file_exit" "1"

echo "──────────────────────────────"
echo "annotate: $pass passed, $fail failed"
# Assert the expected total COUNT — catches a silently-truncated run (test-query.sh's own
# discipline, restated in test-rewrite.sh, restated here).
want_total=21
got_total=$((pass + fail))
if [ "$got_total" -ne "$want_total" ]; then
  echo "✗ check-count-mismatch — expected $want_total checks to run, only $got_total did (script truncated?)"
  exit 1
fi
[ "$fail" -eq 0 ]
