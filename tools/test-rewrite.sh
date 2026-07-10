#!/usr/bin/env bash
# tool: role=test couples=examples/*/main.bang runs-in=verify
source "$(git rev-parse --show-toplevel 2>/dev/null)/tools/tool-log.sh" 2>/dev/null && tool_log "$(basename "$0")" || true
# test-rewrite.sh — the non-interactive gate for `bang rewrite <verb>` (issue #81, the CQS command
# side over #80's query/read-model side).
#
# Mirrors test-query.sh's shape (build once, exercise the binary, diff, tally pass/fail). The pure
# AST-walk internals (`renameVars`/`renameDeclBody`/`rename`'s three loud failures) are already
# gated at the Lean `#guard` level (Bang/Frontend/Rewrite.lean) — this file gates the CLI SURFACE:
# fmt-as-rewrite-#0 parity with `bang fmt`, the rename happy path + its three diagnostics, the
# diff-vs--w output contract (default touches NOTHING on disk; -w applies), and — the moat feature
# — the differential PRESERVATION GATE, falsified by a case that genuinely diverges (a rename that
# collides with a LOCAL binding invisible to `rename`'s own top-level collision check) and shown
# to abort cleanly (no partial write) before being "restored" (the ORIGINAL file, never touched,
# is simply re-verified byte-identical — there is nothing to undo, which is itself the point).
#
# GOTCHA (set -euo pipefail, per test-query.sh's own documented lesson): an unguarded
# `$(cmd1 | cmd2)` capture can kill this script SILENTLY mid-run. Every capture below either runs
# standalone (no pipe) with an explicit `&& … || …` exit-capture, or pipes into `grep` with
# `|| true` on the capture. The FINAL line asserts the expected check COUNT.
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"
bang=".lake/build/bin/bang"

if [ -z "${BANG_BIN_FRESH:-}" ]; then
  echo "building bang runner…" >&2
  lake build bang >&2
fi

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
cat > "$tmpdir/simple.bang" <<'BANG'
let rec double : Int -> Int = fun n => n + n
let quad = {fun n => $double ($double n)}
let main = $quad 3
BANG

# a fixture whose rename target collides with a LOCAL (non-top-level) binding — `rename`'s own
# top-level collision check cannot see this (`x` is not a top-level decl), so it is exactly the
# preservation gate's job to catch it. `helper` renamed to `x` shadows/captures at `main`'s own
# `let x = 5 in $helper 1` call site.
cat > "$tmpdir/capture.bang" <<'BANG'
let helper = {fun x => x + 100}
let main = let x = 5 in $helper 1
BANG

# ══ 1. `bang rewrite fmt` — rewrite #0, parity with `bang fmt` ══

# fmt-as-rewrite parity: the REWRITTEN program (parsed then re-printed) equals `bang fmt`'s own
# output — one construct, not two independent printers.
got_fmt_direct="$("$bang" fmt "$tmpdir/simple.bang" 2>/dev/null)" && got_fmt_direct_exit=0 || got_fmt_direct_exit=$?
check "fmt-direct-exit" "$got_fmt_direct_exit" "0"

"$bang" rewrite fmt "$tmpdir/simple.bang" -w >/dev/null 2>&1
got_rewrite_fmt="$(cat "$tmpdir/simple.bang")"
check "rewrite-fmt-w-equals-fmt-direct" "$got_rewrite_fmt" "$got_fmt_direct"

# already-canonical input: `rewrite fmt` (no -w) reports "(no changes)", diff mode — file untouched.
before_md5="$(md5sum "$tmpdir/simple.bang" | cut -d' ' -f1)"
got_nochange="$("$bang" rewrite fmt "$tmpdir/simple.bang" 2>/dev/null)" && got_nochange_exit=0 || got_nochange_exit=$?
after_md5="$(md5sum "$tmpdir/simple.bang" | cut -d' ' -f1)"
check "rewrite-fmt-nochange-message" "$got_nochange" "(no changes)"
check "rewrite-fmt-nochange-exit" "$got_nochange_exit" "0"
check "rewrite-fmt-nochange-file-untouched" "$after_md5" "$before_md5"

# non-canonical input: `rewrite fmt` (no -w) shows a diff, touches NOTHING on disk.
cat > "$tmpdir/messy.bang" <<'BANG'
let   rec   double : Int -> Int = fun n => n+n
let main = $double 5
BANG
before_messy_md5="$(md5sum "$tmpdir/messy.bang" | cut -d' ' -f1)"
got_diff="$("$bang" rewrite fmt "$tmpdir/messy.bang" 2>/dev/null)" && got_diff_exit=0 || got_diff_exit=$?
after_messy_md5="$(md5sum "$tmpdir/messy.bang" | cut -d' ' -f1)"
check "rewrite-fmt-diff-exit" "$got_diff_exit" "0"
check "rewrite-fmt-diff-file-untouched" "$after_messy_md5" "$before_messy_md5"
check "rewrite-fmt-diff-shows-plus-minus" "$(printf '%s' "$got_diff" | grep -c '^[-+]' || true)" "2"

# -w on the messy fixture actually rewrites it to the canonical form.
"$bang" rewrite fmt "$tmpdir/messy.bang" -w >/dev/null 2>&1
got_messy_after="$(cat "$tmpdir/messy.bang")"
want_messy_after="$("$bang" fmt "$tmpdir/messy.bang" 2>/dev/null)"
check "rewrite-fmt-w-applies" "$got_messy_after" "$want_messy_after"

# stdin route (no file): reads stdin, diff-mode default, no file to touch.
got_stdin="$(cat "$tmpdir/simple.bang" | "$bang" rewrite fmt 2>/dev/null)" && got_stdin_exit=0 || got_stdin_exit=$?
check "rewrite-fmt-stdin-exit" "$got_stdin_exit" "0"
check "rewrite-fmt-stdin-nochange" "$got_stdin" "(no changes)"

# ══ 2. `bang rewrite rename` — the happy path ══

cp "$tmpdir/simple.bang" "$tmpdir/rename-happy.bang"
before_happy_md5="$(md5sum "$tmpdir/rename-happy.bang" | cut -d' ' -f1)"
got_rename_diff="$("$bang" rewrite rename double twice "$tmpdir/rename-happy.bang" 2>/dev/null)" && got_rename_exit=0 || got_rename_exit=$?
after_happy_md5="$(md5sum "$tmpdir/rename-happy.bang" | cut -d' ' -f1)"
check "rename-happy-exit" "$got_rename_exit" "0"
check "rename-happy-diff-file-untouched" "$after_happy_md5" "$before_happy_md5"
check "rename-happy-diff-mentions-old" "$(printf '%s' "$got_rename_diff" | grep -c -- '-let rec double' || true)" "1"
check "rename-happy-diff-mentions-new" "$(printf '%s' "$got_rename_diff" | grep -c -- '+let rec twice' || true)" "1"
check "rename-happy-diff-renames-refs" "$(printf '%s' "$got_rename_diff" | grep -c '\$twice' || true)" "1"

# -w actually applies the rename, and the REWRITTEN program still evaluates (preservation held,
# `main` still runs to the SAME value `3+3` doubled twice = 12).
"$bang" rewrite rename double twice "$tmpdir/rename-happy.bang" -w >/dev/null 2>&1
got_renamed_run="$("$bang" run "$tmpdir/rename-happy.bang" 2>/dev/null)" && got_renamed_run_exit=0 || got_renamed_run_exit=$?
want_orig_run="$("$bang" run "$tmpdir/simple.bang" 2>/dev/null)"
check "rename-w-applies-and-preserves-value" "$got_renamed_run" "$want_orig_run"
check "rename-w-run-exit" "$got_renamed_run_exit" "0"
check "rename-w-uses-new-name" "$(grep -o 'twice' "$tmpdir/rename-happy.bang" | wc -l | tr -d ' ')" "3"

# ══ 3. `bang rewrite rename` — the three loud diagnostics (ADR-0046) ══

before_diag_md5="$(md5sum "$tmpdir/simple.bang" | cut -d' ' -f1)"

# (a) missing name.
got_missing="$("$bang" rewrite rename nosuch y "$tmpdir/simple.bang" 2>&1 >/dev/null)" && got_missing_exit=0 || got_missing_exit=$?
check "rename-missing-exit" "$got_missing_exit" "1"
check "rename-missing-message" "$(printf '%s' "$got_missing" | grep -c "no top-level declaration named 'nosuch'" || true)" "1"

# (b) collision — renaming to an EXISTING top-level name.
got_collide="$("$bang" rewrite rename double quad "$tmpdir/simple.bang" 2>&1 >/dev/null)" && got_collide_exit=0 || got_collide_exit=$?
check "rename-collide-exit" "$got_collide_exit" "1"
check "rename-collide-message" "$(printf '%s' "$got_collide" | grep -c "already names a top-level declaration" || true)" "1"

# (c) ambiguous — TWO decls sharing a name is a malformed-program defensive case; simulated by
# hand-writing a source with a duplicate top-level `let` name (the parser accepts it structurally;
# `rename` is the first consumer to reject it explicitly rather than silently picking one).
cat > "$tmpdir/ambiguous.bang" <<'BANG'
let x = 1
let x = 2
let main = x
BANG
got_ambig="$("$bang" rewrite rename x y "$tmpdir/ambiguous.bang" 2>&1 >/dev/null)" && got_ambig_exit=0 || got_ambig_exit=$?
check "rename-ambiguous-exit" "$got_ambig_exit" "1"
check "rename-ambiguous-message" "$(printf '%s' "$got_ambig" | grep -c "names more than one top-level declaration" || true)" "1"

# file is untouched after EVERY diagnostic failure above (no partial writes on a rejected rename).
after_diag_md5="$(md5sum "$tmpdir/simple.bang" | cut -d' ' -f1)"
check "rename-diagnostics-file-untouched" "$after_diag_md5" "$before_diag_md5"

# ══ 4. THE PRESERVATION GATE — falsify, then restore ══

# baseline: the ORIGINAL capture.bang runs and produces a value (101).
got_capture_before="$("$bang" run --engine=oracle "$tmpdir/capture.bang" 2>/dev/null)" && got_capture_before_exit=0 || got_capture_before_exit=$?
check "capture-baseline-exit" "$got_capture_before_exit" "0"
check "capture-baseline-value" "$got_capture_before" "101"

before_capture_md5="$(md5sum "$tmpdir/capture.bang" | cut -d' ' -f1)"

# FALSIFY: renaming `helper` -> `x` collides with `main`'s OWN local `let x = 5` — invisible to
# `rename`'s top-level collision check (x is not a top-level decl) but caught by the preservation
# gate re-elaborating the rewritten program (`$x` now tries to force the INTEGER `5`, not a
# thunk — an elaboration failure the ORIGINAL program never had). The gate must ABORT: no diff
# printed as a success, no write, a loud message naming the failure, nonzero exit.
got_gate_stderr="$("$bang" rewrite rename helper x "$tmpdir/capture.bang" 2>&1 >/dev/null)" && got_gate_exit=0 || got_gate_exit=$?
check "preservation-gate-catches-capture-exit" "$got_gate_exit" "1"
check "preservation-gate-catches-capture-message" "$(printf '%s' "$got_gate_stderr" | grep -c 'preservation:' || true)" "1"

# and with -w too: the gate must abort BEFORE any write, even when -w was requested.
got_gate_w_stderr="$("$bang" rewrite rename helper x "$tmpdir/capture.bang" -w 2>&1 >/dev/null)" && got_gate_w_exit=0 || got_gate_w_exit=$?
check "preservation-gate-blocks-w-exit" "$got_gate_w_exit" "1"

# RESTORE (trivial here — the gate never wrote anything, which IS the falsification's point):
# the file is STILL byte-identical to before either attempt, and still runs to the SAME value.
after_capture_md5="$(md5sum "$tmpdir/capture.bang" | cut -d' ' -f1)"
check "preservation-gate-file-untouched" "$after_capture_md5" "$before_capture_md5"
got_capture_after="$("$bang" run --engine=oracle "$tmpdir/capture.bang" 2>/dev/null)" && got_capture_after_exit=0 || got_capture_after_exit=$?
check "capture-restored-value" "$got_capture_after" "$got_capture_before"
check "capture-restored-exit" "$got_capture_after_exit" "0"

# a NON-colliding rename on the SAME fixture (renaming `helper` -> `helper2`, no capture) DOES
# pass the gate — confirms the gate is discriminating (catches the bad case, passes the good one
# on a structurally similar program), not a blanket "always reject" stub.
cp "$tmpdir/capture.bang" "$tmpdir/capture-safe.bang"
got_safe="$("$bang" rewrite rename helper helper2 "$tmpdir/capture-safe.bang" -w 2>&1)" && got_safe_exit=0 || got_safe_exit=$?
check "preservation-gate-passes-safe-rename-exit" "$got_safe_exit" "0"
got_safe_run="$("$bang" run --engine=oracle "$tmpdir/capture-safe.bang" 2>/dev/null)" && got_safe_run_exit=0 || got_safe_run_exit=$?
check "preservation-gate-safe-rename-preserves-value" "$got_safe_run" "$got_capture_before"

# ══ 5. Usage / exit-code hygiene ══

got_no_args_exit=0
"$bang" rewrite >/dev/null 2>&1 || got_no_args_exit=$?
check "rewrite-no-verb-exit" "$got_no_args_exit" "1"

got_bad_verb_exit=0
"$bang" rewrite nosuchverb "$tmpdir/simple.bang" >/dev/null 2>&1 || got_bad_verb_exit=$?
check "rewrite-unknown-verb-exit" "$got_bad_verb_exit" "1"

got_rename_missing_args_exit=0
"$bang" rewrite rename double "$tmpdir/simple.bang" >/dev/null 2>&1 || got_rename_missing_args_exit=$?
check "rename-missing-args-exit" "$got_rename_missing_args_exit" "1"

got_unreadable_exit=0
"$bang" rewrite fmt /no/such/file.bang >/dev/null 2>&1 || got_unreadable_exit=$?
check "rewrite-fmt-unreadable-file-exit" "$got_unreadable_exit" "2"

echo "──────────────────────────────"
echo "rewrite: $pass passed, $fail failed"
# Assert the expected total COUNT — catches a silently-truncated run (test-query.sh's own
# discipline).
want_total=40
got_total=$((pass + fail))
if [ "$got_total" -ne "$want_total" ]; then
  echo "✗ check-count-mismatch — expected $want_total checks to run, only $got_total did (script truncated?)"
  exit 1
fi
[ "$fail" -eq 0 ]
