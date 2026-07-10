#!/usr/bin/env bash
# tool: role=test couples=none runs-in=verify
source "$(git rev-parse --show-toplevel 2>/dev/null)/tools/tool-log.sh" 2>/dev/null && tool_log "$(basename "$0")" || true
# test-repl.sh — the non-interactive gate for `bang repl` (issue #7).
#
# The REPL is agent-facing (piped stdin, no TTY), so its test surface IS a
# scripted piped session: feed a multi-line "transcript" on stdin, capture
# stdout, diff against an expected transcript. Mirrors check-examples.sh's
# shape (build once, exercise the binary, diff, tally pass/fail).
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"
bang=".lake/build/bin/bang"

if [ -z "${BANG_BIN_FRESH:-}" ]; then
  echo "building bang runner…" >&2
  lake build bang >&2
fi

pass=0
fail=0

# `check NAME INPUT EXPECTED_STDOUT EXPECTED_EXIT` — feeds INPUT (already
# newline-separated) to `bang repl` on stdin, compares stdout + exit code.
check() {
  local name="$1" input="$2" want_out="$3" want_exit="$4"
  local got_out got_exit
  got_out="$(printf '%b' "$input" | "$bang" repl 2>/dev/null)" && got_exit=0 || got_exit=$?
  if [ "$got_out" = "$want_out" ] && [ "$got_exit" = "$want_exit" ]; then
    echo "✓ $name"; pass=$((pass + 1))
  else
    echo "✗ $name — expected stdout=[$want_out] exit=$want_exit, got stdout=[$got_out] exit=$got_exit"
    fail=$((fail + 1))
  fi
}

# `check_stderr NAME INPUT STDERR_SUBSTRING EXPECTED_EXIT` — like `check`, but asserts a SUBSTRING
# of stderr instead of exact stdout. Distinguishes "the right feature fired" from "some unrelated
# usage error happened to share exit code 1" (a real risk for these three since `bang`'s top-level
# usage error is ALSO exit 1) — without this, a broken `:let`/unknown-command/type-error path could
# false-green by coincidentally matching only on the exit code.
check_stderr() {
  local name="$1" input="$2" want_substr="$3" want_exit="$4"
  local got_err got_exit
  got_err="$(printf '%b' "$input" | "$bang" repl 2>&1 >/dev/null)" && got_exit=0 || got_exit=$?
  if [[ "$got_err" == *"$want_substr"* ]] && [ "$got_exit" = "$want_exit" ]; then
    echo "✓ $name"; pass=$((pass + 1))
  else
    echo "✗ $name — expected stderr containing [$want_substr] exit=$want_exit, got stderr=[$got_err] exit=$got_exit"
    fail=$((fail + 1))
  fi
}

# ── bare expression evaluates and exits (the core piped-agent use case) ──
check "bare-expr" "1 + 2\n" "3" "0"

# ── :let persists a binding for later turns, oldest-first nesting ──
check "let-persist" ":let x = 3\n:let y = x + 1\ny * 2\n" "8" "0"

# ── :let accepts no surrounding spaces ──
check "let-no-spaces" ":let x=3\nx+1\n" "4" "0"

# ── :q stops the loop before running anything after it ──
check "quit-stops-loop" ":q\n1+1\n" "" "0"

# ── EOF (no trailing :q) behaves the same as an explicit :q ──
check "eof-quits" "1+1" "2" "0"

# ── :help prints the command list, runs nothing, exits 0 ──
check "help" ":help\n" "commands:
  :t <expr>, :type <expr>   show the checked type ! effect row of <expr>
  :let <name> = <expr>      persist a definition for the rest of the session
  :load <file>              run a file's contents as one turn (not persisted)
  :help, :?                 this text
  :q, :quit                 exit (also Ctrl-D / EOF)
  <expr>                    evaluate against all persisted definitions and print the result" "0"

# ── :t / :type happy path — the rendered `showType` string (Bang.Frontend.TypeCheck.typeStringOfProg) ──
check "type-happy-path" ":t 1 + 2\n" "Int" "0"
check "type-alias" ":type 1 + 2\n" "Int" "0"

# ── :t with no expr fails loud (own message, not a generic usage wall) ──
check_stderr "type-no-expr" ":t\n" "\`:t\`/\`:type\` expects" "1"

# ── :t surfaces a type/elaboration error through the SAME checker as evaluation ──
check_stderr "type-error" ":t unboundvar\n" "unbound variable unboundvar" "1"

# ── :let then :t — a persisted binding must be visible to :t exactly like it is to evaluation
# (both route through the SAME wrapBindings mechanism, so this is also a same-prelude regression
# check between the eval path and the type-display path) ──
check "type-sees-let-binding" ":let x = 3\n:t x + 1\n" "Int" "0"

# ── a bad :let (missing '=') fails loud with ITS OWN message, not a generic usage wall ──
check_stderr "bad-let" ":let\n" "\`:let\` expects" "1"

# ── an unknown command fails loud rather than silently matching bare-expr ──
check_stderr "unknown-command" ":bogus\n" "unknown command ':bogus'" "1"

# ── a type error surfaces through the SAME pipeline as `bang run`/`bang eval` ──
check_stderr "type-error-exit" "unboundvar\n" "unbound variable unboundvar" "1"

# ── --compiled engine flag reaches the REPL (same value as the oracle engine) ──
got_out="$(printf '1 + 2\n' | "$bang" repl --compiled 2>/dev/null)"
if [ "$got_out" = "3" ]; then
  echo "✓ compiled-engine-flag"; pass=$((pass + 1))
else
  echo "✗ compiled-engine-flag — expected [3], got [$got_out]"; fail=$((fail + 1))
fi

# ── :load runs a file's contents as one turn, seeing prior :let bindings ──
tmpfile="$(mktemp --tmpdir bang-repl-test-XXXXXX.bang)"
trap 'rm -f "$tmpfile"' EXIT
printf 'x + 100' > "$tmpfile"
check "load-file" ":let x = 1\n:load $tmpfile\n" "101" "0"

# ── :load on a missing file fails loud instead of silently continuing ──
check_stderr "load-missing-file" ":load /nonexistent-path-for-bang-repl-test.bang\n" \
  "could not read file '/nonexistent-path-for-bang-repl-test.bang'" "1"

echo "──────────────────────────────"
echo "repl: $pass passed, $fail failed"
[ "$fail" -eq 0 ]
