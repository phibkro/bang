#!/usr/bin/env bash
# tool: role=test couples=examples/*/main.bang runs-in=verify
# test-check-json.sh — the non-interactive gate for `bang check [--json]` (issue #59).
#
# Mirrors test-fmt.sh/test-repl.sh's shape (build once, exercise the binary, diff, tally
# pass/fail). The SCHEMA byte-exactness is already gated at the Lean `#guard` level
# (Bang/Frontend/Diagnostics.lean §4) — this file gates the CLI SURFACE specifically: file-arg vs
# stdin, the human (no `--json`) path, and the 0/1/2 exit-code contract observed THROUGH the
# binary (the CLI's arg-parsing / file-reading / exit-code plumbing is new code the `#guard`s
# never touch).
#
# GOTCHA (set -euo pipefail): an unguarded `$(cmd1 | cmd2)` capture can kill this script SILENTLY
# mid-run on a nonzero exit from either stage (a truncated false-green — the tally at the bottom
# never runs, but nothing prints "fail" either). Every capture below either runs standalone (no
# pipe) with an explicit `&& … || …` exit-capture, or pipes into `jq`/`grep` with `|| true` on the
# capture. The FINAL line asserts the expected check COUNT, so a silently-truncated run is caught
# by "did we even reach the count" rather than trusted on faith.
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"
bang=".lake/build/bin/bang"

echo "building bang runner…" >&2
lake build bang >&2

pass=0
fail=0

# `check NAME GOT WANT` — generic string-equality tally.
check() {
  local name="$1" got="$2" want="$3"
  if [ "$got" = "$want" ]; then
    echo "✓ $name"; pass=$((pass + 1))
  else
    echo "✗ $name — expected [$want], got [$got]"; fail=$((fail + 1))
  fi
}

# ── ok:true, exit 0 — a clean program, via stdin ──
got_out="$(printf 'let x = 3 in x' | "$bang" check --json 2>/dev/null)" && got_exit=0 || got_exit=$?
check "ok-true-stdout" "$got_out" '{"ok":true,"diagnostics":[]}'
check "ok-true-exit" "$got_exit" "0"

# ── ok:false, exit 1 — a parse error, via stdin ──
got_out="$(printf 'let x 3 in x' | "$bang" check --json 2>/dev/null)" && got_exit=0 || got_exit=$?
check "parse-error-code-field" "$(printf '%s' "$got_out" | grep -o '"code":"parse"' || true)" '"code":"parse"'
check "parse-error-ok-false" "$(printf '%s' "$got_out" | grep -o '"ok":false' || true)" '"ok":false'
check "parse-error-exit" "$got_exit" "1"

# ── ok:false, exit 1 — a type error, via stdin ──
got_out="$(printf 'let x = 3 in $x' | "$bang" check --json 2>/dev/null)" && got_exit=0 || got_exit=$?
check "type-error-code-field" "$(printf '%s' "$got_out" | grep -o '"code":"type"' || true)" '"code":"type"'
check "type-error-exit" "$got_exit" "1"

# ── file-arg and stdin agree on the SAME input (the two entry points must be one code path) ──
got_file="$("$bang" check --json examples/state/main.bang 2>/dev/null)" || true
got_stdin="$(cat examples/state/main.bang | "$bang" check --json 2>/dev/null)" || true
check "file-and-stdin-agree" "$got_stdin" "$got_file"
check "file-arg-ok-true" "$got_file" '{"ok":true,"diagnostics":[]}'

# ── #75 REGRESSION GUARDS: single-file FILE input must match stdin's span/code EXACTLY, for both
# a nameHint-located type error and a parse error (round-2 finding: file input silently dropped
# both to span:null, and additionally mislabeled the parse error code:"type"). ──
tmpdir="$(mktemp -d)"
trap 'rm -rf "$tmpdir"' EXIT

# single-file, nameHint-located type error ('force: not a thunk') — file must equal stdin byte-for-byte.
printf 'let x = 3 in $x' > "$tmpdir/type-err.bang"
got_stdin_type="$(printf 'let x = 3 in $x' | "$bang" check --json 2>/dev/null)" || true
got_file_type="$("$bang" check --json "$tmpdir/type-err.bang" 2>/dev/null)" || true
check "75-single-file-type-error-file-eq-stdin" "$got_file_type" "$got_stdin_type"
check "75-single-file-type-error-span-present" "$(printf '%s' "$got_file_type" | grep -o '"span":null' || true)" ""

# single-file, PARSE error — file must carry code:"parse" (not "type") AND a real span (not null).
printf 'let x 3 in x' > "$tmpdir/parse-err.bang"
got_file_parse="$("$bang" check --json "$tmpdir/parse-err.bang" 2>/dev/null)" || true
check "75-single-file-parse-error-code-parse" "$(printf '%s' "$got_file_parse" | grep -o '"code":"parse"' || true)" '"code":"parse"'
check "75-single-file-parse-error-not-mislabeled-type" "$(printf '%s' "$got_file_parse" | grep -o '"code":"type"' || true)" ""
check "75-single-file-parse-error-span-present" "$(printf '%s' "$got_file_parse" | grep -o '"span":null' || true)" ""
got_stdin_parse="$(printf 'let x 3 in x' | "$bang" check --json 2>/dev/null)" || true
check "75-single-file-parse-error-file-eq-stdin" "$got_file_parse" "$got_stdin_parse"

# ── genuine MULTI-file program: the documented v1 grant (span:null, code:"type") must stay INTACT
# — the #75 fix only widens the single-file fast path, never narrows the resolver path's own
# (still-honest) limitation. ──
mkdir -p "$tmpdir/mf"
printf 'pub let x = 3' > "$tmpdir/mf/Lib.bang"
printf 'import Lib\nlet main = $Lib.x + "a"' > "$tmpdir/mf/main.bang"
got_mf="$("$bang" check --json "$tmpdir/mf/main.bang" 2>/dev/null)" || true
check "75-multi-file-grant-intact-code-type" "$(printf '%s' "$got_mf" | grep -o '"code":"type"' || true)" '"code":"type"'
check "75-multi-file-grant-intact-span-null" "$(printf '%s' "$got_mf" | grep -o '"span":null' || true)" '"span":null'

# ── every examples/*/main.bang round-trips ok:true through --json (the corpus, not just one file) ──
examples_pass=0
examples_fail=0
for dir in examples/*/; do
  main="$dir/main.bang"
  name="$(basename "$dir")"
  [ -f "$main" ] || continue
  out="$("$bang" check --json "$main" 2>/dev/null)" || true
  if [ "$out" = '{"ok":true,"diagnostics":[]}' ]; then
    examples_pass=$((examples_pass + 1))
  else
    echo "✗ examples-sweep-$name — expected ok:true, got [$out]"; examples_fail=$((examples_fail + 1))
  fi
done
if [ "$examples_fail" -eq 0 ]; then
  echo "✓ examples-sweep ($examples_pass/$examples_pass examples)"; pass=$((pass + 1))
else
  echo "✗ examples-sweep ($examples_fail failed)"; fail=$((fail + 1))
fi

# ── the HUMAN (no --json) path: pass prints "ok"/exit 0, fail prints "error at L:C: …"/exit 1 ──
got_out="$(printf 'let x = 3 in x' | "$bang" check 2>/dev/null)" && got_exit=0 || got_exit=$?
check "human-pass-stdout" "$got_out" "ok"
check "human-pass-exit" "$got_exit" "0"

got_out="$(printf 'let x 3 in x' | "$bang" check 2>/dev/null)" && got_exit=0 || got_exit=$?
check "human-fail-stdout-empty" "$got_out" ""
check "human-fail-exit" "$got_exit" "1"
got_stderr="$(printf 'let x 3 in x' | "$bang" check 2>&1 >/dev/null)" || true
if [[ "$got_stderr" == *"error at"* ]]; then
  echo "✓ human-fail-stderr-located"; pass=$((pass + 1))
else
  echo "✗ human-fail-stderr-located — expected an 'error at' line, got [$got_stderr]"; fail=$((fail + 1))
fi

# ── TOOL error (exit 2): unreadable file, JSON mode — stdout stays EMPTY (never folded into the
# diagnostic JSON), stderr carries the message, distinct from exit 0/1 ──
got_out="$("$bang" check --json /no/such/file.bang 2>/dev/null)" && got_exit=0 || got_exit=$?
check "tool-error-json-stdout-empty" "$got_out" ""
check "tool-error-json-exit" "$got_exit" "2"
got_stderr="$("$bang" check --json /no/such/file.bang 2>&1 >/dev/null)" || true
if [[ "$got_stderr" == *"error:"* ]]; then
  echo "✓ tool-error-json-stderr-content"; pass=$((pass + 1))
else
  echo "✗ tool-error-json-stderr-content — expected an 'error:' line, got [$got_stderr]"; fail=$((fail + 1))
fi

# ── TOOL error (exit 2): unreadable file, human mode — SAME exit code as --json (the tool-error
# tier is orthogonal to --json/human) ──
got_out="$("$bang" check /no/such/file.bang 2>/dev/null)" && got_exit=0 || got_exit=$?
check "tool-error-human-stdout-empty" "$got_out" ""
check "tool-error-human-exit" "$got_exit" "2"

# ── too many positional args is a usage error, not a silent pick-first/pick-last ──
got_argerr_exit=0
"$bang" check a.bang b.bang >/dev/null 2>&1 || got_argerr_exit=$?
check "too-many-args-exit" "$got_argerr_exit" "1"

# ── jq-parseability: the JSON output is valid JSON, not just byte-matching our own expectation.
# Skip with a note if jq isn't in the dev shell (do NOT add jq to the flake for this). NOTE: under
# `pipefail`, a 3-stage pipe's overall status is the RIGHTMOST NONZERO code — `bang check --json`
# exits 1 on ok:false, which would poison the pipeline status even when `jq -e`'s OWN verdict is
# true. So the JSON is captured first (its own `&&/||` exit, `bang`'s exit is EXPECTED to be 1
# here and is not the thing under test), then piped into `jq` alone. ──
if command -v jq >/dev/null 2>&1; then
  jq_in="$(printf 'let x = 3 in $x' | "$bang" check --json 2>/dev/null)" || true
  if printf '%s' "$jq_in" | jq -e '.ok == false and (.diagnostics | length) == 1' >/dev/null 2>&1; then
    echo "✓ jq-parseable"; pass=$((pass + 1))
  else
    echo "✗ jq-parseable — output did not parse as expected JSON shape"; fail=$((fail + 1))
  fi
else
  echo "· jq-parseable — SKIPPED (jq not in dev shell; not adding it for this check)"
fi

echo "──────────────────────────────"
echo "check-json: $pass passed, $fail failed"
# Assert the expected total COUNT — catches a silently-truncated run (the gotcha the mission
# brief calls out) even if every individual `check` that DID run happened to pass.
want_total=30
got_total=$((pass + fail))
if [ "$got_total" -ne "$want_total" ]; then
  echo "✗ check-count-mismatch — expected $want_total checks to run, only $got_total did (script truncated?)"
  exit 1
fi
[ "$fail" -eq 0 ]
