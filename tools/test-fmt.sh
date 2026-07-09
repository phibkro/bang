#!/usr/bin/env bash
# test-fmt.sh — the non-interactive gate for `bang fmt` (issue #58's CLI half).
#
# Mirrors test-repl.sh's shape (build once, exercise the binary, diff, tally pass/fail). The
# formatter CORE's laws (idempotency/round-trip over a corpus, `Bang/Frontend/Format.lean` §6-7)
# are already gated at the Lean `#guard` level — this file gates the CLI SURFACE specifically:
# file-arg vs stdin, exit codes, and idempotency observed THROUGH the binary (not just the pure
# function), since the CLI's stdin-reading/arg-parsing is new code the `#guard`s never touch.
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"
bang=".lake/build/bin/bang"

echo "building bang runner…" >&2
lake build bang >&2

pass=0
fail=0

# `check NAME GOT WANT` — generic string-equality tally (used for ad-hoc checks below that don't
# fit the "single command, single assertion" shape of check_cmd/check_cmd_stderr).
check() {
  local name="$1" got="$2" want="$3"
  if [ "$got" = "$want" ]; then
    echo "✓ $name"; pass=$((pass + 1))
  else
    echo "✗ $name — expected [$want], got [$got]"; fail=$((fail + 1))
  fi
}

# ── happy path: a known corpus file → its exact canonical form ──
# (examples/state/main.bang is a small fixed program; pin the LITERAL expected output so a printer
# regression shows as a diff here, not just "still parses".)
got_out="$("$bang" fmt examples/state/main.bang 2>/dev/null)" && got_exit=0 || got_exit=$?
want_out="state 0 in let c = {get} in let z = put 5 in \$c"
check "happy-path-stdout" "$got_out" "$want_out"
check "happy-path-exit" "$got_exit" "0"

# ── file-arg and stdin agree on the SAME input (the two entry points must be one code path) ──
got_stdin="$(cat examples/state/main.bang | "$bang" fmt 2>/dev/null)" || true
check "file-and-stdin-agree" "$got_stdin" "$got_out"

# ── idempotency AT THE CLI: piping fmt's own output back through fmt is byte-identical ──
got_twice="$(printf '%s' "$got_out" | "$bang" fmt 2>/dev/null)" || true
check "idempotent-via-cli" "$got_twice" "$got_out"

# ── idempotency swept over every examples/*/main.bang (the corpus, not just one file) ──
idempotent_pass=0
idempotent_fail=0
for dir in examples/*/; do
  main="$dir/main.bang"
  name="$(basename "$dir")"
  [ -f "$main" ] || continue
  once="$("$bang" fmt "$main" 2>/dev/null)" || { echo "✗ idempotent-sweep-$name — fmt itself failed"; idempotent_fail=$((idempotent_fail + 1)); continue; }
  twice="$(printf '%s' "$once" | "$bang" fmt 2>/dev/null)" || true
  if [ "$once" = "$twice" ]; then
    idempotent_pass=$((idempotent_pass + 1))
  else
    echo "✗ idempotent-sweep-$name — fmt(fmt(x)) != fmt(x)"; idempotent_fail=$((idempotent_fail + 1))
  fi
done
if [ "$idempotent_fail" -eq 0 ]; then
  echo "✓ idempotent-sweep ($idempotent_pass/$idempotent_pass examples)"; pass=$((pass + 1))
else
  echo "✗ idempotent-sweep ($idempotent_fail failed)"; fail=$((fail + 1))
fi

# ── parse-error path: bad input fails loud, stdout stays EMPTY, distinct nonzero exit ──
got_err_out="$(printf 'let x 3 in x' | "$bang" fmt 2>/dev/null)" && got_err_exit=0 || got_err_exit=$?
check "parse-error-stdout-empty" "$got_err_out" ""
check "parse-error-exit" "$got_err_exit" "1"
got_stderr="$(printf 'let x 3 in x' | "$bang" fmt 2>&1 >/dev/null)" || true
if [[ "$got_stderr" == *"error:"* ]]; then
  echo "✓ parse-error-stderr-content"; pass=$((pass + 1))
else
  echo "✗ parse-error-stderr-content — expected an 'error:' line, got [$got_stderr]"; fail=$((fail + 1))
fi

# ── too many positional args is a usage error, not a silent pick-first/pick-last ──
got_argerr_exit=0
"$bang" fmt a.bang b.bang >/dev/null 2>&1 || got_argerr_exit=$?
check "too-many-args-exit" "$got_argerr_exit" "1"

echo "──────────────────────────────"
echo "fmt: $pass passed, $fail failed"
[ "$fail" -eq 0 ]
