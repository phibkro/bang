#!/usr/bin/env bash
# tool: role=test couples=none runs-in=verify
# test-law.sh — the non-interactive gate for `bang test` (issue #60's CLI wiring).
#
# Exercises the LawTest/lawInstancesOf discovery seam THROUGH the compiled binary: a real trait
# law that holds, one that's deliberately false (a counterexample), a program with no laws at
# all (vacuous success), and the decls-only-input footgun this slice's own manual testing found
# (a trailing expression silently corrupts every discovered law's test program — pre-checked via
# `Prog.isLibrary` before ever calling into `Bang.LawTest`, so the error names the real cause).
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

# ── a REAL, TRUE trait law: IntOrd.trans holds ──
holds_tmp="$(mktemp /tmp/bang-law-holds-XXXXXX.bang)"
trap 'rm -f "$holds_tmp" "$bogus_tmp" "$nolaws_tmp" "$trailing_tmp"' EXIT
printf 'trait IntOrd { fn lt(a, b) -> (Unit + Unit) law trans(a, b, c): a < b => b < c => a < c }\nimpl IntOrd for Int { fn lt(a, b) = a < b }' > "$holds_tmp"
holds_out="$("$bang" test "$holds_tmp" 2>/dev/null)" && holds_exit=0 || holds_exit=$?
check "holds-exit" "$holds_exit" "0"
contains "holds-stdout-pass" "$holds_out" "IntOrd.trans"
contains "holds-stdout-pass-marker" "$holds_out" "PASS"

# ── a DELIBERATELY FALSE trait law: reports a counterexample, exit 1 ──
bogus_tmp="$(mktemp /tmp/bang-law-bogus-XXXXXX.bang)"
printf 'trait IntOrd { fn lt(a, b) -> (Unit + Unit) law bogus(a, b): a < b => b < a }\nimpl IntOrd for Int { fn lt(a, b) = a < b }' > "$bogus_tmp"
bogus_out="$("$bang" test "$bogus_tmp" 2>/dev/null)" && bogus_exit=0 || bogus_exit=$?
check "bogus-exit" "$bogus_exit" "1"
contains "bogus-stdout-fail-marker" "$bogus_out" "FAIL"
contains "bogus-stdout-counterexample" "$bogus_out" "counterexample"

# ── NO trait laws in the program: vacuous success, exit 0 ──
nolaws_tmp="$(mktemp /tmp/bang-law-nolaws-XXXXXX.bang)"
printf 'let x = 3' > "$nolaws_tmp"
nolaws_out="$("$bang" test "$nolaws_tmp" 2>/dev/null)" && nolaws_exit=0 || nolaws_exit=$?
check "nolaws-exit" "$nolaws_exit" "0"
contains "nolaws-stdout" "$nolaws_out" "no trait laws found"

# ── DECLS-ONLY FOOTGUN: a trailing expression is caught BEFORE it corrupts every law's report ──
trailing_tmp="$(mktemp /tmp/bang-law-trailing-XXXXXX.bang)"
printf 'trait IntOrd { fn lt(a, b) -> (Unit + Unit) law trans(a, b, c): a < b => b < c => a < c }\nimpl IntOrd for Int { fn lt(a, b) = a < b }\n0' > "$trailing_tmp"
trailing_stderr="$("$bang" test "$trailing_tmp" 2>&1 >/dev/null)" && trailing_exit=0 || trailing_exit=$?
check "trailing-body-exit" "$trailing_exit" "1"
contains "trailing-body-message" "$trailing_stderr" "DECLS-ONLY"
# stdout must stay EMPTY on this path (no bogus per-law report reaches it).
trailing_stdout="$("$bang" test "$trailing_tmp" 2>/dev/null)" || true
check "trailing-body-stdout-empty" "$trailing_stdout" ""

# ── stdin works the same as a file argument (mirrors fmt/check's convention) ──
stdin_out="$(cat "$holds_tmp" | "$bang" test 2>/dev/null)" && stdin_exit=0 || stdin_exit=$?
check "stdin-exit" "$stdin_exit" "0"
check "stdin-matches-file" "$stdin_out" "$holds_out"

echo "──────────────────────────────"
echo "law: $pass passed, $fail failed"
[ "$fail" -eq 0 ]
