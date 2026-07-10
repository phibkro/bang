#!/usr/bin/env bash
# tool: role=test couples=none runs-in=verify
source "$(git rev-parse --show-toplevel 2>/dev/null)/tools/tool-log.sh" 2>/dev/null && tool_log "$(basename "$0")" || true
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

contains() {
  local name="$1" haystack="$2" needle="$3"
  if [[ "$haystack" == *"$needle"* ]]; then
    echo "✓ $name"; pass=$((pass + 1))
  else
    echo "✗ $name — expected to find [$needle] in [$haystack]"; fail=$((fail + 1))
  fi
}

# ── a REAL, TRUE trait law: IntOrd.trans holds — PLUS (#74 part 2) the unreachable-impl warning,
# since `impl IntOrd for Int { fn lt(a, b) = ... }` aliases the built-in `<`: v1's law sampler
# (`genIntSamples`) only ever generates plain Int literals, so a law param's declared trait target
# is cosmetic to the SAMPLE VALUES either way (a non-Int target wouldn't change what's actually
# exercised — the sampler has no non-Int generator at all, a pre-existing, separately-scoped v1
# ceiling) — the HONEST fix is surfacing that this impl is unreachable, not hiding it behind a
# target-type change that wouldn't actually fix the underlying non-dispatch. ──
holds_tmp="$(mktemp /tmp/bang-law-holds-XXXXXX.bang)"
trap 'rm -f "$holds_tmp" "$bogus_tmp" "$nolaws_tmp" "$trailing_tmp"' EXIT
printf 'trait IntOrd { fn lt(a, b) -> (Unit + Unit) law trans(a, b, c): a < b => b < c => a < c }\nimpl IntOrd for Int { fn lt(a, b) = a < b }' > "$holds_tmp"
holds_out="$("$bang" test "$holds_tmp" 2>/dev/null)" && holds_exit=0 || holds_exit=$?
check "holds-exit" "$holds_exit" "1"
contains "holds-stdout-pass" "$holds_out" "IntOrd.trans"
contains "holds-stdout-pass-marker" "$holds_out" "PASS"
contains "holds-stdout-deadimpl-warning" "$holds_out" "can never run"

# ── a DELIBERATELY FALSE trait law: reports a counterexample, exit 1 (same unreachable-impl note
# applies — the warning and the counterexample coexist, one per outcome). ──
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

# ── #74 part 1: a law body calling its trait op DIRECTLY BY NAME (`plt(a, b)`, not through the
# overloaded operator) is diagnosed with a clear, actionable message — NOT the previous opaque
# runtime crash (`app: callee is not a function`) the stranger test hit with zero PASS/FAIL/shrink
# ever reached. Uses a NON-Int target ((Int*Int)) so this fixture stays orthogonal to part-2's
# unreachable-impl check above — the point here is the DIRECT-CALL shape, not the target type. ──
directcall_tmp="$(mktemp /tmp/bang-law-directcall-XXXXXX.bang)"
trap 'rm -f "$holds_tmp" "$bogus_tmp" "$nolaws_tmp" "$trailing_tmp" "$directcall_tmp"' EXIT
printf 'trait PairEq { fn peq(a, b) -> Int law refl(x): peq(x, x) == 1 }\nimpl PairEq for (Int * Int) { fn peq(p, q) = let (a, b) = p in (let (c, d) = q in (let e = a == c in if e then 1 else 0)) }' > "$directcall_tmp"
directcall_out="$("$bang" test "$directcall_tmp" 2>/dev/null)" && directcall_exit=0 || directcall_exit=$?
check "directcall-exit" "$directcall_exit" "1"
contains "directcall-names-op" "$directcall_out" "'peq'"
contains "directcall-names-adr" "$directcall_out" "ADR-0068"

# ── stdin works the same as a file argument (mirrors fmt/check's convention) ──
stdin_out="$(cat "$holds_tmp" | "$bang" test 2>/dev/null)" && stdin_exit=0 || stdin_exit=$?
check "stdin-exit" "$stdin_exit" "1"
check "stdin-matches-file" "$stdin_out" "$holds_out"

echo "──────────────────────────────"
echo "law: $pass passed, $fail failed"
[ "$fail" -eq 0 ]
