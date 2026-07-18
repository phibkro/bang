#!/usr/bin/env bash
# tool: role=test couples=none runs-in=verify
source "$(git rev-parse --show-toplevel 2>/dev/null)/tools/tool-log.sh" 2>/dev/null && tool_log "$(basename "$0")" || true
# test-law.sh — the non-interactive gate for `bang test` (issue #60's CLI wiring).
#
# Exercises the LawTest/lawInstancesOf discovery seam THROUGH the compiled binary: real trait and
# effect-contract laws that hold, deliberately false realizations (counterexamples), a program with
# no laws at all (vacuous success), and the decls-only-input footgun this slice's manual testing found
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

# ── a REAL, TRUE trait law on a REACHABLE (non-Int) carrier: IntOrd.trans holds for real —
# `(Int * Int)` is not shadowed by the kernel's `<` δ-rule, so `env.insts` IS consulted and the
# impl's own `lt` actually runs (unlike an `impl … for Int`, see the deadimpl fixture below). ──
holds_tmp="$(mktemp /tmp/bang-law-holds-XXXXXX.bang)"
codec_holds_tmp="$(mktemp /tmp/bang-law-codec-holds-XXXXXX.bang)"
codec_bogus_tmp="$(mktemp /tmp/bang-law-codec-bogus-XXXXXX.bang)"
trap 'rm -f "$holds_tmp" "${bogus_tmp:-}" "${nolaws_tmp:-}" "${trailing_tmp:-}" "${deadimpl_tmp:-}" "${directcall_tmp:-}" "$codec_holds_tmp" "$codec_bogus_tmp"' EXIT
printf 'trait IntOrd { fn lt(a, b) -> (Unit + Unit) law trans(a, b, c): a < b => b < c => a < c }\nimpl IntOrd for (Int * Int) { fn lt(p, q) = let (a, _) = p in (let (b, _) = q in a < b) }' > "$holds_tmp"
holds_out="$("$bang" test "$holds_tmp" 2>/dev/null)" && holds_exit=0 || holds_exit=$?
check "holds-exit" "$holds_exit" "0"
contains "holds-stdout-pass" "$holds_out" "IntOrd.trans"
contains "holds-stdout-pass-marker" "$holds_out" "PASS"

# ── a DELIBERATELY FALSE trait law on the same REACHABLE carrier: reports a counterexample, exit 1. ──
bogus_tmp="$(mktemp /tmp/bang-law-bogus-XXXXXX.bang)"
printf 'trait IntOrd { fn lt(a, b) -> (Unit + Unit) law bogus(a, b): a < b => b < a }\nimpl IntOrd for (Int * Int) { fn lt(p, q) = let (a, _) = p in (let (b, _) = q in a < b) }' > "$bogus_tmp"
bogus_out="$("$bang" test "$bogus_tmp" 2>/dev/null)" && bogus_exit=0 || bogus_exit=$?
check "bogus-exit" "$bogus_exit" "1"
contains "bogus-stdout-fail-marker" "$bogus_out" "FAIL"
contains "bogus-stdout-counterexample" "$bogus_out" "counterexample"

# ── Effect laws are CONTRACTS, checked once per named HANDLER realization. Two correct Codec
# realizations produce four passing instances (2 laws × 2 handlers). ──
printf 'effect Codec { encode : Int -> Int decode : Int -> Int law decode_encode(codec, x): let y = codec.encode(x) in codec.decode(y) == x law encode_decode(codec, x): let y = codec.decode(x) in codec.encode(y) == x }\nhandler Identity implements Codec { encode(x) => x, decode(x) => x }\nhandler Shift7 implements Codec { encode(x) => x + 7, decode(x) => x - 7 }' > "$codec_holds_tmp"
codec_holds_out="$("$bang" test "$codec_holds_tmp" 2>/dev/null)" && codec_holds_exit=0 || codec_holds_exit=$?
check "codec-holds-exit" "$codec_holds_exit" "0"
contains "codec-identity-pass" "$codec_holds_out" "Codec@Identity.decode_encode — PASS"
contains "codec-shift-pass" "$codec_holds_out" "Codec@Shift7.encode_decode — PASS"
contains "codec-cross-product" "$codec_holds_out" "laws: 4/4 passed"

# ── A corpus consumer owns the same semantic unit in a module: stage-swap's runtime-selected
# installer functions statically install two named handlers that share one stability contract. ──
stage_out="$("$bang" test examples/stage-swap/Stage.bang 2>/dev/null)" && stage_exit=0 || stage_exit=$?
check "stage-contract-exit" "$stage_exit" "0"
contains "stage-test-pass" "$stage_out" "Net@Test.stable — PASS"
contains "stage-prod-pass" "$stage_out" "Net@Prod.stable — PASS"

# ── A broken realization is rejected by the SAME runner with a sampled counterexample. ──
printf 'effect Codec { encode : Int -> Int decode : Int -> Int law roundtrip(codec, x): let y = codec.encode(x) in codec.decode(y) == x }\nhandler BrokenShift implements Codec { encode(x) => x + 7, decode(x) => x - 6 }' > "$codec_bogus_tmp"
codec_bogus_out="$("$bang" test "$codec_bogus_tmp" 2>/dev/null)" && codec_bogus_exit=0 || codec_bogus_exit=$?
check "codec-bogus-exit" "$codec_bogus_exit" "1"
contains "codec-bogus-realization" "$codec_bogus_out" "Codec@BrokenShift.roundtrip"
contains "codec-bogus-counterexample" "$codec_bogus_out" "counterexample"

# ── #113: an `impl … for Int` aliasing a built-in operator is UNREACHABLE (#74 part 2) — its law
# must report SKIPPED, never a misleading PASS (the impl's own body never runs; sampling it would
# only exercise the KERNEL's own `<`). The unreachable-impl ERROR line and the SKIPPED line both
# appear; exit 1 (the ERROR alone already fails the run). ──
deadimpl_tmp="$(mktemp /tmp/bang-law-deadimpl-XXXXXX.bang)"
printf 'trait IntOrd { fn lt(a, b) -> (Unit + Unit) law trans(a, b, c): a < b => b < c => a < c }\nimpl IntOrd for Int { fn lt(a, b) = a < b }' > "$deadimpl_tmp"
deadimpl_out="$("$bang" test "$deadimpl_tmp" 2>/dev/null)" && deadimpl_exit=0 || deadimpl_exit=$?
check "deadimpl-exit" "$deadimpl_exit" "1"
contains "deadimpl-stdout-deadimpl-warning" "$deadimpl_out" "can never run"
contains "deadimpl-stdout-skip-marker" "$deadimpl_out" "SKIPPED"
if [[ "$deadimpl_out" == *"— PASS"* ]]; then
  echo "✗ deadimpl-stdout-no-misleading-pass — found [— PASS] in [$deadimpl_out]"; fail=$((fail + 1))
else
  echo "✓ deadimpl-stdout-no-misleading-pass"; pass=$((pass + 1))
fi

# ── NO trait laws in the program: vacuous success, exit 0 ──
nolaws_tmp="$(mktemp /tmp/bang-law-nolaws-XXXXXX.bang)"
printf 'let x = 3' > "$nolaws_tmp"
nolaws_out="$("$bang" test "$nolaws_tmp" 2>/dev/null)" && nolaws_exit=0 || nolaws_exit=$?
check "nolaws-exit" "$nolaws_exit" "0"
contains "nolaws-stdout" "$nolaws_out" "no laws found"

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
printf 'trait PairEq { fn peq(a, b) -> Int law refl(x): peq(x, x) == 1 }\nimpl PairEq for (Int * Int) { fn peq(p, q) = let (a, b) = p in (let (c, d) = q in (let e = a == c in if e then 1 else 0)) }' > "$directcall_tmp"
directcall_out="$("$bang" test "$directcall_tmp" 2>/dev/null)" && directcall_exit=0 || directcall_exit=$?
check "directcall-exit" "$directcall_exit" "1"
contains "directcall-names-op" "$directcall_out" "'peq'"
contains "directcall-names-adr" "$directcall_out" "ADR-0068"

# ── stdin works the same as a file argument (mirrors fmt/check's convention) ──
stdin_out="$(cat "$holds_tmp" | "$bang" test 2>/dev/null)" && stdin_exit=0 || stdin_exit=$?
check "stdin-exit" "$stdin_exit" "0"
check "stdin-matches-file" "$stdin_out" "$holds_out"

echo "──────────────────────────────"
echo "law: $pass passed, $fail failed"
[ "$fail" -eq 0 ]
