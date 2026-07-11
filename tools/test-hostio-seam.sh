#!/usr/bin/env bash
# tool: role=test couples=Main.lean,Bang/Backend/EnvMachine.lean,std/Io.bang runs-in=verify
source "$(git rev-parse --show-toplevel 2>/dev/null)/tools/tool-log.sh" 2>/dev/null && tool_log "$(basename "$0")" || true
# test-hostio-seam.sh — the SEAM + CLI-surface gate for the host-IO wedge (ADR-0104).
#
# NOT AN END-TO-END REAL-IO GATE (honest naming, ADR-0104 §Scope): live host IO does not ship in this
# slice — a normal program's own `with` catches its host ops lexically, so the outermost host seam is
# reached only via the H1 elaboration affordance (the named NEXT slice). This battery gates the SEAM
# MECHANISM (via the compiled #guards, below) + the driver's SIM-path + flag SURFACE — everything that
# IS reachable today — never presented as e2e.
#
# WHAT THIS GATES vs WHAT THE #guards GATE (the seam's invariant-#1 oracle):
#   - the ENGINE seam's correctness (evalEHost ≡ evalE at hostResponses=[], and the seam
#     servicing a granted host perform + response) is the compiled DRIFT + SEAM #guards in
#     Bang/Backend/EnvMachine.lean — gated at BUILD time (a failing #guard fails `lake build`,
#     which run-batteries.sh runs once up front). Those are the mechanism's invariant-#1 gate.
#   - THIS file gates the CLI SURFACE the #guards can't reach (filesystem, exit codes, flag
#     parsing, error-message content): the sim wedge runs, `--allow` name→label resolution +
#     its loud error, the record/replay driver path is TRANSPARENT (record then replay
#     reproduces the run byte-identically), and the `--max-host-requests` ceiling exists.
#
# SCOPE NOTE (ADR-0104 §4, the H1 reach, #126 — LANDED): a v1 program can EITHER install its own
# `with Io_* {…}` handler (catches every host op lexically, driver-independent — examples/hostio-echo/
# main.bang, section 1-5 below) OR use the module-qualified AMBIENT spelling (`Io.print`, no `with` —
# examples/hostio-echo/ambient.bang, section 6 below), which reaches the driver's outermost grant
# surface UNCONDITIONALLY. MEASURED CORRECTION to this ADR's original nearness claim: a `with
# Io_Console` does NOT intercept an ambient `Io.print` call even when lexically enclosing it (see the
# ADR-0104 §4 "CORRECTION" section + the `#guard` refutation witness in TypeCheck.lean) — the two
# spellings are deliberately SEPARATE constructs post-correction, not two paths to one nearness-
# resolved call. Section 6 is the FIRST leg of this battery that reaches REAL host IO through the
# ambient path (sections 1-5 exercise the SIM-catches-lexically path + the driver's flag/record/
# replay surface, which never actually reaches real IO for hostio-echo's own program — verified: its
# `with Io_Console` catches every op even under `--env=real`, so those sections test the DRIVER's
# transparency, not a live host boundary).
#
# PIPEFAIL GOTCHA (guarded throughout): every fallible command feeding a `$(...)` capture is
# followed by `&& code=0 || code=$?` — a guard-free failing command under `set -e`/`-o pipefail`
# would abort the whole script and silently skip later checks (false-green).
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
  if [ "$got" = "$want" ]; then echo "✓ $name"; pass=$((pass + 1))
  else echo "✗ $name — expected [$want], got [$got]"; fail=$((fail + 1)); fi
}
check_contains() {
  local name="$1" haystack="$2" needle="$3"
  if [[ "$haystack" == *"$needle"* ]]; then echo "✓ $name"; pass=$((pass + 1))
  else echo "✗ $name — expected to find [$needle] in [$haystack]"; fail=$((fail + 1)); fi
}

workdir="$(mktemp -d --tmpdir bang-hostio-test-XXXXXX)"
trap 'rm -rf "$workdir"' EXIT

echo_main="examples/hostio-echo/main.bang"

# ── 1 · the SIM wedge runs (import Io + a `with Io_Console` sim handler) ──
got="$("$bang" run "$echo_main" 2>/dev/null)" && code=0 || code=$?
check "sim-wedge-stdout" "$got" "ih"
check "sim-wedge-exit"   "$code" "0"

# ── 2 · --allow name→label resolution: an unqualified name matches the qualified effect ──
got="$("$bang" run --env=real --allow=Console --record "$workdir/t1.ndjson" "$echo_main" 2>/dev/null)" && code=0 || code=$?
check "allow-console-unqualified-stdout" "$got" "ih"
check "allow-console-unqualified-exit"   "$code" "0"

# ── 3 · --allow LOUD error names the bad grant + the declared effects (ADR-0104 §2) ──
err="$("$bang" run --env=real --allow=Nonexistent "$echo_main" 2>&1 >/dev/null)" && code=0 || code=$?
check_contains "allow-bad-name-errors" "$err" "not a declared effect"
check_contains "allow-bad-name-lists-declared" "$err" "Io_Console"

# ── 4 · the RECORD→REPLAY driver path is TRANSPARENT (invariant-#1 at the driver level):
#        recording a run then replaying it reproduces the SAME output byte-for-byte. For the sim
#        wedge the trace is empty (the `with` handled every op), so this proves the driver leg
#        adds nothing — the necessary transparency the real-host trace will ride on. ──
"$bang" run --env=real --allow=Console --record "$workdir/t2.ndjson" "$echo_main" >/dev/null 2>&1 && rcode=0 || rcode=$?
replayed="$("$bang" run --replay "$workdir/t2.ndjson" "$echo_main" 2>/dev/null)" && pcode=0 || pcode=$?
recorded="$("$bang" run "$echo_main" 2>/dev/null)" && ocode=0 || ocode=$?
check "record-succeeds"        "$rcode" "0"
check "replay-reproduces-run"  "$replayed" "$recorded"
check "replay-exit"            "$pcode" "0"

# ── 5 · --max-host-requests is accepted (the O(n²) ceiling flag exists + parses; ADR-0104 §4) ──
got="$("$bang" run --env=real --allow=Console --max-host-requests 8 "$echo_main" 2>/dev/null)" && code=0 || code=$?
check "max-host-requests-accepted-stdout" "$got" "ih"
check "max-host-requests-accepted-exit"   "$code" "0"

# ── 6 · THE H1 REACH (#126) — the ambient `Io.print`/`Io.readLine` spelling, which sections 1-5
#        above never exercise (hostio-echo's own `with Io_Console` catches every op lexically, so
#        it never reaches the driver even under --env=real, measured). ambient.bang has NO `with` —
#        it can ONLY resolve via the driver's grant surface. This is the FIRST leg of this battery
#        that touches a REAL host boundary end-to-end (real stdin → the program's own $reverse). ──
ambient_main="examples/hostio-echo/ambient.bang"

# 6a · no --env at all ⟹ the DEFINED escapedCap terminal (ADR-0063), not silently swallowed —
#      pins the "mechanism ready, driver-gated" contract this file's header now documents.
err="$("$bang" run "$ambient_main" 2>&1 >/dev/null)" && code=0 || code=$?
check "ambient-no-env-nonzero-exit" "$code" "5"
check_contains "ambient-no-env-names-the-collapse" "$err" "escaped-capability"

# 6b · --env=real --allow=Console with REAL stdin ⟹ the driver services `Io.print`/`Io.readLine`
#      for REAL: the printed "?" prompt, the ECHOED real stdin line, and the reversed line all come
#      from the actual host boundary (Lean's `IO.println`/stdin), not a sim clause.
got="$(printf 'hi\n' | "$bang" run --env=real --allow=Console "$ambient_main" 2>/dev/null)" && code=0 || code=$?
check "ambient-real-env-stdout" "$got" "$(printf '?\nhi\nih')"
check "ambient-real-env-exit"   "$code" "0"

# 6c · a DIFFERENT real stdin line reverses differently — proves 6b wasn't a coincidental match
#      against a hardcoded expectation (the same structural distinctness `check-examples.sh`'s own
#      byte-diff relies on, applied here since ambient.bang isn't in that corpus loop).
got="$(printf 'go\n' | "$bang" run --env=real --allow=Console "$ambient_main" 2>/dev/null)" && code=0 || code=$?
check "ambient-real-env-different-input" "$got" "$(printf '?\ngo\nog')"

# 6d · record → replay is transparent for the AMBIENT path too (invariant-#1 at the driver level,
#      now proven over a run that touched REAL IO, not just the sim-transparent case sections 1-5
#      covered). REPLAY does NO real IO (the pure oracle, `--replay`'s whole point) — `Io.print`'s
#      `Unit` results and `Io.readLine`'s recorded `hi` are fed back from the trace, so ONLY the
#      program's RETURN value (`ih`, the reversed line) prints; the "?"/"hi" lines 6b saw were the
#      REAL handler's own `IO.println`/echo side effects, absent on replay by construction — this
#      is the invariant-#1 CONTRACT (replay reproduces the program's observable OUTPUT, not the
#      world's side effects, host-io-design.md §3 "honest limits"), not a gap in this leg.
printf 'hi\n' | "$bang" run --env=real --allow=Console --record "$workdir/ambient.ndjson" "$ambient_main" >/dev/null 2>&1 && rcode=0 || rcode=$?
replayed="$("$bang" run --replay "$workdir/ambient.ndjson" "$ambient_main" 2>/dev/null)" && pcode=0 || pcode=$?
check "ambient-record-succeeds"       "$rcode" "0"
check "ambient-replay-reproduces-run" "$replayed" "ih"
check "ambient-replay-exit"           "$pcode" "0"

echo "──────────────────────────────"
echo "hostio: $pass passed, $fail failed"
[ "$fail" -eq 0 ]
