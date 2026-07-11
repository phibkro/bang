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
# SCOPE NOTE (ADR-0104 §4, the open host-provision reach): a v1 program installs its OWN `with
# Io_* {…}` sim handler, which catches every host op lexically — so the HOST seam (the outermost
# fallback) is not reached by a normal program yet; that needs the module-qualified-host-perform
# surface affordance (the named next, cross-lane slice). Until then the REAL-host + non-trivial
# trace legs live in the #guards (which exercise the seam directly on Comp AST); this file gates
# the driver's SIM-path transparency + flag surface, which IS reachable today.
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

echo "──────────────────────────────"
echo "hostio: $pass passed, $fail failed"
[ "$fail" -eq 0 ]
