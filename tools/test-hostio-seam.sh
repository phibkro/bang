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

expect_replay_failure() {
  local name="$1" trace="$2" program="$3" needle="$4" cwd="$5" err code
  err="$(cd "$cwd" && "$bang_abs" run --replay "$trace" "$program" 2>&1 >/dev/null)" && code=0 || code=$?
  check "$name-exit" "$code" "7"
  check_contains "$name-error" "$err" "$needle"
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
check "reference-run-exit"     "$ocode" "0"

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

# ── 7 · THE Fs WIDENING (ADR-0104 §Scope "next" tier, hostio-widen lane) — real filesystem
#        write/read/exists + grant + refusal + the record/replay round-trip WITHOUT the file
#        present. This is the FIRST leg to touch the real FILESYSTEM boundary end-to-end (sections
#        1-6 are Console/Clock). ambient.bang uses a RELATIVE path (`g.t`), so we run it INSIDE a
#        fresh jail (cwd = the jail) — the file lands there and the trap-rm'd $workdir cleans it. ──
repo="$(git rev-parse --show-toplevel)"
fs_ambient="$repo/examples/hostio-fs/ambient.bang"
fs_jail="$(mktemp -d --tmpdir bang-hostio-fs-XXXXXX)"
trap 'rm -rf "$workdir" "$fs_jail"' EXIT
bang_abs="$repo/$bang"

# 7a · no --env ⟹ the DEFINED escapedCap terminal (exit 5), same contract as the Console ambient path.
err="$(cd "$fs_jail" && "$bang_abs" run "$fs_ambient" 2>&1 >/dev/null)" && code=0 || code=$?
check "fs-no-env-nonzero-exit" "$code" "5"
check_contains "fs-no-env-names-the-collapse" "$err" "escaped-capability"

# 7b · an ungranted label refusal: --env=real WITHOUT Fs in --allow ⟹ the Fs perform still escapes
#      (exit 5). Proves --allow is deny-by-default per label (row-attenuation), not all-or-nothing.
err="$(cd "$fs_jail" && "$bang_abs" run --env=real --allow=Console "$fs_ambient" 2>&1 >/dev/null)" && code=0 || code=$?
check "fs-ungranted-label-refused-exit" "$code" "5"

# 7c · --allow=Fs bad-name resolution still errors loud (an unqualified Fs resolves to Io_Fs; a
#      typo does not). Confirms the name→label map sees the new effect.
got="$(cd "$fs_jail" && "$bang_abs" run --env=real --allow=Fs "$fs_ambient" 2>/dev/null)" && code=0 || code=$?
check "fs-real-write-read-stdout" "$got" "hi"
check "fs-real-write-read-exit"   "$code" "0"
# the file was ACTUALLY written to the jail (not a sim) — the real IO boundary, observed on disk.
check "fs-real-file-on-disk" "$(cat "$fs_jail/g.t" 2>/dev/null)" "hi"

# 7d · THE RECORD → REPLAY ROUND-TRIP over a REAL filesystem (the heart of the slice, ADR-0104 §3).
#      Record a real run, DELETE the file, then replay: byte-identical output WITHOUT the file on
#      disk ⇒ the tested-stratum host handler conforms to the pure oracle (invariant #1). Replay
#      does NO real IO, so the deleted file stays absent — the recorded readFile result is fed back.
(cd "$fs_jail" && "$bang_abs" run --env=real --allow=Fs --record "$fs_jail/fs.ndjson" "$fs_ambient" >/dev/null 2>&1) && rcode=0 || rcode=$?
check "fs-record-succeeds" "$rcode" "0"
rm -f "$fs_jail/g.t"
replayed="$(cd "$fs_jail" && "$bang_abs" run --replay "$fs_jail/fs.ndjson" "$fs_ambient" 2>/dev/null)" && pcode=0 || pcode=$?
check "fs-replay-reproduces-run" "$replayed" "hi"
check "fs-replay-exit"           "$pcode" "0"
check "fs-replay-did-no-real-io" "$( [ -e "$fs_jail/g.t" ] && echo present || echo absent )" "absent"

# 7e · the trace's three rows record the real (label,op,payload,result) sequence (writeFile→() ,
#      exists→1, readFile→hi) — the Sendable ordered log the replay rides. Confirms all three ops
#      recorded (not just readFile) and the (path,body) PAIR payload serialized.
tracelines="$(grep -c '"op"' "$fs_jail/fs.ndjson")" && code=0 || code=$?
check "fs-trace-three-rows" "$tracelines" "3"
check_contains "fs-trace-writefile-pair-payload" "$(cat "$fs_jail/fs.ndjson")" '"op":"writeFile","payload":"(g.t, hi)"'

# 7f · JSON-escape robustness — a file body carrying a `"` and a NEWLINE round-trips faithfully
#      (the un-escaped `takeWhile != '"'` loader would TRUNCATE at the quote and the newline would
#      split the row — a silent record/replay divergence, the exact false-green invariant #1 forbids).
cat > "$fs_jail/quote.bang" <<'BANG'
import Io
let main =
  let path = SCons(Char(102), SNil) in
  let body = SCons(Char(97), SCons(Char(34), SCons(Char(98), SCons(Char(10), SCons(Char(99), SNil))))) in
  let u1 = Io.writeFile((path, body)) in
  let back = Io.readFile(path) in
  back
BANG
real_out="$(cd "$fs_jail" && "$bang_abs" run --env=real --allow=Fs --record "$fs_jail/q.ndjson" "$fs_jail/quote.bang" 2>/dev/null)" && code=0 || code=$?
rm -f "$fs_jail/f"
replay_out="$(cd "$fs_jail" && "$bang_abs" run --replay "$fs_jail/q.ndjson" "$fs_jail/quote.bang" 2>/dev/null)" && code=0 || code=$?
check "fs-escaped-body-round-trips" "$replay_out" "$real_out"
# the recorded trace stayed ONE line per row (the newline inside the value did NOT split it).
check "fs-escaped-trace-one-row-per-op" "$(grep -c '"op"' "$fs_jail/q.ndjson")" "2"

# ── 8 · STRICT REPLAY VALIDATION (#164) — falsify every request field and both directions of
#        trace-length drift. Every replay fails BEFORE any real host IO; the final disk assertion makes
#        that purity observable for the first `writeFile` request. Each fixture is derived from the known-
#        good three-row trace above so only the named dimension changes. ──
sed '1s/"label":[0-9][0-9]*/"label":999999/' "$fs_jail/fs.ndjson" > "$fs_jail/bad-label.ndjson"
expect_replay_failure "replay-label-mismatch" "$fs_jail/bad-label.ndjson" "$fs_ambient" "label mismatch" "$fs_jail"

sed '1s/"op":"writeFile"/"op":"readFile"/' "$fs_jail/fs.ndjson" > "$fs_jail/bad-op.ndjson"
expect_replay_failure "replay-op-mismatch" "$fs_jail/bad-op.ndjson" "$fs_ambient" "op mismatch" "$fs_jail"

sed '1s/(g.t, hi)/(g.t, bye)/' "$fs_jail/fs.ndjson" > "$fs_jail/bad-payload.ndjson"
expect_replay_failure "replay-payload-mismatch" "$fs_jail/bad-payload.ndjson" "$fs_ambient" "payload mismatch" "$fs_jail"

printf '{not valid json}\n' > "$fs_jail/invalid.ndjson"
expect_replay_failure "replay-invalid-json" "$fs_jail/invalid.ndjson" "$fs_ambient" "invalid replay trace row 1" "$fs_jail"

sed '$d' "$fs_jail/fs.ndjson" > "$fs_jail/missing-row.ndjson"
expect_replay_failure "replay-missing-row" "$fs_jail/missing-row.ndjson" "$fs_ambient" "trace exhausted" "$fs_jail"

cp "$fs_jail/fs.ndjson" "$fs_jail/extra-row.ndjson"
sed -n '1p' "$fs_jail/fs.ndjson" >> "$fs_jail/extra-row.ndjson"
expect_replay_failure "replay-extra-row" "$fs_jail/extra-row.ndjson" "$fs_ambient" "unconsumed extra row" "$fs_jail"

check "strict-replay-did-no-real-io" "$( [ -e "$fs_jail/g.t" ] && echo present || echo absent )" "absent"
check "strict-replay-left-repo-root-clean" "$( [ -e "$repo/g.t" ] && echo present || echo absent )" "absent"

echo "──────────────────────────────"
echo "hostio: $pass passed, $fail failed"
expected=48
if [ "$pass" -ne "$expected" ]; then
  echo "✗ hostio-check-count — expected $expected completed checks, got $pass"
  fail=$((fail + 1))
fi
[ "$pass" -eq "$expected" ] && [ "$fail" -eq 0 ]
