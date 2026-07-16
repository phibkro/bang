#!/usr/bin/env bash
# tool: role=test couples=Main.lean,std/Io.bang runs-in=verify
source "$(git rev-parse --show-toplevel 2>/dev/null)/tools/tool-log.sh" 2>/dev/null && tool_log "$(basename "$0")" || true
# #169: explicit real-host authority, trusted bundled-service identity, and Fs root containment.
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"
bang="$PWD/.lake/build/bin/bang"
if [ -z "${BANG_BIN_FRESH:-}" ]; then lake build bang >/dev/null; fi

tmp="$(mktemp -d --tmpdir bang-host-authority-XXXXXX)"
trap 'rm -rf "$tmp"' EXIT
mkdir -p "$tmp/root" "$tmp/root2" "$tmp/outside"
printf 'outside-original\n' >"$tmp/outside/sentinel"
printf 'read-one\n' >"$tmp/root/read.txt"
printf 'read-two\n' >"$tmp/root2/read.txt"

pass=0 fail=0
ok() { echo "✓ $1"; pass=$((pass + 1)); }
bad() { echo "✗ $1 — $2"; fail=$((fail + 1)); }
eq() { if [ "$2" = "$3" ]; then ok "$1"; else bad "$1" "expected [$3], got [$2]"; fi; }
contains() { if [[ "$2" == *"$3"* ]]; then ok "$1"; else bad "$1" "expected [$3] in [$2]"; fi; }
not_contains() { if [[ "$2" != *"$3"* ]]; then ok "$1"; else bad "$1" "unexpected [$3] in [$2]"; fi; }
integer() { if [[ "$2" =~ ^[0-9]+$ ]]; then ok "$1"; else bad "$1" "expected a nonnegative integer, got [$2]"; fi; }

run_capture() {
  stdout='' stderr='' status=0
  "$@" >"$tmp/stdout" 2>"$tmp/stderr" || status=$?
  stdout="$(cat "$tmp/stdout")"
  stderr="$(cat "$tmp/stderr")"
}

write_prog="$tmp/write.bang"
read_prog="$tmp/read.bang"
exists_prog="$tmp/exists.bang"
clock_prog="$tmp/clock.bang"
cat >"$clock_prog" <<'BANG'
import Io
let main = Io.now(())
BANG
make_write_prog() {
  cat >"$write_prog" <<BANG
import Io
let main =
  let u = Io.writeFile(("$1", "changed")) in
  1
BANG
}
make_read_prog() {
  cat >"$read_prog" <<BANG
import Io
let main = Io.readFile("$1")
BANG
}
make_exists_prog() {
  cat >"$exists_prog" <<BANG
import Io
let main = Io.exists("$1")
BANG
}

# Typed grammar: real mode is default-deny, replay accepts no authority flags, and `all` is exact.
missing="$tmp/never-read.bang"
run_capture "$bang" run --env=real "$missing"
eq real-omission-exit "$status" 1
contains real-omission-migration "$stderr" "omitting --allow no longer grants"
eq real-omission-no-source-read "$(test ! -e "$missing" && echo absent)" absent

printf '\n' >"$tmp/empty.ndjson"
run_capture "$bang" run --replay "$tmp/empty.ndjson" --allow=Console "$clock_prog"
eq replay-rejects-effect-authority-exit "$status" 1
contains replay-rejects-effect-authority "$stderr" "not valid with '--replay'"
run_capture "$bang" run --replay "$tmp/empty.ndjson" --allow-fs-read "$tmp/root" "$clock_prog"
eq replay-rejects-path-authority-exit "$status" 1
contains replay-rejects-path-authority "$stderr" "filesystem root grants require '--env=real'"
run_capture "$bang" run --env=real --allow=Console,all "$clock_prog"
eq mixed-all-exit "$status" 1
contains mixed-all-diagnostic "$stderr" "'all' must be the only grant"
run_capture "$bang" run --env=real --allow=all --allow-fs-read "$tmp/root" "$clock_prog"
eq all-root-conflict-exit "$status" 1
contains all-root-conflict "$stderr" "already grants unrestricted filesystem access"

# Effect-level attenuation surfaces precise denial before the corresponding Console/Clock/Fs IO.
run_capture "$bang" run --env=real --allow=Clock examples/hostio-echo/ambient.bang
eq console-ungranted-exit "$status" 7
contains console-ungranted-diagnostic "$stderr" "console is not granted"
eq console-ungranted-stdout "$stdout" ""
run_capture "$bang" run --env=real --allow=Console "$clock_prog"
eq clock-ungranted-exit "$status" 7
contains clock-ungranted-diagnostic "$stderr" "clock is not granted"
run_capture "$bang" run --env=real --allow=Clock "$clock_prog"
eq import-io-clock-granted-exit "$status" 0
integer import-io-clock-granted-result "$stdout"
make_write_prog "$tmp/outside/ungranted.txt"
run_capture "$bang" run --env=real --allow=Console --allow-fs-write "$tmp/outside" "$write_prog"
eq fs-ungranted-exit "$status" 1
contains fs-ungranted-diagnostic "$stderr" "path authority never implies the Fs effect label"
eq fs-ungranted-no-write "$(test ! -e "$tmp/outside/ungranted.txt" && echo absent)" absent

# Root grants are repeatable, CWD-bound directories, and split by operation (`exists` is read).
make_write_prog "$tmp/root/write-ok.txt"
run_capture "$bang" run --env=real --allow=Fs --allow-fs-write "$tmp/root" "$write_prog"
eq write-root-success-exit "$status" 0
eq write-root-success-bytes "$(cat "$tmp/root/write-ok.txt")" changed
make_read_prog "$tmp/root/read.txt"
run_capture "$bang" run --env=real --allow=Fs --allow-fs-read "$tmp/root" "$read_prog"
eq read-root-success-exit "$status" 0
eq read-root-success-output "$stdout" read-one
make_write_prog "$tmp/root/read-only-denied.txt"
run_capture "$bang" run --env=real --allow=Fs --allow-fs-read "$tmp/root" "$write_prog"
eq write-needs-write-axis-exit "$status" 7
contains write-needs-write-axis "$stderr" "has no path authority"
eq write-needs-write-axis-no-file "$(test ! -e "$tmp/root/read-only-denied.txt" && echo absent)" absent
make_exists_prog "$tmp/root/read.txt"
run_capture "$bang" run --env=real --allow=Fs --allow-fs-write "$tmp/root" "$exists_prog"
eq exists-needs-read-axis-exit "$status" 7
contains exists-needs-read-axis "$stderr" "--allow-fs-read"
make_read_prog "$tmp/root2/read.txt"
run_capture "$bang" run --env=real --allow=Fs \
  --allow-fs-read "$tmp/root" --allow-fs-read "$tmp/root2" "$read_prog"
eq root-union-exit "$status" 0
eq root-union-selects-second "$stdout" read-two

make_write_prog "root/cwd-bound.txt"
(cd "$tmp" && "$bang" run --env=real --allow=Fs --allow-fs-write root "$write_prog" \
  >"$tmp/stdout" 2>"$tmp/stderr") && status=0 || status=$?
eq relative-root-binds-cwd-exit "$status" 0
eq relative-root-binds-cwd "$(cat "$tmp/root/cwd-bound.txt")" changed

# Canonical containment: parent traversal, absolute/prefix escapes, final and intermediate links,
# and missing parents are denied without modifying targets or manufacturing directories.
make_write_prog "../outside/traversal.txt"
(cd "$tmp/root" && "$bang" run --env=real --allow=Fs --allow-fs-write . "$write_prog" \
  >"$tmp/stdout" 2>"$tmp/stderr") && status=0 || status=$?
stderr="$(cat "$tmp/stderr")"
eq traversal-exit "$status" 7
contains traversal-diagnostic "$stderr" "outside its granted roots"
eq traversal-no-write "$(test ! -e "$tmp/outside/traversal.txt" && echo absent)" absent
make_write_prog "$tmp/outside/absolute.txt"
run_capture "$bang" run --env=real --allow=Fs --allow-fs-write "$tmp/root" "$write_prog"
eq absolute-escape-exit "$status" 7
eq absolute-escape-no-write "$(test ! -e "$tmp/outside/absolute.txt" && echo absent)" absent
make_write_prog "$tmp/root2/prefix.txt"
run_capture "$bang" run --env=real --allow=Fs --allow-fs-write "$tmp/root" "$write_prog"
eq prefix-collision-exit "$status" 7
eq prefix-collision-no-write "$(test ! -e "$tmp/root2/prefix.txt" && echo absent)" absent

ln -s "$tmp/outside/sentinel" "$tmp/root/live-link"
make_write_prog "$tmp/root/live-link"
run_capture "$bang" run --env=real --allow=Fs --allow-fs-write "$tmp/root" "$write_prog"
eq live-final-link-exit "$status" 7
contains live-final-link-diagnostic "$stderr" "refuses final symlink"
eq live-final-link-target-preserved "$(cat "$tmp/outside/sentinel")" outside-original
ln -s "$tmp/outside/missing" "$tmp/root/dangling-link"
make_write_prog "$tmp/root/dangling-link"
run_capture "$bang" run --env=real --allow=Fs --allow-fs-write "$tmp/root" "$write_prog"
eq dangling-final-link-exit "$status" 7
contains dangling-final-link-diagnostic "$stderr" "refuses final symlink"
eq dangling-final-link-preserved "$(test -L "$tmp/root/dangling-link" && echo present)" present
ln -s "$tmp/outside" "$tmp/root/intermediate"
make_write_prog "$tmp/root/intermediate/linked.txt"
run_capture "$bang" run --env=real --allow=Fs --allow-fs-write "$tmp/root" "$write_prog"
eq intermediate-link-exit "$status" 7
contains intermediate-link-diagnostic "$stderr" "outside its granted roots"
eq intermediate-link-no-write "$(test ! -e "$tmp/outside/linked.txt" && echo absent)" absent
make_write_prog "$tmp/root/missing/child.txt"
run_capture "$bang" run --env=real --allow=Fs --allow-fs-write "$tmp/root" "$write_prog"
eq missing-parent-exit "$status" 7
contains missing-parent-diagnostic "$stderr" "no resolvable existing parent"
eq missing-parent-not-created "$(test ! -e "$tmp/root/missing" && echo absent)" absent

# Exact all is the explicit unrestricted policy. Rootless named Fs remains denied.
make_write_prog "$tmp/outside/all.txt"
run_capture "$bang" run --env=real --allow=all "$write_prog"
eq explicit-all-exit "$status" 0
eq explicit-all-unrestricted "$(cat "$tmp/outside/all.txt")" changed
make_write_prog "$tmp/outside/no-root.txt"
run_capture "$bang" run --env=real --allow=Fs "$write_prog"
eq named-fs-no-root-exit "$status" 7
eq named-fs-no-root-no-write "$(test ! -e "$tmp/outside/no-root.txt" && echo absent)" absent
make_write_prog "$tmp/outside/slash-root.txt"
run_capture "$bang" run --env=real --allow=Fs --allow-fs-write / "$write_prog"
eq filesystem-root-directory-exit "$status" 0
eq filesystem-root-directory-write "$(cat "$tmp/outside/slash-root.txt")" changed

# Trusted identity comes only from bundled Io provenance, not flattened/tail names or matching ops.
cat >"$tmp/untrusted-flat.bang" <<'BANG'
effect Io_Clock { now : Unit -> Int }
let main = 1
BANG
run_capture "$bang" run --env=real --allow=Io_Clock "$tmp/untrusted-flat.bang"
eq untrusted-flat-exit "$status" 1
contains untrusted-flat-diagnostic "$stderr" "did not originate in the resolver-owned bundled"
cat >"$tmp/untrusted-bare.bang" <<'BANG'
effect Clock { now : Unit -> Int }
let main = 1
BANG
run_capture "$bang" run --env=real --allow=Clock "$tmp/untrusted-bare.bang"
eq untrusted-bare-exit "$status" 1
contains untrusted-bare-diagnostic "$stderr" "did not originate in the resolver-owned bundled"

cat >"$tmp/Fake.bang" <<'BANG'
pub effect Console { print : Str -> Unit }
pub effect Clock { now : Unit -> Int }
pub effect Fs { writeFile : Str * Str -> Unit }
BANG
cat >"$tmp/fake-print.bang" <<'BANG'
import Fake
let main = Fake.print("must-not-print")
BANG
run_capture "$bang" run --env=real --allow=all "$tmp/fake-print.bang"
eq fake-console-exit "$status" 5
eq fake-console-no-output "$stdout" ""
cat >"$tmp/fake-clock.bang" <<'BANG'
import Fake
let main = Fake.now(())
BANG
run_capture "$bang" run --env=real --allow=all "$tmp/fake-clock.bang"
eq fake-clock-exit "$status" 5
make_write_prog "$tmp/outside/fake-fs.txt"
sed 's/import Io/import Fake/; s/Io.writeFile/Fake.writeFile/' "$write_prog" >"$tmp/fake-fs.bang"
run_capture "$bang" run --env=real --allow=all "$tmp/fake-fs.bang"
eq fake-fs-exit "$status" 5
eq fake-fs-no-write "$(test ! -e "$tmp/outside/fake-fs.txt" && echo absent)" absent

cat >"$tmp/use-clock.bang" <<'BANG'
use Io (Clock)
let main =
  let leaked = handle ({ logger.now(()) }) with Clock as logger { now(u) => 0 } in
  $leaked
BANG
run_capture "$bang" run --env=real --allow=Clock "$tmp/use-clock.bang"
eq use-io-clock-capability-exit "$status" 0
integer use-io-clock-capability-result "$stdout"
not_contains use-io-clock-trusted-by-resolver "$stderr" "did not originate in the resolver-owned bundled"

# A denied service publishes no partial record; success publishes one complete trace and no temp.
failed_record="$tmp/outside/failed.ndjson"
run_capture "$bang" run --env=real --allow=Clock --record "$failed_record" examples/hostio-echo/ambient.bang
eq denied-record-exit "$status" 7
eq denied-record-absent "$(test ! -e "$failed_record" && echo absent)" absent
make_write_prog "$tmp/root/recorded.txt"
record="$tmp/outside/success.ndjson"
run_capture "$bang" run --env=real --allow=Fs --allow-fs-write "$tmp/root" --record "$record" "$write_prog"
eq successful-record-exit "$status" 0
contains successful-record-complete "$(cat "$record")" '"op":"writeFile"'
eq successful-record-no-temp "$(find "$tmp/outside" -maxdepth 1 -name '.*.bang-record-*' -print -quit)" ""

echo "──────────────────────────────"
expected=76
if [ "$pass" -ne "$expected" ]; then bad host-authority-check-count "expected $expected completed checks, got $pass"; fi
echo "host-authority: $pass passed, $fail failed"
[ "$pass" -eq "$expected" ] && [ "$fail" -eq 0 ]
