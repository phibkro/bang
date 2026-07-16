#!/usr/bin/env bash
# tool: role=test couples=Main.lean,tools/lean-warnings.py,docfacts/lean-warning-budget.json,justfile runs-in=verify
# Falsification poles for the deterministic, reduction-friendly Lean warning budget.
source "$(git rev-parse --show-toplevel 2>/dev/null)/tools/tool-log.sh" 2>/dev/null && tool_log "$(basename "$0")" || true
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"

workdir="$(mktemp -d --tmpdir bang-lean-warnings-XXXXXX)"
trap 'rm -rf "$workdir"' EXIT
tool=(python3 tools/lean-warnings.py)
passed=0

pass() {
  passed=$((passed + 1))
  printf '  ✓ %s\n' "$1"
}

expect_status() {
  local name=$1 expected=$2
  shift 2
  set +e
  "$@" >"$workdir/stdout" 2>"$workdir/stderr"
  local status=$?
  set -e
  if [ "$status" -ne "$expected" ]; then
    printf 'FAIL: %s exited %s, expected %s\n' "$name" "$status" "$expected" >&2
    sed -n '1,120p' "$workdir/stdout" >&2
    sed -n '1,120p' "$workdir/stderr" >&2
    exit 1
  fi
  pass "$name"
}

expect_failure_text() {
  local name=$1 needle=$2
  shift 2
  expect_status "$name" 1 "$@"
  if ! grep -Fq -- "$needle" "$workdir/stderr"; then
    printf 'FAIL: %s did not report %s\n' "$name" "$needle" >&2
    sed -n '1,120p' "$workdir/stderr" >&2
    exit 1
  fi
}

cat >"$workdir/fake-build" <<'SH'
#!/usr/bin/env bash
set -u
cat "$1"
if [ "${FAKE_STDERR:-}" ]; then printf '%s' "$FAKE_STDERR" >&2; fi
exit "${2:-0}"
SH
chmod +x "$workdir/fake-build"

# The committed identity is portable across every flake system: the host
# triple is display metadata, while version, commit, and build flavor bind the
# actual compiler release.
python3 - <<'PY'
import importlib.util
from pathlib import Path

spec = importlib.util.spec_from_file_location("lean_warnings", Path("tools/lean-warnings.py"))
assert spec is not None and spec.loader is not None
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)

commit = "d024af099ca4bf2c86f649261ebf59565dc8c622"
versions = [
    f"Lean (version 4.30.0, x86_64-unknown-linux-gnu, commit {commit}, Release)",
    f"Lean (version 4.30.0, aarch64-apple-darwin, commit {commit}, Release)",
    f"Lean (version 4.30.0, x86_64-w64-windows-gnu, commit {commit}, Release)",
]
identities = [module.lean_release_identity(version) for version in versions]
assert identities == [identities[0]] * len(identities)
assert identities[0] == {
    "leanVersion": "4.30.0",
    "leanCommit": commit,
    "leanBuild": "Release",
}
PY
pass "toolchain release identity is independent of the host triple"

# The standing wrapper must explicitly request both the complete Bang library
# and native runner in one Lake invocation, avoiding a second cold build.
python3 - <<'PY'
import argparse
import importlib.util
from pathlib import Path

spec = importlib.util.spec_from_file_location("lean_warnings", Path("tools/lean-warnings.py"))
assert spec is not None and spec.loader is not None
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
assert module.command_from(argparse.Namespace(command=None)) == ["lake", "build", "Bang", "bang"]
PY
pass "default warning build includes the native bang runner"

"${tool[@]}" --help >"$workdir/help.out"
grep -Fq 'build command (default: lake build Bang bang)' "$workdir/help.out"
pass "help names the exact default warning build command"

# Same three warnings in deliberately different order, locations, ANSI display,
# and cold/replayed progress noise.  Their generated maps must be byte-identical.
printf '\033[1;33mwarning:\033[0m Bang/Fixture/A.lean:10:2: This simp argument is unused:\n' >"$workdir/good-a.log"
cat >>"$workdir/good-a.log" <<'LOG'
  alpha
warning: Bang/Fixture/B.lean:20:4: `old` has been deprecated: Use `new` instead
warning: Bang/Fixture/A.lean:30:6: This simp argument is unused:
  beta
Build completed successfully (cold jobs).
LOG

cat >"$workdir/good-b.log" <<'LOG'
⚠ [2/2] Replayed Bang.Fixture.B
warning: Bang/Fixture/A.lean:999:44: This simp argument is unused:
  beta
warning: Bang/Fixture/A.lean:1:1: This simp argument is unused:
  alpha
warning: Bang/Fixture/B.lean:77:9: `old` has been deprecated: Use `new` instead
Build completed successfully (cached jobs).
LOG

baseline_a="$workdir/baseline-a.json"
baseline_b="$workdir/baseline-b.json"
"${tool[@]}" update --baseline "$baseline_a" --command "$workdir/fake-build" "$workdir/good-a.log" \
  >"$workdir/update-a.out" 2>"$workdir/update-a.err"
"${tool[@]}" update --baseline "$baseline_b" --command "$workdir/fake-build" "$workdir/good-b.log" \
  >"$workdir/update-b.out" 2>"$workdir/update-b.err"
cmp "$baseline_a" "$baseline_b"
pass "deterministic update ignores order, line, color, and cache noise"

# A successful wrapper copies the child's stdout byte-for-byte; its own status
# report belongs on stderr.
"${tool[@]}" build --baseline "$baseline_a" --command "$workdir/fake-build" "$workdir/good-a.log" \
  >"$workdir/build.out" 2>"$workdir/build.err"
cmp "$workdir/good-a.log" "$workdir/build.out"
grep -Fq 'target remains zero' "$workdir/build.err"
pass "build stream is unmodified and the zero-warning target is explicit"

cat >"$workdir/reduction.log" <<'LOG'
warning: Bang/Fixture/A.lean:101:3: This simp argument is unused:
warning: Bang/Fixture/B.lean:202:4: `old` has been deprecated: Use `new` instead
LOG
expect_status "warning reductions pass without baseline edits" 0 \
  "${tool[@]}" check --baseline "$baseline_a" --input "$workdir/reduction.log"
grep -Fq '1 below the committed ceiling' "$workdir/stderr"

cat >"$workdir/increase.log" <<'LOG'
warning: Bang/Fixture/A.lean:1:1: This simp argument is unused:
warning: Bang/Fixture/A.lean:2:1: This simp argument is unused:
warning: Bang/Fixture/A.lean:3:1: This simp argument is unused:
warning: Bang/Fixture/B.lean:4:1: `old` has been deprecated: Use `new` instead
LOG
expect_failure_text "count increases fail" "count increase Bang.Fixture.A/unusedSimpArgs: 2 -> 3" \
  "${tool[@]}" check --baseline "$baseline_a" --input "$workdir/increase.log"

cat >"$workdir/new-module.log" <<'LOG'
warning: Bang/Fixture/A.lean:1:1: This simp argument is unused:
warning: Bang/Fixture/B.lean:2:1: `old` has been deprecated: Use `new` instead
warning: Bang/Fixture/C.lean:3:1: This simp argument is unused:
LOG
expect_failure_text "new modules fail" "new module Bang.Fixture.C" \
  "${tool[@]}" check --baseline "$baseline_a" --input "$workdir/new-module.log"

cat >"$workdir/runner-only.log" <<'LOG'
warning: Bang/Fixture/A.lean:1:1: This simp argument is unused:
warning: Bang/Fixture/A.lean:2:1: This simp argument is unused:
warning: Bang/Fixture/B.lean:3:1: `old` has been deprecated: Use `new` instead
warning: Main.lean:4:1: `oldRunnerApi` has been deprecated: Use `newRunnerApi` instead
LOG
expect_failure_text "runner-only warnings cannot escape" "new module Main" \
  "${tool[@]}" check --baseline "$baseline_a" --input "$workdir/runner-only.log"

cat >"$workdir/new-category.log" <<'LOG'
warning: Bang/Fixture/A.lean:1:1: This simp argument is unused:
warning: Bang/Fixture/A.lean:2:1: unused variable `x`
warning: Bang/Fixture/B.lean:3:1: `old` has been deprecated: Use `new` instead
LOG
expect_failure_text "new categories fail" "new category unusedVariables" \
  "${tool[@]}" check --baseline "$baseline_a" --input "$workdir/new-category.log"

cat >"$workdir/new-bucket.log" <<'LOG'
warning: Bang/Fixture/A.lean:1:1: This simp argument is unused:
warning: Bang/Fixture/A.lean:2:1: `old` has been deprecated: Use `new` instead
warning: Bang/Fixture/B.lean:3:1: `old` has been deprecated: Use `new` instead
LOG
expect_failure_text "new module/category buckets fail" "new bucket Bang.Fixture.A/deprecated" \
  "${tool[@]}" check --baseline "$baseline_a" --input "$workdir/new-bucket.log"

printf '{"schemaVersion":1,"schemaVersion":1}\n' >"$workdir/duplicate-key.json"
expect_failure_text "duplicate JSON keys fail" "duplicate JSON key: schemaVersion" \
  "${tool[@]}" check --baseline "$workdir/duplicate-key.json" --input "$workdir/reduction.log"

printf '{not json}\n' >"$workdir/malformed.json"
expect_failure_text "malformed JSON fails" "malformed warning baseline" \
  "${tool[@]}" check --baseline "$workdir/malformed.json" --input "$workdir/reduction.log"

python3 - "$baseline_a" "$workdir/duplicate-bucket.json" <<'PY'
import json, sys
with open(sys.argv[1], encoding="utf-8") as source:
    data = json.load(source)
data["buckets"].append(dict(data["buckets"][0]))
with open(sys.argv[2], "w", encoding="utf-8") as target:
    json.dump(data, target, indent=2, ensure_ascii=False)
    target.write("\n")
PY
expect_failure_text "duplicate warning buckets fail" "duplicate warning bucket" \
  "${tool[@]}" check --baseline "$workdir/duplicate-bucket.json" --input "$workdir/reduction.log"

python3 - "$baseline_a" "$workdir/wrong-toolchain.json" <<'PY'
import json, sys
with open(sys.argv[1], encoding="utf-8") as source:
    data = json.load(source)
data["toolchain"]["leanVersion"] = "Lean (wrong fixture version)"
with open(sys.argv[2], "w", encoding="utf-8") as target:
    json.dump(data, target, indent=2, ensure_ascii=False)
    target.write("\n")
PY
expect_failure_text "toolchain identity drift fails" "Lean toolchain mismatch" \
  "${tool[@]}" check --baseline "$workdir/wrong-toolchain.json" --input "$workdir/reduction.log"

python3 - "$baseline_a" "$workdir/invented-category.json" <<'PY'
import json, sys
with open(sys.argv[1], encoding="utf-8") as source:
    data = json.load(source)
data["buckets"][0]["category"] = "inventedCategory"
with open(sys.argv[2], "w", encoding="utf-8") as target:
    json.dump(data, target, indent=2, ensure_ascii=False)
    target.write("\n")
PY
expect_failure_text "invented baseline categories fail" "unknown category 'inventedCategory'" \
  "${tool[@]}" check --baseline "$workdir/invented-category.json" --input "$workdir/reduction.log"

cat >"$workdir/malformed-header.log" <<'LOG'
warning: Bang/Fixture/A.lean: This simp argument is unused:
LOG
expect_failure_text "changed project diagnostic layouts fail closed" "malformed project diagnostic header" \
  "${tool[@]}" check --baseline "$baseline_a" --input "$workdir/malformed-header.log"

# Located dependency diagnostics can be excluded safely. Any warning without a
# location cannot be attributed to project or dependency, so both read and
# write paths must reject it without touching the baseline.
cat >"$workdir/dependency.log" <<'LOG'
warning: .lake/packages/mathlib/Mathlib/Fixture.lean:1:1: This simp argument is unused:
LOG
expect_status "located dependency warnings stay excluded" 0 \
  "${tool[@]}" check --baseline "$baseline_a" --input "$workdir/dependency.log"

cat >"$workdir/headerless.log" <<'LOG'
warning: This simp argument is unused:
LOG
cp "$baseline_a" "$workdir/before-headerless.json"
expect_failure_text "locationless categorized warnings fail check" "locationless warning cannot be attributed" \
  "${tool[@]}" check --baseline "$baseline_a" --input "$workdir/headerless.log"
expect_failure_text "locationless categorized warnings block regeneration" "locationless warning cannot be attributed" \
  "${tool[@]}" update --baseline "$baseline_a" --command "$workdir/fake-build" "$workdir/headerless.log"
cmp "$baseline_a" "$workdir/before-headerless.json"
pass "locationless failure leaves the baseline unchanged"

cat >"$workdir/headerless-unknown.log" <<'LOG'
warning: an entirely new warning shape
LOG
expect_failure_text "new locationless warning shapes fail check" "locationless warning cannot be attributed" \
  "${tool[@]}" check --baseline "$baseline_a" --input "$workdir/headerless-unknown.log"
expect_failure_text "new locationless warning shapes block regeneration" "locationless warning cannot be attributed" \
  "${tool[@]}" update --baseline "$baseline_a" --command "$workdir/fake-build" "$workdir/headerless-unknown.log"
cmp "$baseline_a" "$workdir/before-headerless.json"
pass "new locationless shape leaves the baseline unchanged"

cp "$baseline_a" "$workdir/before-failure.json"
cat >"$workdir/unknown.log" <<'LOG'
warning: Bang/Fixture/A.lean:1:1: an entirely new warning shape
LOG
expect_failure_text "unknown warning shapes block regeneration" "unclassified project Lean warning" \
  "${tool[@]}" update --baseline "$baseline_a" --command "$workdir/fake-build" "$workdir/unknown.log"
cmp "$baseline_a" "$workdir/before-failure.json"
pass "unknown-shape failure leaves the baseline unchanged"

expect_status "child build status is preserved exactly" 23 \
  "${tool[@]}" build --baseline "$baseline_a" --command "$workdir/fake-build" "$workdir/good-a.log" 23
cmp "$workdir/good-a.log" "$workdir/stdout"

expect_status "failed build blocks regeneration with exact status" 19 \
  "${tool[@]}" update --baseline "$baseline_a" --command "$workdir/fake-build" "$workdir/reduction.log" 19
cmp "$baseline_a" "$workdir/before-failure.json"
pass "failed build leaves the baseline unchanged"

expect_status "SIGKILL child termination is preserved without a traceback" 137 \
  "${tool[@]}" build --baseline "$baseline_a" --command bash -c 'kill -KILL $$'
if grep -Fq 'Traceback' "$workdir/stderr"; then
  printf 'FAIL: SIGKILL propagation emitted a traceback\n' >&2
  sed -n '1,120p' "$workdir/stderr" >&2
  exit 1
fi

expect_status "catchable child signal termination is preserved" 143 \
  "${tool[@]}" build --baseline "$baseline_a" --command bash -c 'kill -TERM $$'
if grep -Fq 'Traceback' "$workdir/stderr"; then
  printf 'FAIL: SIGTERM propagation emitted a traceback\n' >&2
  sed -n '1,120p' "$workdir/stderr" >&2
  exit 1
fi

# Updating from a successful reduced build deterministically shrinks the ceiling.
reduced_baseline="$workdir/reduced.json"
"${tool[@]}" update --baseline "$reduced_baseline" --command "$workdir/fake-build" "$workdir/reduction.log" \
  >"$workdir/reduced.out" 2>"$workdir/reduced.err"
grep -Fq '"totalWarnings": 2' "$reduced_baseline"
expect_status "regenerated reductions remain green" 0 \
  "${tool[@]}" check --baseline "$reduced_baseline" --input "$workdir/reduction.log"

printf 'lean-warning-budget tests: %d checks passed.\n' "$passed"
