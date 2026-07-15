#!/usr/bin/env bash
# tool: role=test couples=onboarding-preflight.sh runs-in=fitness
# Known-good/known-bad poles for the read-only newcomer preflight.
set -euo pipefail

ROOT="$(git rev-parse --show-toplevel)"
PREFLIGHT="$ROOT/tools/onboarding-preflight.sh"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

ready="$TMP/ready"
git init -q "$ready"
git -C "$ready" config gc.auto 0
git -C "$ready" config gc.autoDetach false
mkdir -p "$ready/.lake/packages/mathlib/.lake/build" "$ready/.lake/build/bin"
cat >"$ready/.lake/build/bin/bang" <<'EOF'
#!/usr/bin/env bash
printf 'bang 0.2.0\n'
EOF
chmod +x "$ready/.lake/build/bin/bang"

output="$(IN_NIX_SHELL=impure bash "$PREFLIGHT" --repo "$ready")"
[[ "$output" == *"READY"* ]] || {
  printf 'FAIL: ready fixture was not reported ready\n%s\n' "$output" >&2
  exit 1
}
ready_json="$(IN_NIX_SHELL=impure bash "$PREFLIGHT" --json --repo "$ready")"
python3 - "$ready_json" <<'PY'
import json
import sys

report = json.loads(sys.argv[1])
assert report["state"] == "ready"
assert report["ready"] is True
assert report["missing"] == []
assert report["linkedWorktree"] is False
assert report["inDevShell"] is True
assert report["cachePresent"] is True
assert report["runnerPresent"] is True
assert report["gitHygiene"] is True
PY

cold="$TMP/cold"
git init -q "$cold"
before_status="$(git -C "$cold" status --porcelain=v1)"
before_config="$(git -C "$cold" config --local --list)"
set +e
cold_output="$(IN_NIX_SHELL=impure bash "$PREFLIGHT" --repo "$cold" 2>&1)"
cold_code=$?
set -e
[[ "$cold_code" -eq 1 ]] || {
  printf 'FAIL: cold fixture exited %s, expected 1\n%s\n' "$cold_code" "$cold_output" >&2
  exit 1
}
[[ "$cold_output" == *"COLD / NOT READY"* && "$cold_output" == *"just setup"* && "$cold_output" == *"serially"* ]] || {
  printf 'FAIL: cold fixture guidance is incomplete\n%s\n' "$cold_output" >&2
  exit 1
}
[[ "$(git -C "$cold" status --porcelain=v1)" == "$before_status" ]] || {
  printf 'FAIL: preflight changed the cold worktree\n' >&2
  exit 1
}
[[ "$(git -C "$cold" config --local --list)" == "$before_config" ]] || {
  printf 'FAIL: preflight changed cold Git configuration\n' >&2
  exit 1
}
set +e
cold_json="$(IN_NIX_SHELL=impure BANG_PREFLIGHT_NIX="$TMP/missing-nix" bash "$PREFLIGHT" --json --repo "$cold" 2>&1)"
cold_json_code=$?
set -e
[[ "$cold_json_code" -eq 1 ]] || {
  printf 'FAIL: degraded JSON fixture exited %s, expected 1\n%s\n' "$cold_json_code" "$cold_json" >&2
  exit 1
}
python3 - "$cold_json" <<'PY'
import json
import sys

report = json.loads(sys.argv[1])
assert report["state"] == "cold-not-ready"
assert report["ready"] is False
assert report["nixPresent"] is False
assert "nix" in report["missing"]
PY

set +e
error_json="$(bash "$PREFLIGHT" --json --repo "$TMP/not-a-repo" 2>&1)"
error_code=$?
set -e
[[ "$error_code" -eq 2 ]] || {
  printf 'FAIL: invalid repository exited %s, expected 2\n%s\n' "$error_code" "$error_json" >&2
  exit 1
}
python3 - "$error_json" <<'PY'
import json
import sys

report = json.loads(sys.argv[1])
assert report["state"] == "error"
assert report["ready"] is False
PY

worktree_source="$TMP/worktree-source"
linked="$TMP/linked"
git init -q "$worktree_source"
git -C "$worktree_source" config user.name preflight-test
git -C "$worktree_source" config user.email preflight@example.test
git -C "$worktree_source" config gc.auto 0
git -C "$worktree_source" config gc.autoDetach false
git -C "$worktree_source" commit --allow-empty -qm initial
git -C "$worktree_source" worktree add -qb linked "$linked"
mkdir -p "$linked/.lake/packages/mathlib/.lake/build" "$linked/.lake/build/bin"
cp "$ready/.lake/build/bin/bang" "$linked/.lake/build/bin/bang"
linked_json="$(IN_NIX_SHELL=impure bash "$PREFLIGHT" --json --repo "$linked")"
python3 - "$linked_json" <<'PY'
import json
import sys

report = json.loads(sys.argv[1])
assert report["state"] == "ready"
assert report["linkedWorktree"] is True
PY

echo 'test-onboarding-preflight: PASS — ready, cold, degraded, linked, error, and non-mutation poles hold.'
