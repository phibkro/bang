#!/usr/bin/env bash
# tool: role=test couples=onboarding-preflight.sh runs-in=fitness
# Known-good/known-bad poles for the read-only newcomer preflight.
set -euo pipefail

ROOT="$(git rev-parse --show-toplevel)"
PREFLIGHT="$ROOT/tools/onboarding-preflight.sh"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

seed_identity() {
  local repo="$1" anchor
  for anchor in lakefile.toml lean-toolchain justfile Bang/Spec.lean tools/setup.sh; do
    mkdir -p "$repo/$(dirname "$anchor")"
    printf 'fixture\n' >"$repo/$anchor"
  done
  git -C "$repo" add lakefile.toml lean-toolchain justfile Bang/Spec.lean tools/setup.sh
}

seed_artifacts() {
  local repo="$1"
  mkdir -p "$repo/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" "$repo/.lake/build/bin"
  printf 'olean fixture\n' >"$repo/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Init.olean"
  cat >"$repo/.lake/build/bin/bang" <<'EOF'
#!/usr/bin/env bash
printf 'bang 0.2.0\n'
EOF
  chmod +x "$repo/.lake/build/bin/bang"
}

ready="$TMP/ready"
git init -q "$ready"
git -C "$ready" config gc.auto 0
git -C "$ready" config gc.autoDetach false
seed_identity "$ready"
seed_artifacts "$ready"

output="$(IN_NIX_SHELL=impure BANG_PREFLIGHT_MIN_RUNNER_BYTES=1 bash "$PREFLIGHT" --repo "$ready")"
[[ "$output" == *"READY"* ]] || {
  printf 'FAIL: ready fixture was not reported ready\n%s\n' "$output" >&2
  exit 1
}
ready_json="$(IN_NIX_SHELL=impure BANG_PREFLIGHT_MIN_RUNNER_BYTES=1 bash "$PREFLIGHT" --json --repo "$ready")"
python3 - "$ready_json" <<'PY'
import json
import sys

report = json.loads(sys.argv[1])
assert report["state"] == "ready"
assert report["ready"] is True
assert report["missing"] == []
assert report["linkedWorktree"] is False
assert report["checkoutIdentity"] is True
assert report["inDevShell"] is True
assert report["cachePresent"] is True
assert report["runnerPresent"] is True
assert report["gitHygiene"] is True
PY

unrelated="$TMP/unrelated"
git init -q "$unrelated"
git -C "$unrelated" config gc.auto 0
git -C "$unrelated" config gc.autoDetach false
seed_artifacts "$unrelated"
set +e
unrelated_json="$(IN_NIX_SHELL=impure BANG_PREFLIGHT_MIN_RUNNER_BYTES=1 bash "$PREFLIGHT" --json --repo "$unrelated")"
unrelated_code=$?
set -e
[[ "$unrelated_code" -eq 1 ]] || {
  printf 'FAIL: unrelated checkout exited %s, expected 1\n%s\n' "$unrelated_code" "$unrelated_json" >&2
  exit 1
}
python3 - "$unrelated_json" <<'PY'
import json
import sys

report = json.loads(sys.argv[1])
assert report["state"] == "cold-not-ready"
assert report["checkoutIdentity"] is False
assert "BANG checkout identity" in report["missing"]
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

for args in '--json --bogus' '--json --repo'; do
  set +e
  # shellcheck disable=SC2086 # arguments intentionally exercise the public parser
  argument_json="$(bash "$PREFLIGHT" $args 2>&1)"
  argument_code=$?
  set -e
  [[ "$argument_code" -eq 2 ]] || {
    printf 'FAIL: argument error [%s] exited %s, expected 2\n%s\n' "$args" "$argument_code" "$argument_json" >&2
    exit 1
  }
  python3 - "$argument_json" <<'PY'
import json
import sys

report = json.loads(sys.argv[1])
assert report["state"] == "error"
assert report["ready"] is False
PY
done

worktree_source="$TMP/worktree-source"
linked="$TMP/linked"
git init -q "$worktree_source"
git -C "$worktree_source" config user.name preflight-test
git -C "$worktree_source" config user.email preflight@example.test
git -C "$worktree_source" config gc.auto 0
git -C "$worktree_source" config gc.autoDetach false
seed_identity "$worktree_source"
git -C "$worktree_source" commit -qm initial
git -C "$worktree_source" worktree add -qb linked "$linked"
seed_artifacts "$linked"
linked_json="$(IN_NIX_SHELL=impure BANG_PREFLIGHT_MIN_RUNNER_BYTES=1 bash "$PREFLIGHT" --json --repo "$linked")"
python3 - "$linked_json" <<'PY'
import json
import sys

report = json.loads(sys.argv[1])
assert report["state"] == "ready"
assert report["linkedWorktree"] is True
PY

echo 'test-onboarding-preflight: PASS — ready, cold, degraded, linked, error, and non-mutation poles hold.'
