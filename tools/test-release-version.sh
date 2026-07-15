#!/usr/bin/env bash
# tool: role=test couples=check-release-version.sh runs-in=verify
# Known-good/known-bad poles for the exact release identity gate.
set -euo pipefail

ROOT="$(git rev-parse --show-toplevel)"
CHECK="$ROOT/tools/check-release-version.sh"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
checks=0

fixture() { # <name> <stdout> <exit> [stderr]
  local name="$1" stdout="$2" code="$3" stderr="${4:-}"
  cat >"$TMP/$name" <<EOF
#!/usr/bin/env bash
printf '%s\n' '$stdout'
[[ -z '$stderr' ]] || printf '%s\n' '$stderr' >&2
exit $code
EOF
  chmod +x "$TMP/$name"
}

expect_pass() { # <label> <tag> <fixture>
  local label="$1" tag="$2" bin="$3"
  if bash "$CHECK" "$tag" "$bin" >/dev/null; then
    printf '  ok   %s\n' "$label"
    checks=$((checks + 1))
  else
    printf '  FAIL %s: expected success\n' "$label" >&2
    exit 1
  fi
}

expect_fail() { # <label> <tag> <fixture>
  local label="$1" tag="$2" bin="$3"
  if bash "$CHECK" "$tag" "$bin" >/dev/null 2>&1; then
    printf '  FAIL %s: expected rejection\n' "$label" >&2
    exit 1
  else
    printf '  ok   %s\n' "$label"
    checks=$((checks + 1))
  fi
}

fixture good 'bang 0.1.1' 0
fixture stale 'bang 0.1.0' 0
fixture suffixed 'bang 0.1.1-dev' 0
fixture noisy 'bang 0.1.1' 0 'unexpected warning'
fixture broken 'bang 0.1.1' 7

echo '── test-release-version ──'
expect_pass 'exact stable tag' v0.1.1 "$TMP/good"
expect_fail 'stale binary' v0.1.1 "$TMP/stale"
expect_fail 'suffixed provenance' v0.1.1 "$TMP/suffixed"
expect_fail 'stderr is not silent' v0.1.1 "$TMP/noisy"
expect_fail 'nonzero --version' v0.1.1 "$TMP/broken"
expect_fail 'malformed tag rejected' 0.1.1 "$TMP/good"

[[ "$checks" -eq 6 ]] || { echo "FAIL: expected 6 checks, ran $checks" >&2; exit 1; }
echo "test-release-version: PASS — $checks/6 poles hold."
