#!/usr/bin/env bash
# tool: role=check couples=Main.lean,tools/release.sh,tools/release-artifact.sh,tools/bang/release-version-check.bang runs-in=ci
# Exact release-tag ↔ compiler-provenance gate. One comparison seam for local
# tagging and the final stripped CI artifact.
#
# The tag-format-validation + string-compare DECISION is a compiled bang program
# (tools/bang/release-version-check.bang) — this shell wrapper only does what bang v1
# cannot do itself: spawn the artifact under test and capture its stdout/stderr. bang has
# no subprocess primitive, so the split is: shell orchestrates the process, bang decides
# PASS/FAIL over the two resulting strings (fed via real stdin, ADR-0104's host-IO seam).
set -euo pipefail

TAG="${1:?usage: check-release-version.sh <vX.Y.Z> <bang-executable>}"
BANG="${2:?usage: check-release-version.sh <vX.Y.Z> <bang-executable>}"
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
CHECKER_RUNNER="$ROOT/.lake/build/bin/bang"
CHECKER_PROG="$ROOT/tools/bang/release-version-check.bang"

if [[ ! -x "$BANG" ]]; then
  echo "release-version: FAIL — executable not found: $BANG" >&2
  exit 1
fi
if [[ ! -x "$CHECKER_RUNNER" ]]; then
  echo "release-version: FAIL — checker runner not found: $CHECKER_RUNNER (run 'lake build bang' first)." >&2
  exit 1
fi

stderr_file="$(mktemp)"
trap 'rm -f "$stderr_file"' EXIT
set +e
actual="$($BANG --version 2>"$stderr_file")"
code=$?
set -e
stderr="$(<"$stderr_file")"

if [[ "$code" -ne 0 ]]; then
  echo "release-version: FAIL — '$BANG --version' exited $code." >&2
  [[ -z "$stderr" ]] || printf 'stderr: %s\n' "$stderr" >&2
  exit 1
fi
if [[ -n "$stderr" ]]; then
  echo "release-version: FAIL — '$BANG --version' wrote to stderr: [$stderr]" >&2
  exit 1
fi

verdict="$(printf '%s\n%s\n' "$TAG" "$actual" | "$CHECKER_RUNNER" run --env=real --allow=Console "$CHECKER_PROG")"

if [[ "$verdict" != PASS ]]; then
  echo "release-version: $verdict" >&2
  exit 1
fi

echo "release-version: PASS — $TAG ≡ '$actual'."
