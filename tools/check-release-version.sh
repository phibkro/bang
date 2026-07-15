#!/usr/bin/env bash
# tool: role=check couples=Main.lean,tools/release.sh,tools/release-artifact.sh runs-in=ci
# Exact release-tag ↔ compiler-provenance gate. One comparison seam for local
# tagging and the final stripped CI artifact.
set -euo pipefail

TAG="${1:?usage: check-release-version.sh <vX.Y.Z> <bang-executable>}"
BANG="${2:?usage: check-release-version.sh <vX.Y.Z> <bang-executable>}"

if [[ ! "$TAG" =~ ^v[0-9]+\.[0-9]+\.[0-9]+$ ]]; then
  echo "release-version: FAIL — expected a stable vX.Y.Z tag, got '$TAG'." >&2
  exit 1
fi
if [[ ! -x "$BANG" ]]; then
  echo "release-version: FAIL — executable not found: $BANG" >&2
  exit 1
fi

stderr_file="$(mktemp)"
trap 'rm -f "$stderr_file"' EXIT
set +e
actual="$($BANG --version 2>"$stderr_file")"
code=$?
set -e
stderr="$(<"$stderr_file")"
expected="bang ${TAG#v}"

if [[ "$code" -ne 0 ]]; then
  echo "release-version: FAIL — '$BANG --version' exited $code." >&2
  [[ -z "$stderr" ]] || printf 'stderr: %s\n' "$stderr" >&2
  exit 1
fi
if [[ -n "$stderr" ]]; then
  echo "release-version: FAIL — '$BANG --version' wrote to stderr: [$stderr]" >&2
  exit 1
fi
if [[ "$actual" != "$expected" ]]; then
  echo "release-version: FAIL — tag and binary provenance disagree." >&2
  echo "  expected: [$expected]" >&2
  echo "  observed: [$actual]" >&2
  exit 1
fi

echo "release-version: PASS — $TAG ≡ '$actual'."
