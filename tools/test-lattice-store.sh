#!/usr/bin/env bash
# tool: role=test couples=Bang/Distribution/LatticeStore.lean,examples/lattice-store runs-in=verify
# Lattice-store surface probes: pin the shared computed-update wall and fail-closed CAS boundary.
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"
bang="${BANG_BIN:-$PWD/.lake/build/bin/bang}"
if [ "${BANG_BIN_FRESH:-0}" != 1 ]; then
  lake build bang >&2
fi

tmpdir="$(mktemp -d --tmpdir bang-lattice-store-XXXXXX)"
trap 'rm -rf "$tmpdir"' EXIT

set +e
"$bang" check examples/lattice-store/computed-update-wall.bang >"$tmpdir/computed.out" 2>&1
computed_status=$?
set -e
if [ "$computed_status" -ne 1 ]; then
  echo "test-lattice-store: computed-update probe returned $computed_status, expected 1" >&2
  cat "$tmpdir/computed.out" >&2
  exit 1
fi
grep -Fq "update clause 'joinPut' must return a value pair \`(resumeValue, nextParam)\`" \
  "$tmpdir/computed.out"

set +e
"$bang" check examples/lattice-store/cas-excluded.bang >"$tmpdir/cas.out" 2>&1
cas_status=$?
set -e
if [ "$cas_status" -ne 1 ]; then
  echo "test-lattice-store: excluded CAS check returned $cas_status, expected 1" >&2
  cat "$tmpdir/cas.out" >&2
  exit 1
fi
grep -Fq "unknown operation 'cas' for effect 'LatticeStore_Store'" "$tmpdir/cas.out"
if grep -Fq "must return a value pair" "$tmpdir/cas.out"; then
  echo "test-lattice-store: CAS refusal was masked by the computed-update boundary" >&2
  cat "$tmpdir/cas.out" >&2
  exit 1
fi

echo "test-lattice-store: computed-update wall and independent CAS refusal passed"
