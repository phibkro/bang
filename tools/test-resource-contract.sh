#!/usr/bin/env bash
# tool: role=test couples=Bang/Frontend/TypeCheck.lean,Bang/Backend/WasmEmit.lean,Bang/Frontend/Query.lean runs-in=verify
# Resource-contract tracer: acceptance, refusals, query join, laws, and observable Wasm erasure.
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"
bang="${BANG_BIN:-$PWD/.lake/build/bin/bang}"
if [ "${BANG_BIN_FRESH:-0}" != 1 ]; then
  lake build bang >&2
fi

tmpdir="$(mktemp -d --tmpdir bang-resource-contract-XXXXXX)"
trap 'rm -rf "$tmpdir"' EXIT

"$bang" check scratch/resource-contract/accept-once.bang >/dev/null
test "$("$bang" run scratch/resource-contract/accept-once.bang)" = 7
test "$("$bang" run scratch/resource-contract/erase-zero.bang)" = 7

for fixture in reject-duplicate reject-forget; do
  if "$bang" check "scratch/resource-contract/$fixture.bang" >"$tmpdir/$fixture.out" 2>&1; then
    echo "test-resource-contract: expected $fixture to fail" >&2
    exit 1
  fi
  grep -Fq 'error[B018]: quantity mismatch' "$tmpdir/$fixture.out"
done

"$bang" test examples/resource-contract/Permit.bang >"$tmpdir/laws.out"
grep -Fq 'laws: 2/2 passed' "$tmpdir/laws.out"

"$bang" query contract examples/resource-contract/main.bang >"$tmpdir/contract.json"
grep -Fq '"name":"ghost","declared":"[0]","observed":"[0]"' "$tmpdir/contract.json"
grep -Fq '"name":"permit","declared":"[1]","observed":"[1]"' "$tmpdir/contract.json"
grep -Fq '"typeChecked":true' "$tmpdir/contract.json"

"$bang" emit examples/resource-contract/main.bang -o "$tmpdir/main.wat"
grep -Fq '(drop (struct.new $ival (i64.const 99)))' "$tmpdir/main.wat"

echo "test-resource-contract: acceptance, refusals, laws, query, and Wasm erasure passed"
