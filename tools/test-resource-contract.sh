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
  grep -Fq 'error[B018]' "$tmpdir/$fixture.out"
  grep -Fq 'quantity mismatch' "$tmpdir/$fixture.out"
done

# Frozen-study T03 transfer: keep both permit uses, widen the explicit local obligation, and prove
# the recovery checks. This is stdin-safe because the refusal fixture is self-contained.
sed 's/use \[1\] permit/use [omega] permit/' scratch/resource-contract/reject-duplicate.bang |
  "$bang" check >/dev/null

"$bang" test examples/resource-contract/Permit.bang >"$tmpdir/laws.out"
grep -Fq 'laws: 2/2 passed' "$tmpdir/laws.out"

"$bang" query contract examples/resource-contract/main.bang >"$tmpdir/contract.json"
grep -Fq '"ok":true,"subjectValid":true' "$tmpdir/contract.json"
grep -Fq '"name":"ghost","declared":"[0]","observed":"[0]"' "$tmpdir/contract.json"
grep -Fq '"name":"permit","declared":"[1]","observed":"[1]"' "$tmpdir/contract.json"
grep -Fq '"typeChecked":true' "$tmpdir/contract.json"

# Frozen-study T04 transfer: install the alternative realization, predict/observe -7, and retain
# the same stable evidence identities despite the selected display name changing.
mkdir -p "$tmpdir/negate"
cp examples/resource-contract/Permit.bang "$tmpdir/negate/Permit.bang"
cat > "$tmpdir/negate/main.bang" <<'BANG'
use Permit (Negate)

handle
  use [1] permit in permit.spend(7)
with Negate as permit
BANG
test "$("$bang" run "$tmpdir/negate/main.bang")" = -7
"$bang" query contract "$tmpdir/negate/main.bang" >"$tmpdir/negate-contract.json"
grep -Fq '"id":"Permit_Permit@Permit_Negate:preserves_zero"' "$tmpdir/negate-contract.json"

# Frozen-study T06: inspecting a refused subject is still a successful query operation, but the
# explicit top-level validity signal is false.
"$bang" query contract scratch/resource-contract/reject-duplicate.bang >"$tmpdir/refused-contract.json"
grep -Fq '"ok":true,"subjectValid":false' "$tmpdir/refused-contract.json"
grep -Fq '"typeChecked":false' "$tmpdir/refused-contract.json"

"$bang" emit examples/resource-contract/main.bang -o "$tmpdir/main.wat"
grep -Fq '(drop (struct.new $ival (i64.const 99)))' "$tmpdir/main.wat"

echo "test-resource-contract: acceptance, refusals, laws, query, and Wasm erasure passed"
