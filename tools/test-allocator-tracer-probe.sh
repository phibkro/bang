#!/usr/bin/env bash
# tool: role=test couples=scratch/allocator-tracer/,Bang/Frontend/TypeCheck.lean,Bang/Core/Semantics/Eval.lean runs-in=manual
# Allocator S0: update-envelope bisect, structured handler state, exact-once result binding,
# concrete-Wasm differential, and the identity-only handler-pop boundary.
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"
bang="${BANG_BIN:-$PWD/.lake/build/bin/bang}"
if [ "${BANG_BIN_FRESH:-0}" != 1 ]; then
  lake build bang >&2
fi

tmpdir="$(mktemp -d --tmpdir bang-allocator-probe-XXXXXX)"
trap 'rm -rf "$tmpdir"' EXIT

check_exact() {
  local stem=$1
  local expected_exit=$2
  local source="scratch/allocator-tracer/$stem.bang"
  local actual="$tmpdir/$stem.check.json"
  local expected="scratch/allocator-tracer/evidence/$stem.check.json"

  if "$bang" check --json "$source" >"$actual"; then
    test "$expected_exit" = pass || {
      echo "test-allocator-tracer-probe: expected $source to fail" >&2
      return 1
    }
  else
    test "$expected_exit" = fail || {
      echo "test-allocator-tracer-probe: expected $source to pass" >&2
      return 1
    }
  fi
  cmp "$expected" "$actual"
}

for stem in structured-param value-pair-update use-one-result; do
  check_exact "$stem" pass
done
for stem in computed-update-refused computed-components-refused match-components-refused \
  use-one-duplicate-refused use-one-forgotten-refused; do
  check_exact "$stem" fail
done

"$bang" query contract scratch/allocator-tracer/structured-param.bang \
  >"$tmpdir/structured-param.contract.json"
cmp scratch/allocator-tracer/evidence/structured-param.contract.json \
  "$tmpdir/structured-param.contract.json"

run_all_engines() {
  local stem=$1
  local expected=$2
  local source="scratch/allocator-tracer/$stem.bang"
  local engine
  for engine in env oracle compiled; do
    test "$("$bang" run --engine="$engine" "$source")" = "$expected"
  done
}

run_all_engines structured-param 403
run_all_engines value-pair-update 700
run_all_engines use-one-result 7

wasm_tools="${WASM_TOOLS_BIN:-$(command -v wasm-tools || true)}"
wasmtime="${WASMTIME_BIN:-$(command -v wasmtime || true)}"
if { [ -z "$wasm_tools" ] || [ -z "$wasmtime" ]; } && command -v nix >/dev/null 2>&1; then
  resolved="$(
    nix shell nixpkgs#wasm-tools nixpkgs#wasmtime \
      -c bash -c 'command -v wasm-tools; command -v wasmtime' 2>/dev/null || true
  )"
  [ -n "$wasm_tools" ] || wasm_tools="$(printf '%s\n' "$resolved" | sed -n '1p')"
  [ -n "$wasmtime" ] || wasmtime="$(printf '%s\n' "$resolved" | sed -n '2p')"
fi
test -x "$wasm_tools" || {
  echo "test-allocator-tracer-probe: wasm-tools is required (set WASM_TOOLS_BIN or make nix shell reachable)" >&2
  exit 1
}
test -x "$wasmtime" || {
  echo "test-allocator-tracer-probe: wasmtime is required (set WASMTIME_BIN or make nix shell reachable)" >&2
  exit 1
}

run_wasm() {
  local stem=$1
  local expected=$2
  local source="scratch/allocator-tracer/$stem.bang"
  local wasm="$tmpdir/$stem.wasm"
  PATH="$(dirname "$wasm_tools"):$PATH" "$bang" build "$source" -o "$wasm" >/dev/null
  test "$("$wasmtime" -W gc=y,function-references=y,exceptions=y "$wasm")" = "$expected"
}

run_wasm structured-param 403
run_wasm value-pair-update 700
run_wasm use-one-result 7

# There is no at-pop clause in the surface representation, and the source machine discards a
# handler frame on return without consulting its parameter. These implementation assertions keep
# the negative finding tied to the two authorities rather than to prose or an invented syntax.
test "$(sed -n '353,356p' Bang/Frontend/Surface.lean | grep -Ec '^  \| (nil|cons|consUpdating)')" = 3
grep -Fq '| (g, .handleF _ _ :: K, .ret v) => some (g, K, .ret v)' Bang/Core/Semantics/Eval.lean

# This probe records the accepted semantic boundary; it must not relax the checker, kernel, or
# concrete-Wasm implementation to manufacture an allocator result.
git diff --quiet -- Bang/Core Bang/Frontend/TypeCheck.lean Bang/Backend/WasmEmit.lean

echo "test-allocator-tracer-probe: S0 matrix, quantity poles, engines, Wasm, and semantic stop passed"
