#!/usr/bin/env bash
# tool: role=test couples=Main.lean,Bang/Backend/WasmEmit.lean runs-in=manual
source "$(git rev-parse --show-toplevel 2>/dev/null)/tools/tool-log.sh" 2>/dev/null && tool_log "$(basename "$0")" || true
# emit-modules-diff.sh — the MULTI-MODULE emission gate (#133 C3 / the calc headline).
# ────────────────────────────────────────────────────────────────────────────────────────────
# The rung-5 corpus gate (emit-rung5-effects-diff.sh) drives the `rung4-shape` scratch exe, which
# lowers a SINGLE file — so multi-file programs (calc, json) refuse there with a frontend
# "unbound variable" (their imports aren't resolved). This gate drives `bang emit` instead, which
# shares the runner's module resolution (`resolveEntryFile`, Main.lean) — so an import-ing program
# emits. It gates the MULTI-MODULE examples end-to-end: bang emit → wasmtime stdout vs expected.txt
# (= bang run stdout).
#
# The headline consumer is CALC (#133): examples/calc is 5 modules with a first-class `Cap Trace`
# woven through a recursive evaluator — the exact first-class-capability shape #133 named. Its C0
# dispatch (the runtime $txbox cap) + the #134 escape stamp carry it to WasmGC. json is the pure
# multi-module companion (no effects).
#
# Requires: the dev shell (`nix develop`) for `lake`; `wasmtime` via `nix shell nixpkgs#wasmtime`.
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"
outdir="$(mktemp -d)"
trap 'rm -rf "$outdir"' EXIT

# Multi-module examples that emit via `bang emit`. Each MUST emit + run == expected.txt. A refusal
# or mismatch is a hard failure. (Single-module examples stay on emit-rung5-effects-diff.sh.)
MULTI_MODULE=(calc json)

echo "── building bang ──"
lake build bang >/dev/null 2>&1
bin="$(find .lake/build/bin -name bang | head -1)"
[ -n "$bin" ] || { echo "FAIL: bang binary not found"; exit 2; }

echo ""
echo "── multi-module emission: bang emit → wasmtime stdout  vs  expected.txt (= bang run) ──"
printf '%-12s %s\n' "example" "verdict"
fail=0

for name in "${MULTI_MODULE[@]}"; do
  main="examples/$name/main.bang"
  exp="examples/$name/expected.txt"
  [ -f "$main" ] || { printf '%-12s %s\n' "$name" "FAIL (no $main)"; fail=1; continue; }
  [ -f "$exp" ]  || { printf '%-12s %s\n' "$name" "FAIL (no $exp)"; fail=1; continue; }

  wat="$outdir/$name.wat"
  set +e
  emit_err="$("$bin" emit "$main" -o "$wat" 2>&1 1>/dev/null)"
  emit_rc=$?
  set -e
  if [ "$emit_rc" -ne 0 ]; then
    printf '%-12s %s\n' "$name" "FAIL (bang emit rc=$emit_rc: $(printf '%s' "$emit_err" | head -1))"; fail=1; continue
  fi
  [ -f "$wat" ] || { printf '%-12s %s\n' "$name" "FAIL (no .wat emitted)"; fail=1; continue; }

  set +e
  got="$(nix shell nixpkgs#wasmtime -c wasmtime run -W gc=y,function-references=y,exceptions=y "$wat" 2>/dev/null)"
  wt_rc=$?
  set -e
  [ "$wt_rc" -eq 0 ] || got="WASMTIME-ERR(rc=$wt_rc)"

  want="$(cat "$exp")"
  if [ "$got" = "$want" ]; then
    printf '%-12s %s\n' "$name" "OK ($got)"
  else
    printf '%-12s %s\n' "$name" "MISMATCH — wasmtime [$got] vs expected [$want]"; fail=1
  fi
done

echo ""
if [ "$fail" -eq 0 ]; then
  echo "PASS — every multi-module example: bang emit → wasmtime == bang run."
  echo "       calc = a 5-module program with a first-class Cap Trace, running as a wasm binary (#133)."
else
  echo "FAIL — a multi-module example did not emit + run == its expected.txt."
fi
exit "$fail"
