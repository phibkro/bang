#!/usr/bin/env bash
# ◊5 engine probe (OPEN_QUESTIONS Q9 / ADR-0035): confirm a released Wasmtime runs
# a stack-switching suspend/resume generator on x86_64 Linux. This is leg #2's
# foundation (the real-engine diff-test oracle) and the single biggest external
# de-risk for the WasmFX backend. Run-the-real-journey: executes the actual engine.
#
#   bash tools/wasmfx-probe.sh        ⟹ prints PASS / FAIL, exits 0 / 1
set -euo pipefail

WAT="$(dirname "$0")/../test/wasmfx/generator.wat"
EXPECTED=49
FLAGS="stack-switching=y,function-references=y,gc=y,exceptions=y"

# wasmtime via nixpkgs (pinned to whatever the dev shell / nixpkgs provides; ≥ 44.0.1).
run() {
  if command -v wasmtime >/dev/null 2>&1; then
    wasmtime run -W "$FLAGS" --invoke main "$WAT" 2>/dev/null
  else
    nix shell nixpkgs#wasmtime --command wasmtime run -W "$FLAGS" --invoke main "$WAT" 2>/dev/null
  fi
}

GOT="$(run | tr -d '[:space:]')"   # unpiped capture ⇒ real exit code (memory: nix-build-verify-exit-codes)

if [ "$GOT" = "$EXPECTED" ]; then
  echo "PASS — wasmtime ran suspend/resume generator → $GOT (expected $EXPECTED)"
  exit 0
else
  echo "FAIL — got '$GOT', expected '$EXPECTED'"
  echo "  (engine viability regressed; leg #2 diff-test oracle unavailable — see Q9)"
  exit 1
fi
