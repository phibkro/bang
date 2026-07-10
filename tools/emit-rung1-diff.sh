#!/usr/bin/env bash
# tool: role=test couples=EmitMain,Bang/Backend/WasmEmit.lean runs-in=manual
source "$(git rev-parse --show-toplevel 2>/dev/null)/tools/tool-log.sh" 2>/dev/null && tool_log "$(basename "$0")" || true
# emit-rung1-diff.sh — the ◊5.5 rung-1 SPIKE differential harness.
# ──────────────────────────────────────────────────────────────────────────────
# The first time bang output executes OUTSIDE Lean. For each pure arithmetic sample:
#   1. `lake exe emit-rung1` writes progN.wat + prints the `Source.eval` ORACLE value.
#   2. `wasmtime run --invoke main progN.wat` runs the emitted core-wasm on a REAL engine.
#   3. diff the two. A mismatch is a LOUD failure (exit 1) — proof rides the reference
#      (invariant #1), now crossing a real-engine boundary.
#
# This is TESTED-stratum (the spike is not proof-bearing); it is the differential-test
# leg the eventual proof-grade emitter would also need (see docs/notes/emission-rung1-probe.md).
#
# Requires: the dev shell (`nix develop`) for `lake`; `wasmtime` via `nix shell nixpkgs#wasmtime`.
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"
outdir="$(mktemp -d)"
trap 'rm -rf "$outdir"' EXIT

echo "── building the emit-rung1 spike exe ──"
lake build emit-rung1 >/dev/null 2>&1
bin="$(find .lake/build/bin -name emit-rung1 | head -1)"
[ -n "$bin" ] || { echo "FAIL: emit-rung1 binary not found"; exit 2; }

echo "── emitting .wat + oracle values ──"
# Capture the emit exe's own report (name/desc/oracle) to a table we parse.
"$bin" "$outdir" | tee "$outdir/report.txt"

echo ""
echo "── differential: wasmtime (real engine)  vs  Source.eval (kernel oracle) ──"
printf '%-8s %-34s %10s %10s   %s\n' "sample" "program" "wasmtime" "oracle" "verdict"
fail=0
# Re-derive the sample list from the emitted files (progN.wat) + parse oracle from report.
for wat in "$outdir"/*.wat; do
  name="$(basename "$wat" .wat)"
  oracle="$(grep -A2 "^$name " "$outdir/report.txt" | grep 'oracle:' | sed 's/.*= //')"
  desc="$(grep "^$name " "$outdir/report.txt" | sed -E "s/^$name +\((.*)\)/\1/")"
  engine="$(nix shell nixpkgs#wasmtime -c wasmtime run --invoke main "$wat" 2>/dev/null || echo ERR)"
  if [ "$engine" = "$oracle" ]; then verdict="OK"; else verdict="MISMATCH"; fail=1; fi
  printf '%-8s %-34s %10s %10s   %s\n' "$name" "$desc" "$engine" "$oracle" "$verdict"
done

echo ""
if [ "$fail" -eq 0 ]; then
  echo "PASS — every emitted core-wasm module ran on wasmtime with a value matching Source.eval."
else
  echo "FAIL — at least one engine/oracle mismatch (see MISMATCH rows)."
fi
exit "$fail"
