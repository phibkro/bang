#!/usr/bin/env bash
# tool: role=test couples=scratch/Rung4Shape.lean,Bang/Backend/WasmEmit.lean runs-in=manual
source "$(git rev-parse --show-toplevel 2>/dev/null)/tools/tool-log.sh" 2>/dev/null && tool_log "$(basename "$0")" || true
# emit-escape-diff.sh — the #133 ESCAPE-DIFFERENTIAL gate (cap-gc-rep, ships FIRST per the C-slice
# amend). Capability-escape is a DEFINED fail-loud in the kernel (`.escapedCap`, ADR-0063): a cap
# used past its handler must NOT produce a value. The GC emitter, when it became structured control
# flow, discarded the handler CHAIN that idDispatch/splitAtId walks to detect this. The scalar
# `$liveTop` repair rejects the original immediate-escape catalog but is not exact live membership:
# `stale-state-reentry.bang` still prints a value after a later mint revives its popped id. This gate
# makes that residual VISIBLE and pins the regression class: every escape-catalog program must (1)
# have kernel outcome .escapedCap, and (2) either fail loud in emitted Wasm or remain an explicit,
# allowlisted known-red.
#
# Escape is surface-expressible in v1 (#134). The gate carries both a raw `Comp` catalog in
# `scratch/Rung4Shape.lean` and legal surface programs under `scratch/cap-gc/surface-escape/`.
#
# XFAIL_UNTIL_STAMP: programs the emitter CANNOT yet fail-loud on. Listed here they are KNOWN-RED
# (documented by the gate) so the build stays green while the hole is on record. The separately
# priced exact-liveness fix REMOVES the entry, flipping the gate to hard-fail. A program that fails
# loud but is STILL listed here is ALSO a failure (the xfail is stale — remove it).
#
# Requires: the dev shell (`nix develop`) for `lake`; `wasmtime` via `nix shell nixpkgs#wasmtime`.
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"
outdir="$(mktemp -d)"
trap 'rm -rf "$outdir"' EXIT

# CI/dev-shell default uses nixpkgs wasmtime. Sandboxed lanes may point at an already-realized,
# read-only binary without changing the semantic invocation.
run_wasmtime() {
  if [ -n "${WASMTIME_BIN:-}" ]; then
    "$WASMTIME_BIN" run -W gc=y,function-references=y,exceptions=y "$1"
  else
    nix shell nixpkgs#wasmtime -c wasmtime run -W gc=y,function-references=y,exceptions=y "$1"
  fi
}

# Programs the emitter does not yet fail-loud on. The scalar `$liveTop` stamp closes immediate
# escape, but a later handler mint raises the watermark and revives an older popped id. Keep that
# stale-reentry witness known-red until the emitter carries exact live-frame membership (or another
# representation proved equivalent to it). A stale entry that starts failing loud is a hard failure,
# so the map cannot silently mask a fix or a changed boundary.
declare -A XFAIL_UNTIL_STAMP=(
  [surface:stale-state-reentry]="scalar liveTop revives a popped id after a later handler mint"
)

echo "── building the emitter and engine executables ──"
lake build rung4-shape bang >/dev/null 2>&1
bin="$(find .lake/build/bin -name rung4-shape | head -1)"
[ -n "$bin" ] || { echo "FAIL: rung4-shape binary not found"; exit 2; }
bang="$(find .lake/build/bin -name bang | head -1)"
[ -n "$bang" ] || { echo "FAIL: bang binary not found"; exit 2; }

echo ""
echo "── escape differential: kernel .escapedCap  vs  wasmtime fail-loud (trap / non-zero) ──"
printf '%-22s %s\n' "escape program" "verdict"

fail=0
checked=0
xfailed=0

# Shared verdict for one escape program: given its name, kernel outcome, and either EMIT=REFUSED or
# a written .wat path, assert (1) kernel = escapedCap and (2) the emitted run fails loud. Updates the
# module-level fail/checked/xfailed counters. A silent value (rc=0) is the HOLE — tolerated only if
# the name is on XFAIL_UNTIL_STAMP as a documented, allowlisted known-red.
verdict_one() {
  local name="$1" kernel="$2" emit="$3" wat="$4"
  checked=$((checked + 1))

  if [ "$kernel" != "KERNEL=escapedCap" ]; then
    printf '%-24s %s\n' "$name" "FAIL (kernel=$kernel, expected escapedCap — bad catalog entry)"
    fail=1; return
  fi

  local loud=0 detail=""
  if [ "$emit" = "EMIT=REFUSED" ]; then
    loud=1; detail="emitter refused (loud)"
  else
    [ -f "$wat" ] || { printf '%-24s %s\n' "$name" "FAIL (no .wat: $wat)"; fail=1; return; }
    set +e
    local out rc
    out="$(run_wasmtime "$wat" 2>/dev/null)"
    rc=$?
    set -e
    if [ "$rc" -ne 0 ]; then loud=1; detail="wasmtime fail-loud (rc=$rc)"
    else loud=0; detail="SILENT value [$out] rc=0 — the escape HOLE"; fi
  fi

  if [ "$loud" -eq 1 ]; then
    if [ -n "${XFAIL_UNTIL_STAMP[$name]+x}" ]; then
      printf '%-24s %s\n' "$name" "FAIL (now fails loud — REMOVE from XFAIL_UNTIL_STAMP): $detail"; fail=1
    else
      printf '%-24s %s\n' "$name" "OK ($detail)"
    fi
  else
    if [ -n "${XFAIL_UNTIL_STAMP[$name]+x}" ]; then
      printf '%-24s %s\n' "$name" "XFAIL (known-red lifetime residual: $detail)"; xfailed=$((xfailed + 1))
    else
      printf '%-24s %s\n' "$name" "FAIL — $detail"; fail=1
    fi
  fi
}

# ── Leg 1: raw-Comp catalog (escape shapes not tied to a specific surface program) ──
# `--escape <outdir>` writes one <name>.wat per catalog entry + prints a TSV: name KERNEL=… EMIT=… path
echo "  [raw Comp catalog]"
while IFS=$'\t' read -r name kernel emit rest; do
  [ -n "$name" ] || continue
  verdict_one "$name" "$kernel" "$emit" "$rest"
done < <("$bin" --escape "$outdir")

# ── Leg 2: SURFACE-reachable escape (#134) — legal .bang programs that `bang check`s clean, reach
# escapedCap on the oracle. The stale-reentry member silently miscompiles today; the immediate
# members fail loud. Driven through the FULL surface→emit pipeline (`--print`).
echo "  [surface-reachable #134]"
surfdir="tools/../scratch/cap-gc/surface-escape"
for src in "$surfdir"/*.bang; do
  [ -f "$src" ] || continue
  name="surface:$(basename "$src" .bang)"
  # --print emits + prints the oracle valPretty; ORACLE-DIVERGED-OR-STUCK == the escape terminal.
  wat="$outdir/$(basename "$src" .bang).wat"
  # Pin the local semantic boundary for every legal surface witness: frontend acceptance, then
  # env/oracle/calculated-compiled all fail loud. The oracle's rc=3 is the classified escapedCap;
  # env/compiled intentionally collapse that terminal to rc=5. A drift in any leg is a gate failure.
  set +e
  "$bang" check "$src" >/dev/null 2>&1; check_rc=$?
  "$bang" run --engine=env "$src" >/dev/null 2>&1; env_rc=$?
  "$bang" run --engine=oracle "$src" >/dev/null 2>&1; oracle_rc=$?
  "$bang" run --engine=compiled "$src" >/dev/null 2>&1; compiled_rc=$?
  set -e
  if [ "$check_rc" -ne 0 ] || [ "$env_rc" -ne 5 ] || [ "$oracle_rc" -ne 3 ] || [ "$compiled_rc" -ne 5 ]; then
    printf '%-24s %s\n' "$name" \
      "FAIL (engine boundary: check=$check_rc env=$env_rc oracle=$oracle_rc compiled=$compiled_rc; expected 0/5/3/5)"
    fail=1
    continue
  fi
  set +e
  report="$("$bin" --print "$src" "$wat" 2>&1)"
  print_rc=$?
  set -e
  if [ "$print_rc" -ne 0 ]; then
    printf '%-24s %s\n' "$name" "FAIL (rung4-shape --print rc=$print_rc: $report)"
    fail=1
    continue
  fi
  # kernel: the oracle diverged/stuck line = the escape terminal (valPretty can't render escapedCap).
  if printf '%s\n' "$report" | grep -qi 'ORACLE-DIVERGED-OR-STUCK'; then kern="KERNEL=escapedCap"; else kern="KERNEL=done"; fi
  if printf '%s\n' "$report" | grep -qiE 'EMIT-REFUSED|LOWER-ERROR'; then
    verdict_one "$name" "$kern" "EMIT=REFUSED" ""
  else
    verdict_one "$name" "$kern" "EMIT=ok" "$wat"
  fi
done

echo ""
echo "escape gate: $checked programs checked, $xfailed known-red lifetime residual(s)."
if [ "$fail" -eq 0 ]; then
  if [ "$xfailed" -eq 0 ]; then
    echo "PASS — every escape program fails loud on wasmtime (== the kernel's .escapedCap)."
  else
    echo "PASS (with $xfailed known-red xfails) — no NEW regression; the documented hole is on record."
  fi
else
  echo "FAIL — an escape program that should fail loud produced a silent value, or a stale xfail."
fi
exit "$fail"
