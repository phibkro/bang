#!/usr/bin/env bash
# tool: role=test couples=scratch/Rung4Shape.lean,Bang/Backend/WasmEmit.lean runs-in=manual
source "$(git rev-parse --show-toplevel 2>/dev/null)/tools/tool-log.sh" 2>/dev/null && tool_log "$(basename "$0")" || true
# emit-escape-diff.sh — the #133 ESCAPE-DIFFERENTIAL gate (cap-gc-rep, ships FIRST per the C-slice
# amend). Capability-escape is a DEFINED fail-loud in the kernel (`.escapedCap`, ADR-0063): a cap
# used past its handler must NOT produce a value. The GC emitter, when it became structured control
# flow, discarded the handler CHAIN that idDispatch/splitAtId walks to detect this — so a naive
# first-class-cap rep SILENTLY SUCCEEDS on an escaped cap (witnessed: capEscape emits + prints 0 on
# wasmtime TODAY, where the kernel says .escapedCap). This gate makes that hole VISIBLE and pins the
# regression class: every escape-catalog program must (1) have kernel outcome .escapedCap, and (2)
# have its emitted module FAIL LOUD on wasmtime (a trap / non-zero exit), never a silent value.
#
# Escape is not surface-expressible in v1 (needs scoped-cap types, post-v1), so the catalog is raw
# `Comp`s in scratch/Rung4Shape.lean (`escapeCatalog`), emitted via `rung4-shape --escape`.
#
# XFAIL_UNTIL_STAMP: programs the emitter CANNOT yet fail-loud on (the $liveTop stamp = C2 not landed).
# Listed here they are KNOWN-RED (documented, not silent) so the build stays green while the hole is
# on record; C2's commit REMOVES the entry, flipping the gate to hard-fail. A program that fails loud
# but is STILL listed here is ALSO a failure (the xfail is stale — remove it).
#
# Requires: the dev shell (`nix develop`) for `lake`; `wasmtime` via `nix shell nixpkgs#wasmtime`.
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"
outdir="$(mktemp -d)"
trap 'rm -rf "$outdir"' EXIT

# Programs the emitter does not yet fail-loud on (no $liveTop stamp). EMPTY as of #134 C2 (the
# $liveTop watermark LANDED) — every escape witness now traps (rc=134) on wasmtime, matching the
# kernel's escapedCap. The list is kept (not deleted) so a FUTURE escape shape the stamp misses can
# be parked here with its number; a stale entry (a program that now traps but is still listed) is a
# hard failure, so this map cannot silently mask a regression.
declare -A XFAIL_UNTIL_STAMP=(
)

echo "── building the rung4-shape emitter exe ──"
lake build rung4-shape >/dev/null 2>&1
bin="$(find .lake/build/bin -name rung4-shape | head -1)"
[ -n "$bin" ] || { echo "FAIL: rung4-shape binary not found"; exit 2; }

echo ""
echo "── escape differential: kernel .escapedCap  vs  wasmtime fail-loud (trap / non-zero) ──"
printf '%-22s %s\n' "escape program" "verdict"

fail=0
checked=0
xfailed=0

# Shared verdict for one escape program: given its name, kernel outcome, and either EMIT=REFUSED or
# a written .wat path, assert (1) kernel = escapedCap and (2) the emitted run fails loud. Updates the
# module-level fail/checked/xfailed counters. A silent value (rc=0) is the HOLE — tolerated only if
# the name is on XFAIL_UNTIL_STAMP (documented known-red until the #133 C2 $liveTop stamp lands).
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
    out="$(nix shell nixpkgs#wasmtime -c wasmtime run -W gc=y,function-references=y,exceptions=y "$wat" 2>/dev/null)"
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
      printf '%-24s %s\n' "$name" "XFAIL (known-red #134 C2: $detail)"; xfailed=$((xfailed + 1))
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
# escapedCap on the oracle, and silently miscompile TODAY. These prove #134 is a live miscompile of
# legal programs, not a raw-Comp curiosity. Driven through the FULL surface→emit pipeline (`--print`).
echo "  [surface-reachable #134]"
surfdir="tools/../scratch/cap-gc/surface-escape"
for src in "$surfdir"/*.bang; do
  [ -f "$src" ] || continue
  name="surface:$(basename "$src" .bang)"
  # --print emits + prints the oracle valPretty; ORACLE-DIVERGED-OR-STUCK == the escape terminal.
  wat="$outdir/$(basename "$src" .bang).wat"
  set +e
  report="$("$bin" --print "$src" "$wat" 2>/dev/null)"
  set -e
  # kernel: the oracle diverged/stuck line = the escape terminal (valPretty can't render escapedCap).
  if printf '%s\n' "$report" | grep -qi 'ORACLE-DIVERGED-OR-STUCK'; then kern="KERNEL=escapedCap"; else kern="KERNEL=done"; fi
  if printf '%s\n' "$report" | grep -qiE 'EMIT-REFUSED|LOWER-ERROR'; then
    verdict_one "$name" "$kern" "EMIT=REFUSED" ""
  else
    verdict_one "$name" "$kern" "EMIT=ok" "$wat"
  fi
done

echo ""
echo "escape gate: $checked programs checked, $xfailed known-red (awaiting the #134/#133 C2 \$liveTop stamp)."
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
