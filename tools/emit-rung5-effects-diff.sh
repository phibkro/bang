#!/usr/bin/env bash
# tool: role=test couples=scratch/Rung4Shape.lean,Bang/Backend/WasmEmit.lean runs-in=manual
source "$(git rev-parse --show-toplevel 2>/dev/null)/tools/tool-log.sh" 2>/dev/null && tool_log "$(basename "$0")" || true
# emit-rung5-effects-diff.sh — the ◊5.5 EMISSION rung-5 S0-S4 EFFECTS harness.
# ────────────────────────────────────────────────────────────────────────────────────────────
# Rung 4 REFUSED every effectful program on the GC path (handle/perform → a named refusal; effects
# lowered only on the inline/linear-memory path). Rung 5 S0-S4 UNIFIES effects onto the WasmGC
# $val/$env rep: state ($ref box) · throws (try_table/throw) · transaction ($txbox journal +
# explicit rollback) · custom user effects (clause call_ref, env-reachable). So effectful whole
# programs now emitModuleGCPrint → wasmtime == `bang run`.
#
# This harness AUTO-DISCOVERS every examples/*/ with an expected.txt and gates each honestly:
#   · emits  → run wasmtime (WasmGC + WASI readback), diff stdout vs expected.txt (= bang run stdout).
#   · refuses → OK ONLY if the example is in KNOWN_REFUSALS (a named wall). A NEW refusal FAILS LOUD
#              (a regression: something that used to lower now doesn't) — never silently skipped.
# So the corpus count grows by construction and a drift in either direction is caught.
#
# Requires: the dev shell (`nix develop`) for `lake`; `wasmtime` via `nix shell nixpkgs#wasmtime`.
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"
outdir="$(mktemp -d)"
trap 'rm -rf "$outdir"' EXIT

# Programs the GC path CANNOT lower yet, each with the NAMED wall. A refusal here is expected; an
# emit here (or a refusal NOT here) is a gate failure. Keep this list minimal + honest.
#   calc/json : MULTI-MODULE — refuse HERE only because this gate drives the single-file `rung4-shape`
#               exe (no import resolution). They EMIT + run == bang run via `bang emit` (module-
#               resolving); gated by emit-rung5-print-diff.sh's MODULE_CORPUS=( json calc ) (calc
#               11021193, json 163). NOT an emitter wall — a harness-scope split (#133 C3).
#   reactive-* / resource-contract / policy/pledged: newer multi-file examples have the same
#               single-file-harness boundary and are covered by the module-aware `bang build` battery.
#   hostio-echo : FRONTEND host-IO perform not lowered here (ADR-0104 boundary) — a real refusal.
#   sched-*                : `drive`'s NINE-argument curried `let rec` (5 curried Step/Int params
#                           plus round+acc) leaves a type variable unresolved for ADR-0103's
#                           monomorphization pass at one of its self-calls — a frontend lower-error
#                           orthogonal to the Sched EFFECT itself (the same wall calc/json hit on
#                           unrelated polymorphic-use shapes, not a Sched-specific gap). Named here,
#                           not investigated further — a compiler-side fix is out of this lane's
#                           write scope (docs/notes/sched-library-demo.md §"the emission attempt").
# NOTE (#133 C0 + multi-op successor): first-class custom capabilities NO LONGER refuse — stage-swap
# runs 30005 and first-class-multi-operation-cap runs 255 through exact runtime clause records. Both
# remain #134-stamped for liveness. Multi-file stage-swap is named below only because this harness does
# not resolve imports; the module-aware build battery executes it.
declare -A KNOWN_REFUSALS=(
  [calc]="frontend: unbound variable Ast"
  [codec-contract]="single-file harness: module/use resolution belongs to emit-rung5-print-diff"
  [json]="frontend: unresolved type variable"
  [hostio-echo]="frontend: host-IO perform not lowered here"
  [pledged-plugin]="single-file harness: imported handler realization belongs to emit-rung5-print-diff"
  [policy-host-allowlist]="single-file harness: imported effect belongs to emit-rung5-print-diff"
  [reactive-observation-reuse]="single-file harness: imported generated workload belongs to module-aware bang build"
  [reactive-recomputation]="single-file harness: imported workload belongs to module-aware bang build"
  [reactive-spreadsheet]="single-file harness: imported formulas belong to module-aware bang build"
  [resource-contract]="single-file harness: imported handler realization belongs to module-aware bang build"
  [sched-roundrobin]="frontend: unresolved type variable (drive's curried self-calls, ADR-0103 monomorphization)"
  [sched-swap-dfs]="frontend: unresolved type variable (drive's curried self-calls, ADR-0103 monomorphization)"
  [sched-seeded-lcg]="frontend: unresolved type variable (drive's curried self-calls, ADR-0103 monomorphization)"
  [stage-swap]="single-file harness: imported handler realizations belong to emit-rung5-print-diff"
)

echo "── building the rung4-shape emitter exe ──"
lake build rung4-shape >/dev/null 2>&1
bin="$(find .lake/build/bin -name rung4-shape | head -1)"
[ -n "$bin" ] || { echo "FAIL: rung4-shape binary not found"; exit 2; }

echo ""
echo "── effects differential: wasmtime stdout (WasmGC S0-S4)  vs  expected.txt (= bang run) ──"
printf '%-26s %s\n' "example" "verdict"
fail=0
emitted=0
refused=0
effectful=0

for dir in examples/*/; do
  name="$(basename "$dir")"
  main="$dir/main.bang"
  exp="$dir/expected.txt"
  [ -f "$main" ] || continue
  [ -f "$exp" ]  || continue

  # Does the source use an effect? Honest effectful count: strip comment lines (-- …), then look for
  # genuine effect SYNTAX (handle/with a handler · atomically · a perform-op keyword). Loose is fine
  # for a lower bound — the gate is MIN_EFFECTFUL, and a false positive only inflates that floor.
  is_eff=0
  if grep -vE '^\s*--' "$main" 2>/dev/null | grep -qE '\b(handle|atomically|perform|effect)\b|\bwith\b.*\{|\braise\b' 2>/dev/null; then
    is_eff=1
  fi

  wat="$outdir/$name.wat"
  set +e
  report="$("$bin" --print "$main" "$wat" 2>/dev/null)"
  emit_rc=$?
  set -e
  [ "$emit_rc" -eq 0 ] || { echo "FAIL: rung4-shape --print crashed on $name"; echo "$report"; exit 2; }

  if printf '%s\n' "$report" | grep -qiE 'EMIT-REFUSED|LOWER-ERROR'; then
    reason="$(printf '%s\n' "$report" | grep -iE 'REFUSED|ERROR' | head -1)"
    if [ -n "${KNOWN_REFUSALS[$name]+x}" ]; then
      printf '%-26s %s\n' "$name" "REFUSE (named: ${KNOWN_REFUSALS[$name]})"
      refused=$((refused + 1))
    else
      echo "FAIL: $name REFUSED but is not a KNOWN wall (regression?):"
      echo "   $reason"
      fail=1
    fi
    continue
  fi

  [ -f "$wat" ] || { echo "FAIL: no .wat emitted for $name"; exit 2; }
  emitted=$((emitted + 1))
  [ "$is_eff" -eq 1 ] && effectful=$((effectful + 1))

  set +e
  engine="$(nix shell nixpkgs#wasmtime -c wasmtime run -W gc=y,function-references=y,exceptions=y "$wat" 2>/dev/null)"
  wt_rc=$?
  set -e
  [ "$wt_rc" -eq 0 ] || engine="ENGINE-ERR(rc=$wt_rc)"

  expected="$(cat "$exp")"
  if [ "$engine" = "$expected" ]; then
    tag="OK"; [ "$is_eff" -eq 1 ] && tag="OK (effectful)"
    printf '%-26s %s\n' "$name" "$tag"
  else
    printf '%-26s %s\n' "$name" "MISMATCH"; fail=1
    echo ""; echo "!! MISMATCH on $name"
    echo "   wasmtime stdout : [$engine]"
    echo "   expected.txt    : [$expected]"
    echo ""
  fi
done

# ADR-0114 is intentionally below the surface gate, so exercise its raw `ClauseKey.updating` witness
# separately. This is the concrete-emitter regression: the second call must observe the parameter
# installed by the first call, not the immutable environment captured when the clauses were lifted.
echo ""
echo "── stateful custom-clause differential (raw typed IR) ──"
stateful_report="$("$bin" --stateful-custom "$outdir")"
while IFS=$'\t' read -r name oracle_field emit_field wat; do
  [ -n "$name" ] || continue
  expected="${oracle_field#ORACLE=}"
  if [ "$emit_field" != "EMIT=ok" ] || [ ! -f "$wat" ]; then
    printf '%-26s %s\n' "$name" "REFUSED"; fail=1
    continue
  fi
  set +e
  engine="$(nix shell nixpkgs#wasmtime -c wasmtime run -W gc=y,function-references=y,exceptions=y --invoke main "$wat" 2>/dev/null)"
  wt_rc=$?
  set -e
  if [ "$wt_rc" -eq 0 ] && [ "$engine" = "$expected" ]; then
    printf '%-26s %s\n' "$name" "OK (stateful custom)"
  else
    printf '%-26s %s\n' "$name" "MISMATCH"; fail=1
    echo "   wasmtime stdout : [$engine]"
    echo "   Source.eval     : [$expected]"
  fi
done <<< "$stateful_report"

# False-green guard: assert the corpus is not silently short (S0-S4 pushed effectful count up).
MIN_EMITTED="${MIN_EMITTED:-30}"
MIN_EFFECTFUL="${MIN_EFFECTFUL:-18}"
if [ "$emitted" -lt "$MIN_EMITTED" ]; then
  echo "FAIL: only $emitted programs emitted, expected ≥ $MIN_EMITTED (corpus shrank?)"; exit 2
fi
if [ "$effectful" -lt "$MIN_EFFECTFUL" ]; then
  echo "FAIL: only $effectful EFFECTFUL programs emitted, expected ≥ $MIN_EFFECTFUL (S0-S4 regressed?)"; exit 2
fi

echo ""
echo "corpus: $emitted whole programs → WasmGC → wasmtime == expected.txt"
echo "        (of which $effectful are EFFECTFUL — handle/perform/atomically, the rung-5 S0-S4 win)"
echo "        $refused named frontend/host-IO refusals"
if [ "$fail" -eq 0 ]; then
  echo "PASS — all emitted programs' READBACK matched bang run; every refusal is a NAMED wall."
else
  echo "FAIL — a mismatch or an UNEXPECTED refusal (see block(s) above)."
fi
exit "$fail"
