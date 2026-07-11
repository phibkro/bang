#!/usr/bin/env bash
# tool: role=test couples=scratch/Rung4Shape.lean,Bang/Backend/WasmEmit.lean runs-in=manual
source "$(git rev-parse --show-toplevel 2>/dev/null)/tools/tool-log.sh" 2>/dev/null && tool_log "$(basename "$0")" || true
# emit-rung4-diff.sh — the ◊5.5 EMISSION rung-4 differential harness (closures + ADTs + recursion).
# ────────────────────────────────────────────────────────────────────────────────────────────
# Rung 4 lowers the PURE λ + ADT + recursion fragment to WasmGC (ADR-0059's `general` slot): each
# `lam`/`vthunk` lambda-lifts to a wasm function, `app`/`force` are `call_ref` through a closure
# GC-struct, ADTs are GC structs (sums/pairs; `fold`/`unfold` erase), recursion runs on the wasm
# call stack (the μ-knot's `force`/`unfold`/`app` — no invented former). See
# `docs/notes/emission-rung4-design.md` and `Bang/Backend/WasmEmit.lean`'s rung-4 section.
#
# For each corpus example (whole `.bang` programs, source → checkAndLower → emitModuleGC):
#   1. `lake exe rung4-shape <main.bang> <NAME.wat>` writes the WasmGC module + prints the
#      `Source.eval` ORACLE value.
#   2. `wasmtime run -W gc=y,function-references=y,exceptions=y --invoke main NAME.wat` runs it on
#      a REAL engine (Wasm 3.0 GC + typed function refs).
#   3. diff the two. A mismatch is a LOUD failure (exit 1) — proof rides the reference (invariant #1),
#      now over closures/ADTs/recursion across a real-engine boundary. THE MILESTONE: nqueens = 21004.
#
# The corpus is the Int-returning subset of examples/ the rung honestly covers (effect-using programs
# lower on the inline rungs 1-3 and are OUT of the GC fragment — a NAMED refusal, not a failure).
#
# Requires: the dev shell (`nix develop`) for `lake`; `wasmtime` via `nix shell nixpkgs#wasmtime`.
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"
outdir="$(mktemp -d)"
trap 'rm -rf "$outdir"' EXIT

# The rung-4 corpus: whole example PROGRAMS the GC fragment covers end-to-end (Int-returning). Each
# exercises closures + ADTs + recursion; nqueens is the roadmap-named milestone.
CORPUS=(
  nqueens list-basics mutual-parity parser-combinators wildcard-match
  tokenizer string-stdlib derive-eq-ord trait-recursive-eq trait-recursive-ord
)
MIN_EMITTED="${MIN_EMITTED:-10}"

echo "── building the rung4-shape emitter exe ──"
lake build rung4-shape >/dev/null 2>&1
bin="$(find .lake/build/bin -name rung4-shape | head -1)"
[ -n "$bin" ] || { echo "FAIL: rung4-shape binary not found"; exit 2; }

echo ""
echo "── differential: wasmtime (WasmGC, real engine)  vs  Source.eval (kernel oracle) ──"
printf '%-22s %14s %14s   %s\n' "example" "wasmtime" "oracle" "verdict"
fail=0
emitted=0
for name in "${CORPUS[@]}"; do
  main="examples/$name/main.bang"
  wat="$outdir/$name.wat"
  [ -f "$main" ] || { echo "FAIL: missing example $main"; exit 2; }

  # Emit + capture the oracle. Guard the exit explicitly (a crashed emitter must not read as green).
  set +e
  report="$("$bin" "$main" "$wat" 2>/dev/null)"
  emit_rc=$?
  set -e
  [ "$emit_rc" -eq 0 ] || { echo "FAIL: rung4-shape crashed on $name"; echo "$report"; exit 2; }

  oracle="$(printf '%s\n' "$report" | grep -oE 'Source.eval = [0-9-]+' | head -1 | sed 's/.*= //')"
  if [ -z "$oracle" ]; then
    echo "FAIL: no integer oracle parsed for $name — emitter refused or non-Int result:"
    printf '%s\n' "$report" | grep -iE 'REFUSED|LOWER-ERROR|oracle' | head -3
    exit 2
  fi
  [ -f "$wat" ] || { echo "FAIL: no .wat emitted for $name"; exit 2; }
  emitted=$((emitted + 1))

  set +e
  engine="$(nix shell nixpkgs#wasmtime -c wasmtime run -W gc=y,function-references=y,exceptions=y --invoke main "$wat" 2>/dev/null)"
  wt_rc=$?
  set -e
  [ "$wt_rc" -eq 0 ] || engine="ENGINE-ERR(rc=$wt_rc)"

  if [ "$engine" = "$oracle" ]; then verdict="OK"; else verdict="MISMATCH"; fail=1; fi
  printf '%-22s %14s %14s   %s\n' "$name" "$engine" "$oracle" "$verdict"
  if [ "$verdict" = "MISMATCH" ]; then
    echo ""; echo "!! MISMATCH on $name — wasmtime=$engine oracle=$oracle"; echo "   emitted .wat:"
    sed 's/^/     /' "$wat"; echo ""
  fi
done

# False-green guard: assert the corpus is not silently short.
if [ "$emitted" -lt "$MIN_EMITTED" ]; then
  echo "FAIL: only $emitted programs emitted, expected ≥ $MIN_EMITTED (corpus too small)"
  exit 2
fi

echo ""
echo "corpus: $emitted whole programs (closures+ADTs+recursion) → WasmGC → wasmtime → diffed vs Source.eval"
if [ "$fail" -eq 0 ]; then
  echo "PASS — all $emitted programs ran on wasmtime with a value matching Source.eval (nqueens = 21004)."
else
  echo "FAIL — at least one engine/oracle mismatch (see MISMATCH block(s) above)."
fi
exit "$fail"
