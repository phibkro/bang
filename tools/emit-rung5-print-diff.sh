#!/usr/bin/env bash
# tool: role=test couples=scratch/Rung4Shape.lean,Bang/Backend/WasmEmit.lean runs-in=manual
source "$(git rev-parse --show-toplevel 2>/dev/null)/tools/tool-log.sh" 2>/dev/null && tool_log "$(basename "$0")" || true
# emit-rung5-print-diff.sh — the ◊5.5 EMISSION rung-5 Part-1 READBACK harness.
# ────────────────────────────────────────────────────────────────────────────────────────────
# Rung 4 could only $unbox a result to i64, so a Str/sum/pair-returning program (e.g. `caesar`)
# emitted but the extracted answer was meaningless. Rung 5 Part 1 adds the $val READBACK: a WASI
# `_start` module whose stdout is `valPretty (Source.eval M)` — the SAME text `bang run` prints and
# `examples/<name>/expected.txt` carries. This UNIFIES Int and non-Int results under one printer.
#
# For each corpus example:
#   1. `lake exe rung4-shape --print <main.bang> <NAME.wat>` writes the WASI readback module and
#      prints the full-shape `valPretty` ORACLE (Int / Str-glyphs / inl/inr / pair).
#   2. `wasmtime run <NAME.wat>` (a WASI COMMAND, NOT --invoke) runs it; the `$render` walk writes
#      the rendered value + newline to stdout via fd_write.
#   3. diff wasmtime stdout against `examples/<name>/expected.txt` (which IS `bang run`'s stdout).
#      A mismatch is a LOUD failure (exit 1) — proof rides the reference (invariant #1), now over
#      the READBACK across a real-engine boundary. THE NEW COVERAGE: caesar's Str result.
#
# Requires: the dev shell (`nix develop`) for `lake`; `wasmtime` via `nix shell nixpkgs#wasmtime`.
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"
outdir="$(mktemp -d)"
trap 'rm -rf "$outdir"' EXIT

# The rung-5 Part-1 corpus: the rung-4 GC-fragment programs (now via the unified readback) PLUS the
# non-Int result caesar (Str) that rung 4 could not read back.
CORPUS=(
  nqueens list-basics mutual-parity parser-combinators wildcard-match
  tokenizer string-stdlib derive-eq-ord trait-recursive-eq trait-recursive-ord
  caesar neg-div big-literal
)
MIN_EMITTED="${MIN_EMITTED:-13}"

echo "── building the rung4-shape emitter exe ──"
lake build rung4-shape >/dev/null 2>&1
bin="$(find .lake/build/bin -name rung4-shape | head -1)"
[ -n "$bin" ] || { echo "FAIL: rung4-shape binary not found"; exit 2; }

echo ""
echo "── readback differential: wasmtime stdout (WasmGC + WASI)  vs  expected.txt (= bang run) ──"
printf '%-22s %s\n' "example" "verdict"
fail=0
emitted=0
for name in "${CORPUS[@]}"; do
  main="examples/$name/main.bang"
  wat="$outdir/$name.wat"
  exp="examples/$name/expected.txt"
  [ -f "$main" ] || { echo "FAIL: missing example $main"; exit 2; }
  [ -f "$exp" ]  || { echo "FAIL: missing expected.txt for $name"; exit 2; }

  # Emit + capture the full-shape oracle. Guard the exit (a crashed emitter must not read as green).
  set +e
  report="$("$bin" --print "$main" "$wat" 2>/dev/null)"
  emit_rc=$?
  set -e
  [ "$emit_rc" -eq 0 ] || { echo "FAIL: rung4-shape --print crashed on $name"; echo "$report"; exit 2; }

  oracle="$(printf '%s\n' "$report" | grep -oE 'valPretty = .*' | head -1 | sed 's/^valPretty = //')"
  if printf '%s\n' "$report" | grep -qiE 'EMIT-REFUSED|LOWER-ERROR'; then
    echo "FAIL: emitter refused/errored on $name:"; printf '%s\n' "$report" | grep -iE 'REFUSED|ERROR' | head -3
    exit 2
  fi
  [ -f "$wat" ] || { echo "FAIL: no .wat emitted for $name"; exit 2; }
  emitted=$((emitted + 1))

  set +e
  engine="$(nix shell nixpkgs#wasmtime -c wasmtime run -W gc=y,function-references=y,exceptions=y "$wat" 2>/dev/null)"
  wt_rc=$?
  set -e
  [ "$wt_rc" -eq 0 ] || engine="ENGINE-ERR(rc=$wt_rc)"

  # Gate against expected.txt (the SoT). Also cross-check the wasm oracle line equals expected's
  # content (guards a drifted --print oracle). expected.txt carries a trailing newline (println);
  # the readback module emits one too, so compare byte-exact.
  expected="$(cat "$exp")"
  engine_trimmed="${engine}"
  if [ "$engine_trimmed" = "$expected" ] && [ "$oracle" = "$expected" ]; then
    verdict="OK"
  else
    verdict="MISMATCH"; fail=1
  fi
  printf '%-22s %s\n' "$name" "$verdict"
  if [ "$verdict" = "MISMATCH" ]; then
    echo ""; echo "!! MISMATCH on $name"
    echo "   wasmtime stdout : [$engine_trimmed]"
    echo "   --print oracle  : [$oracle]"
    echo "   expected.txt    : [$expected]"
    echo ""
  fi
done

# False-green guard: assert the corpus is not silently short.
if [ "$emitted" -lt "$MIN_EMITTED" ]; then
  echo "FAIL: only $emitted programs emitted, expected ≥ $MIN_EMITTED (corpus too small)"
  exit 2
fi

echo ""
echo "corpus: $emitted whole programs → WasmGC → wasmtime (WASI readback) → diffed vs expected.txt"
if [ "$fail" -eq 0 ]; then
  echo "PASS — all $emitted programs' READBACK matched bang run's output (incl. caesar's Str result)."
else
  echo "FAIL — at least one readback/expected mismatch (see MISMATCH block(s) above)."
fi
exit "$fail"
