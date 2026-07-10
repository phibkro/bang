#!/usr/bin/env bash
# tool: role=test couples=EmitMain,Bang/Backend/WasmEmit.lean runs-in=manual
source "$(git rev-parse --show-toplevel 2>/dev/null)/tools/tool-log.sh" 2>/dev/null && tool_log "$(basename "$0")" || true
# emit-rung1-diff.sh — the ◊5.5 rung-1 / rung-1.5 EMISSION differential harness.
# ──────────────────────────────────────────────────────────────────────────────
# The first time bang output executes OUTSIDE Lean, now over a GENERATED corpus. For each
# emittable sample (hand anchors + rung-1.5 witnesses + ~50 seed-generated programs):
#   1. `lake exe emit-rung1` writes NAME.wat + prints the `Source.eval` ORACLE value + a
#      machine-parsed report (name/desc/oracle) and EMITTED_COUNT/REFUSED_COUNT footers.
#   2. `wasmtime run --invoke main NAME.wat` runs the emitted core-wasm on a REAL engine.
#   3. diff the two. A mismatch is a LOUD failure (exit 1) that prints the .wat + both values —
#      proof rides the reference (invariant #1), now crossing a real-engine boundary.
#
# rung-1.5 additions: guarded division (kernel `a/0 = 0` vs wasm trapping div_s), and the
# comparison + case-on-bool `if` pattern. See docs/notes/emission-rung1-probe.md §rung-1.5.
# rung-2 additions: `throws` handlers → Wasm-3.0 `try_table`/`throw` (abort → exceptions, ADR-0059).
# These need `-W exceptions=y` on wasmtime (see the invocation below). §rung-2 of the same note.
#
# FALSE-GREEN DEFENSES (repo bash conventions): the emitted count is ASSERTED (a silently-empty
# corpus or a mid-run generator refusal fails LOUD), no unguarded `$(a|b)` capture drives control
# flow, and wasmtime's exit is checked explicitly (never a piped exit code).
#
# Requires: the dev shell (`nix develop`) for `lake`; `wasmtime` via `nix shell nixpkgs#wasmtime`.
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"
outdir="$(mktemp -d)"
trap 'rm -rf "$outdir"' EXIT

# Minimum number of emittable programs the corpus MUST run (hand anchors + rung-1.5 + rung-2 throws
# + generated). A run below this is a FALSE GREEN (empty/short corpus) and fails loud.
MIN_EMITTED="${MIN_EMITTED:-55}"

echo "── building the emit-rung1 spike exe ──"
lake build emit-rung1 >/dev/null 2>&1
bin="$(find .lake/build/bin -name emit-rung1 | head -1)"
[ -n "$bin" ] || { echo "FAIL: emit-rung1 binary not found"; exit 2; }

echo "── emitting .wat + oracle values ──"
# Run the emit exe, capturing its full report to a file (parsed below). Guard the exit code
# explicitly — a crashed emitter must not read as an empty (green) corpus.
if ! "$bin" "$outdir" > "$outdir/report.txt" 2>&1; then
  echo "FAIL: emit-rung1 exe crashed:"; cat "$outdir/report.txt"; exit 2
fi

# Count assertions from the exe's own footers (single source of truth for what it emitted).
emitted="$(grep -E '^EMITTED_COUNT ' "$outdir/report.txt" | awk '{print $2}')"
refused="$(grep -E '^REFUSED_COUNT ' "$outdir/report.txt" | awk '{print $2}')"
[ -n "$emitted" ] || { echo "FAIL: no EMITTED_COUNT footer — emitter output malformed"; cat "$outdir/report.txt"; exit 2; }
echo "emit exe reports: EMITTED=$emitted  REFUSED=$refused  (min required $MIN_EMITTED)"

# The generator stays in-fragment by construction, so ANY refusal signals a generator bug — loud.
if [ "$refused" -ne 0 ]; then
  echo "FAIL: $refused generated/sample program(s) were REFUSED by the emitter (generator drifted out of the emittable fragment):"
  grep 'REFUSED' "$outdir/report.txt" || true
  exit 2
fi

# Assert the corpus is not silently short (false-green defense).
if [ "$emitted" -lt "$MIN_EMITTED" ]; then
  echo "FAIL: only $emitted programs emitted, expected ≥ $MIN_EMITTED — corpus too small (false-green guard)"
  exit 2
fi

# Assert the .wat file count on disk matches the reported emitted count (no lost writes).
wat_count="$(find "$outdir" -maxdepth 1 -name '*.wat' | wc -l | tr -d ' ')"
if [ "$wat_count" -ne "$emitted" ]; then
  echo "FAIL: $wat_count .wat files on disk ≠ $emitted reported emitted (lost/extra writes)"
  exit 2
fi

echo ""
echo "── differential: wasmtime (real engine)  vs  Source.eval (kernel oracle) ──"
printf '%-8s %-42s %12s %12s   %s\n' "sample" "program" "wasmtime" "oracle" "verdict"
fail=0
checked=0
for wat in "$outdir"/*.wat; do
  name="$(basename "$wat" .wat)"
  # EXACT-match the report line for this name (EmitMain prints `NAME  (desc)` — TWO spaces),
  # then the oracle line two lines down. The trailing-space anchor + exact prefix avoid
  # gen1-vs-gen10 prefix collisions. grep failures are made non-fatal (|| true) so a parse
  # miss surfaces as the explicit empty-oracle guard below, not an opaque `set -e` abort.
  desc="$(grep -E "^${name}  \(" "$outdir/report.txt" | head -1 | sed -E "s/^${name} +\((.*)\)$/\1/" || true)"
  oracle="$(grep -A2 -E "^${name}  \(" "$outdir/report.txt" | grep 'oracle:' | head -1 | sed 's/.*= //' || true)"
  [ -n "$oracle" ] || { echo "FAIL: no oracle value parsed for $name (report format drift?)"; exit 2; }

  # Run wasmtime, capturing value + exit code SEPARATELY (never a piped exit code).
  # `-W exceptions=y` enables the Wasm-3.0 exception-handling proposal (try_table/throw) the
  # rung-2 `throws` modules use. Confirmed on wasmtime 45: exceptions are Wasm-3.0 CORE but
  # gated behind this feature flag (not on by default yet); the flag is INERT for the pure
  # rung-1/1.5 modules, so one invocation covers the whole corpus.
  set +e
  engine="$(nix shell nixpkgs#wasmtime -c wasmtime run -W exceptions=y --invoke main "$wat" 2>/dev/null)"
  wt_rc=$?
  set -e
  if [ "$wt_rc" -ne 0 ]; then engine="ENGINE-ERR(rc=$wt_rc)"; fi

  checked=$((checked + 1))
  if [ "$engine" = "$oracle" ]; then
    verdict="OK"
  else
    verdict="MISMATCH"
    fail=1
  fi
  printf '%-8s %-42s %12s %12s   %s\n' "$name" "$desc" "$engine" "$oracle" "$verdict"

  if [ "$verdict" = "MISMATCH" ]; then
    echo ""
    echo "!! MISMATCH on $name — $desc"
    echo "   wasmtime = $engine   oracle(Source.eval) = $oracle"
    echo "   emitted .wat:"
    sed 's/^/     /' "$wat"
    echo ""
  fi
done

# Assert every emitted program was actually differential-checked (no silent skip).
if [ "$checked" -ne "$emitted" ]; then
  echo "FAIL: checked $checked programs but emitter reported $emitted emitted (silent skip)"
  exit 2
fi

echo ""
echo "corpus: $checked programs emitted → wasmtime → diffed vs Source.eval"
if [ "$fail" -eq 0 ]; then
  echo "PASS — all $checked emitted core-wasm modules ran on wasmtime with a value matching Source.eval."
else
  echo "FAIL — at least one engine/oracle mismatch (see MISMATCH block(s) above)."
fi
exit "$fail"
