#!/usr/bin/env bash
# tool: role=bench couples=docs/notes/wasm-concurrency-survey.md runs-in=manual
source "$(git rev-parse --show-toplevel 2>/dev/null)/tools/tool-log.sh" 2>/dev/null && tool_log "$(basename "$0")" || true
# run.sh — the WASI-0.3 async spike (Q(conc-3) / G8, the ADR-0101 backend gate).
# ──────────────────────────────────────────────────────────────────────────────
# Answers the four spike questions the G2 bench explicitly did NOT cover:
#
#   1. TOOLING REALITY 2026 — can today's toolchain (wasmtime 45 / wasm-tools
#      1.249) BUILD and RUN a component using the WASI-0.3 async ABI
#      (async func / stream / future, the task/subtask canon builtins)?
#      Proven three ways below: WIT round-trip, async-lift validate, END-TO-END RUN.
#
#   2. ASYNC LIFT/LOWER OVERHEAD — µs/call of an async-lifted export (task alloc +
#      host event-loop drive + task.return + subtask teardown) vs a sync-lifted
#      export returning the same value. The delta IS the async bookkeeping.
#
#   3/4. MODEL FIT + VERDICT — reasoned in the survey §G8-SPIKE addendum against
#      the actual canon-builtin vocabulary this script enumerates.
#
# The engine is built ONCE and each component compiled ONCE; the Rust driver
# (wasmtime crate, mirrors tools/bench/g2-components/driver) times only the call
# under test, so process + JIT startup never pollute the µs numbers.
#
# Requires (all via nixpkgs, no repo dev-shell needed):
#   wasm-tools     (WAT/WIT -> component .wasm)   nix shell nixpkgs#wasm-tools
#   wasmtime       (CLI, the end-to-end RUN gate) nix shell nixpkgs#wasmtime
#   cargo + rustc  (the timing driver, crate 45)  nix shell nixpkgs#cargo nixpkgs#rustc
# Pinned versions are printed in the header so the numbers are reproducible.
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
wat="$here/wat"
fix="$here/fixtures"
drv="$here/driver"
build="$here/.build"
mkdir -p "$build"

tools() { nix shell nixpkgs#wasm-tools nixpkgs#wasmtime -c bash -c "$1"; }
rust()  { nix shell nixpkgs#cargo nixpkgs#rustc -c bash -c "$1"; }

echo "── WASI-0.3 async spike (Q(conc-3)/G8) ──────────────────────────────────"
tools 'echo "wasm-tools: $(wasm-tools --version)"; echo "wasmtime:   $(wasmtime --version)"'
echo "wasmtime crate: $(grep '^wasmtime' "$drv/Cargo.toml" | head -1)"
echo

# ── Q1a · WIT round-trip: async func / stream<u8> / future<u32> ───────────────
echo "════ Q1a · WIT type layer round-trips (async func / stream / future) ════"
for f in async stream_future; do
  echo "-- $fix/$f.wit --"
  tools "wasm-tools component wit '$fix/$f.wit' --wasm -o '$build/$f-wit.wasm' \
         && wasm-tools print '$build/$f-wit.wasm' | grep -iE 'async|stream|future' | head -4"
done
echo

# ── Q1b · async-lift builds + validates ──────────────────────────────────────
echo "════ Q1b · async-lifted component builds + validates ════"
for f in sync_ret async_ret; do
  tools "wasm-tools parse '$wat/$f.wat' -o '$build/$f.wasm' \
         && wasm-tools validate --features all '$build/$f.wasm' \
         && echo '  $f.wasm: valid'"
done
echo

# ── Q1c · END-TO-END RUN on wasmtime 45 (the CLI, the real event loop) ────────
echo "════ Q1c · async component RUNS on wasmtime 45 (returns 42) ════"
echo -n "  wasmtime CLI async run -> "
tools "wasmtime run -W component-model-async=y --invoke 'run()' '$build/async_ret.wasm'"
echo

# ── async canon-builtin vocabulary the toolchain implements ───────────────────
echo "════ async canon builtins present in wasm-tools 1.249 (parser vocabulary) ════"
printf '(component (core func $x (canon %s)))\n' "definitely-not-a-builtin" > "$build/probe.wat"
tools "wasm-tools parse '$build/probe.wat' -o /dev/null 2>&1 | grep -oE 'task.return|stream.new|stream.read|stream.write|future.new|future.read|future.write|waitable-set.wait|waitable-set.poll|subtask.drop|context.get|thread.yield|backpressure.inc|error-context.new' | sort -u | tr '\n' ' '"
echo; echo

# ── Q2 · async lift/lower overhead vs sync floor ─────────────────────────────
echo "════ Q2 · async lift/lower overhead (build driver once, then measure) ════"
echo "building driver (wasmtime crate 45) ..."
rust "cd '$drv' && cargo build --release --target-dir '$build/target' 2>&1 | tail -1"
D="$build/target/release/wasi-async-driver"

printf '%-14s %14s   %s\n' "path" "us_per_call" "result"
for rep in 1 2 3; do
  s="$("$D" call-sync  "$build/sync_ret.wasm"  run 500000)"
  a="$("$D" call-async "$build/async_ret.wasm" run 500000)"
  printf '%-14s %14s   %s\n' "sync  (rep$rep)"  "$(echo "$s" | awk '{print $4}')" "$(echo "$s" | sed 's/.*result=//')"
  printf '%-14s %14s   %s\n' "async (rep$rep)"  "$(echo "$a" | awk '{print $4}')" "$(echo "$a" | sed 's/.*result=//')"
done
echo
echo "note: async delta = async - sync = the task alloc + event-loop drive +"
echo "      task.return + subtask teardown for a task that completes immediately."
echo "      Settled figures (workstation, x86-64): sync ~0.47-0.49 us, async"
echo "      ~1.16-1.22 us -> ~0.7 us async bookkeeping (~2.4x the sync floor)."
