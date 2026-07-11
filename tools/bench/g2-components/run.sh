#!/usr/bin/env bash
# tool: role=bench couples=docs/notes/wasm-concurrency-survey.md runs-in=manual
source "$(git rev-parse --show-toplevel 2>/dev/null)/tools/tool-log.sh" 2>/dev/null && tool_log "$(basename "$0")" || true
# run.sh — the G2 measurement harness (issue #116).
# ──────────────────────────────────────────────────────────────────────────────
# Answers two orders-of-magnitude questions the wasm-concurrency survey §G2 left
# unverified, so the "components-as-actors is DEFERRED" call rests on numbers:
#
#   (1) INSTANTIATION COST — is a component instance µs-cheap (green-thread-
#       plausible) or ms-coarse (a deployment unit)?  Measured cold + warm,
#       default vs pooling allocator, trivial vs stateful (mem+table+global).
#
#   (2) CANONICAL-ABI COPY TAX — what does a GC/collection value cost to cross a
#       typed component boundary vs an intra-component call?  Measured over a
#       small flat message (tuple), and list<u32> at 1 / 1k / 100k, against a
#       no-cross baseline (same compute, list built internally).
#
# The engine is built ONCE and each component compiled ONCE; the driver times
# only the operation under test (Instance::new / a component call), so process +
# JIT startup never pollute the µs numbers — the wasmtime CLI cannot do this.
#
# Requires (all via nixpkgs, no repo dev-shell needed):
#   wasm-tools  (WAT -> component .wasm)     nix shell nixpkgs#wasm-tools
#   wasmtime crate (the driver's engine)     nix shell nixpkgs#cargo nixpkgs#rustc
# Pinned versions are printed in the header so the numbers are reproducible.
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
wat="$here/wat"
drv="$here/driver"
build="$here/.build"
mkdir -p "$build"

run() { nix shell nixpkgs#wasm-tools nixpkgs#cargo nixpkgs#rustc -c bash -c "$1"; }

echo "── G2 component-cost bench ──────────────────────────────────────────────"
run 'echo "wasm-tools: $(wasm-tools --version)"; echo "rustc:      $(rustc --version)"'
echo "wasmtime crate: $(grep '^wasmtime' "$drv/Cargo.toml" | head -1)"
echo

# 1. Build components from WAT (source of truth = the .wat; .wasm are generated).
echo "building components from wat/ ..."
for f in trivial stateful list_sum copyonly baseline tuple; do
  run "wasm-tools parse '$wat/$f.wat' -o '$build/$f.wasm'"
  run "wasm-tools validate --features component-model '$build/$f.wasm'"
done

# 2. Build the driver once (release).
echo "building driver ..."
run "cd '$drv' && cargo build --release --target-dir '$build/target' 2>&1 | tail -1"
D="$build/target/release/g2-driver"

echo
echo "════ (1) INSTANTIATION COST (µs/instance) ════"
printf '%-24s %10s %10s\n' "config" "cold_us" "warm_us"
for cfg in default pool; do
  if [ "$cfg" = pool ]; then export G2_POOL=1; else unset G2_POOL; fi
  for comp in trivial stateful; do
    out="$("$D" instantiate "$build/$comp.wasm" 10000)"
    cold="$(echo "$out" | awk '/cold_us/{print $3}')"
    warm="$(echo "$out" | awk '/warm_us/{print $3}')"
    printf '%-24s %10s %10s\n' "$cfg / $comp" "$cold" "$warm"
  done
done
unset G2_POOL

echo
echo "════ (2) CANONICAL-ABI COPY TAX (µs/call) ════"
printf '%-28s %12s   %s\n' "case" "us_per_call" "result"
call() { # <label> <wasm> <export> <iters> [G2_LIST]
  local label="$1" w="$2" ex="$3" it="$4" ll="${5:-}"
  local out; out="$(G2_LIST="$ll" "$D" copytax "$build/$w.wasm" "$ex" "$it")"
  local us res; us="$(echo "$out" | awk '{print $4}')"; res="$(echo "$out" | sed 's/.*result=//')"
  printf '%-28s %12s   %s\n' "$label" "$us" "$res"
}
call "floor: empty run()"         trivial   run       20000
call "small msg: tuple<u32,u32>"  tuple     sum-tup   20000
call "copy-only list=1"           copyonly  copy-only 3000  1
call "copy-only list=1000"        copyonly  copy-only 3000  1000
call "copy-only list=100000"      copyonly  copy-only 3000  100000
call "copy+sum list=1000"         list_sum  sum-list  3000  1000
call "copy+sum list=100000"       list_sum  sum-list  3000  100000
call "no-cross list=1000"         baseline  sum-internal 3000 1000
call "no-cross list=100000"       baseline  sum-internal 3000 100000

echo
echo "note: copy-only isolates the ABI copy-in; subtract no-cross from copy+sum"
echo "      for the boundary-attributable delta. ~4 ns/element (linear memcpy class)."
