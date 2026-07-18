#!/usr/bin/env bash
# tool: role=test couples=Main.lean,Bang/Backend/WasmEmit.lean runs-in=verify
source "$(git rev-parse --show-toplevel 2>/dev/null)/tools/tool-log.sh" 2>/dev/null && tool_log "$(basename "$0")" || true
# test-bang-build.sh — the CLI gate for `bang build` (issue #136 productized).
#
# `bang build <file> [-o out.wasm] [--component]` is the distribution artifact: emit → `wasm-tools
# parse`/`validate` → a runnable Wasm module (the distribution-survey's static story). This battery
# gates that the produced ARTIFACT runs on a real engine (wasmtime) and prints the SAME value the
# example's `expected.txt` oracle records — proof rides the reference (invariant #1) across the
# build+engine boundary, not just the emitter's own #guards.
#
# Corpus (whole example PROGRAMS with an `expected.txt` oracle):
#   json (import-ing multi-module) · factorial (bignum print path) · logger-counting (EFFECTFUL —
#   an in-program handler the GC path lowers) · stateful-quota (ADR-0114 updating custom clause) ·
#   resource-contract (ADR-0116 checked `[0]` erasure + one-shot `[1]`) · reactive-spreadsheet
#   (named State inputs + pull-reactive thunk formulas + explicit stale snapshot) ·
#   reactive-recomputation (100-line in-band full-DAG call measurement) · reactive-observation-reuse
#   (scoped cache freshness plus deliberately retained stale-cache adverse route).
# Each is built to a module, run on wasmtime, and diffed.
# The --component leg additionally wraps json as a WASI component (via the pinned preview1 adapter,
# fetched to a cache) and asserts the component prints the same value — the full static story.
#
# TOOLCHAIN: `wasm-tools` + `wasmtime` are NOT in the dev shell (nor the flake) — this battery pulls
# them via `nix shell nixpkgs#…` (same as the emit-*-diff.sh harnesses). So it is enrolled in verify
# but SELF-SKIPS LOUD (exit 0) when either tool is unreachable (offline / no nix), rather than
# failing the network-free gate. Where the tools ARE present (CI, or a dev with them) it runs FULL.
#
# GOTCHA (set -euo pipefail): every `$(cmd | cmd)` capture is guarded (standalone with `|| true` or
# an explicit exit-capture); the FINAL line asserts the expected check COUNT so a silently-truncated
# run is caught. A SKIP short-circuits BEFORE the count (its own clean exit 0).
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"
bang=".lake/build/bin/bang"

if [ -z "${BANG_BIN_FRESH:-}" ]; then
  echo "building bang runner…" >&2
  lake build bang >&2
fi

# ── toolchain gate: resolve wasm-tools + wasmtime once, via a single nix shell. If unreachable,
# SKIP LOUD (exit 0). We resolve real paths so the rest of the script needs no nix shell per call. ──
WT_BIN=""; WASMTIME_BIN=""
if command -v wasm-tools >/dev/null 2>&1 && command -v wasmtime >/dev/null 2>&1; then
  WT_BIN="$(command -v wasm-tools)"; WASMTIME_BIN="$(command -v wasmtime)"
elif command -v nix >/dev/null 2>&1; then
  # one nix shell resolves both tool paths; a failure here (offline) trips the skip below.
  resolved="$(nix shell nixpkgs#wasm-tools nixpkgs#wasmtime -c bash -c 'command -v wasm-tools; command -v wasmtime' 2>/dev/null || true)"
  WT_BIN="$(printf '%s\n' "$resolved" | sed -n '1p')"
  WASMTIME_BIN="$(printf '%s\n' "$resolved" | sed -n '2p')"
fi
if [ -z "$WT_BIN" ] || [ -z "$WASMTIME_BIN" ] || [ ! -x "$WT_BIN" ] || [ ! -x "$WASMTIME_BIN" ]; then
  echo "SKIP test-bang-build: wasm-tools / wasmtime not reachable (no dev-shell entry, no network for nix shell)." >&2
  echo "  This battery runs FULL wherever both tools are present (CI, or \`nix shell nixpkgs#wasm-tools nixpkgs#wasmtime\`)." >&2
  exit 0
fi
# `bang build` shells to a BARE `wasm-tools` on $PATH — so put the resolved tool dirs on PATH for
# every `bang build` invocation below (the nix-shell store paths, when we resolved via nix).
wt_dir="$(dirname "$WT_BIN")"
wasmtime_dir="$(dirname "$WASMTIME_BIN")"
export PATH="$wt_dir:$wasmtime_dir:$PATH"

WT_FLAGS="-W gc=y,function-references=y,exceptions=y"
outdir="$(mktemp -d)"
trap 'rm -rf "$outdir"' EXIT

pass=0
fail=0
check() {
  local name="$1" got="$2" want="$3"
  if [ "$got" = "$want" ]; then
    echo "✓ $name"; pass=$((pass + 1))
  else
    echo "✗ $name — expected [$want], got [$got]"; fail=$((fail + 1))
  fi
}

# `build_and_run NAME [--component]` — `bang build` the example, run the artifact on wasmtime, and
# check its stdout == examples/NAME/expected.txt. The build's own exit is guarded explicitly.
build_and_run() {
  local name="$1"; shift
  local extra=("$@")
  local main="examples/$name/main.bang"
  local exp; exp="$(cat "examples/$name/expected.txt" 2>/dev/null | head -1)"
  local out="$outdir/$name.wasm"

  set +e
  build_err="$("$bang" build "$main" -o "$out" "${extra[@]}" 2>&1 >/dev/null)"
  build_rc=$?
  set -e
  if [ "$build_rc" -ne 0 ]; then
    check "build-$name-rc0" "rc=$build_rc: $build_err" "rc=0"
    return
  fi
  check "build-$name-rc0" "rc=$build_rc" "rc=0"
  [ -f "$out" ] || { check "build-$name-artifact" "missing" "$out"; return; }

  set +e
  got="$("$WASMTIME_BIN" run $WT_FLAGS "$out" 2>/dev/null)"
  run_rc=$?
  set -e
  if [ "$run_rc" -ne 0 ]; then
    check "run-$name-rc0" "rc=$run_rc" "rc=0"; return
  fi
  check "run-$name-value" "$got" "$exp"
}

echo "── MODULE form: bang build → wasm-tools parse/validate → wasmtime run vs expected.txt ──"
build_and_run json            # import-ing multi-module  → 163
build_and_run factorial       # bignum print path         → 25!
build_and_run logger-counting # EFFECTFUL (in-prog handler) → 3
build_and_run stateful-quota  # EFFECTFUL updating custom clause → 10
build_and_run resource-contract # quantity obligations + dead result-cell erasure → 7
build_and_run reactive-spreadsheet # live formula update + deliberately stale sample → ((22, 26), (22, 22))
build_and_run reactive-recomputation # 100-line full-DAG measurement → ((7050, 401), (7450, 401))
build_and_run reactive-observation-reuse # scoped freshness + retained stale-cache adverse route

# ── default output name: `bang build <file>` with no -o writes <stem>.wasm in CWD ──
echo "── default output name (<stem>.wasm) ──"
repo="$(git rev-parse --show-toplevel)"
absbang="$repo/$bang"
set +e
( cd "$outdir" && "$absbang" build "$repo/examples/json/main.bang" >/dev/null 2>&1 )
def_rc=$?
set -e
check "default-out-rc0" "$def_rc" "0"
check "default-out-name" "$([ -f "$outdir/main.wasm" ] && echo yes || echo no)" "yes"

# ── --component: wrap json as a WASI component (needs the pinned preview1 adapter) ──
echo "── COMPONENT form (WASI component via the pinned preview1 adapter) ──"
adapter="$outdir/wasi_snapshot_preview1.command.wasm"
adapter_url="https://github.com/bytecodealliance/wasmtime/releases/download/v45.0.0/wasi_snapshot_preview1.command.wasm"
have_adapter=no
if command -v curl >/dev/null 2>&1 && curl -fsSL "$adapter_url" -o "$adapter" 2>/dev/null && [ -s "$adapter" ]; then
  have_adapter=yes
elif command -v nix >/dev/null 2>&1 && nix shell nixpkgs#curl -c curl -fsSL "$adapter_url" -o "$adapter" 2>/dev/null && [ -s "$adapter" ]; then
  have_adapter=yes
fi

if [ "$have_adapter" = yes ]; then
  comp="$outdir/json.component.wasm"
  set +e
  BANG_WASI_ADAPTER="$adapter" "$bang" build "examples/json/main.bang" --component -o "$comp" >/dev/null 2>&1
  comp_build_rc=$?
  set -e
  check "component-build-rc0" "$comp_build_rc" "0"
  set +e
  comp_got="$("$WASMTIME_BIN" run $WT_FLAGS "$comp" 2>/dev/null)"
  set -e
  check "component-run-value" "$comp_got" "$(cat examples/json/expected.txt | head -1)"
else
  # No adapter (offline) — assert the LOUD refusal path instead: --component with no adapter fails 1.
  echo "  (adapter unreachable — asserting the loud no-adapter refusal instead of the wrap)" >&2
  set +e
  norefusal="$("$bang" build "examples/json/main.bang" --component -o "$outdir/x.wasm" 2>&1 >/dev/null)"
  norefusal_rc=$?
  set -e
  check "component-no-adapter-rc1" "$norefusal_rc" "1"
  check "component-no-adapter-loud" \
    "$(printf '%s' "$norefusal" | grep -o 'needs the WASI preview1 adapter' || true)" \
    "needs the WASI preview1 adapter"
fi

# ── LOUD failure: a program the GC path cannot lower refuses (never a silent/wrong artifact) ──
# (No such example ships that ALSO fails build cleanly today — the refusal is emit's, gated in the
#  emit harnesses. Here we assert the tool-absence contract is NOT what we hit: build succeeded above.)

echo "──────────────────────────────"
echo "bang build: $pass passed, $fail failed"
# The count varies by the --component branch (both branches emit exactly 2 checks), so the module
# legs (8×2=16) + default-out (2) + component branch (2) = 20 is invariant across online/offline.
want_total=20
got_total=$((pass + fail))
if [ "$got_total" -ne "$want_total" ]; then
  echo "✗ check-count-mismatch — expected $want_total checks, only $got_total ran (script truncated?)"
  exit 1
fi
[ "$fail" -eq 0 ]
