#!/usr/bin/env bash
# tool: role=test couples=Main.lean,Bang/Frontend/Query.lean,examples/*/main.bang,examples/*/expected.txt runs-in=verify
source "$(git rev-parse --show-toplevel 2>/dev/null)/tools/tool-log.sh" 2>/dev/null && tool_log "$(basename "$0")" || true
# test-slice-fidelity.sh — classify entry-rooted slice execution against the resolved whole program.
#
# The 61-example sweep is positive, corpus-relative evidence at one fixed fuel. The strict-initializer
# fixture is deliberately RED: top-level lets are strict, so pruning an unreachable divergent
# initializer changes execution. That witness prevents body identity from being promoted to standalone
# executability and pins the module-initialization obligation a future link contract must answer.
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"
bang="${BANG_BIN:-.lake/build/bin/bang}"

if [ -z "${BANG_BIN_FRESH:-}" ]; then
  echo "building bang runner…" >&2
  lake build bang >&2
fi

pass=0
fail=0
processed=0
mains=()
names=()
wants=()

for dir in examples/*/; do
  main="${dir}main.bang"
  expected="${dir}expected.txt"
  [ -f "$main" ] || continue
  processed=$((processed + 1))
  name="${dir#examples/}"
  name="${name%/}"
  if [ ! -f "$expected" ]; then
    echo "✗ $name — no expected.txt"
    fail=$((fail + 1))
    continue
  fi
  mains+=("$main")
  names+=("$name")
  wants+=("$(<"$expected")")
done

# One process pays the compiled runner's startup cost once; output remains one line per subject in
# argument order. A nonzero batch status is never allowed to hide which individual line diverged.
if batch_out="$("$bang" internal slice-fidelity "${mains[@]}" 2>&1)"; then
  batch_status=0
else
  batch_status=$?
fi
mapfile -t measurements <<< "$batch_out"
if [ "${#measurements[@]}" -ne "${#mains[@]}" ]; then
  echo "✗ corpus output accounting — got ${#measurements[@]} rows for ${#mains[@]} runnable subjects"
  fail=$((fail + 1))
fi

for i in "${!mains[@]}"; do
  name="${names[$i]}"
  want="${wants[$i]}"
  got="${measurements[$i]:-<missing>}"
  # The source oracle is intentionally exact too. Three existing corpus programs are outside its
  # default-fuel/value lane (the env runner is the product default and owns expected.txt): name those
  # terminals instead of hiding them behind a wildcard.
  case "$name" in
    nqueens) oracle_want="outOfFuel" ;;
    policy-host-allowlist|sched-seeded-lcg) oracle_want="stuck" ;;
    *) oracle_want="done:${want}" ;;
  esac
  line_want="slice-fidelity agree fuel=100000 oracle=${oracle_want} env=done:${want}"
  if [ "$got" = "$line_want" ]; then
    echo "✓ $name"
    pass=$((pass + 1))
  else
    echo "✗ $name — expected [$line_want]; batch-status=$batch_status; got=[$got]"
    fail=$((fail + 1))
  fi
done
if [ "$batch_status" -ne 0 ]; then
  echo "✗ corpus batch exited $batch_status"
  fail=$((fail + 1))
fi

# The fixture family that originally established stable export-body identity also travels through
# the resolver-aware execution apparatus here, tying the two evidence layers together.
tmpdir="$(mktemp -d)"
trap 'rm -rf "$tmpdir"' EXIT
mkdir -p "$tmpdir/tie-back"
cat > "$tmpdir/tie-back/Lib.bang" <<'BANG'
let base : Int = 40
let helper : Int = base + 1
pub let selected : Int = helper
let unrelated : Int = 7
BANG
cat > "$tmpdir/tie-back/main.bang" <<'BANG'
import Lib
let main = Lib.selected
BANG
tie_want="slice-fidelity agree fuel=100000 oracle=done:41 env=done:41"
tie_got="$("$bang" internal slice-fidelity "$tmpdir/tie-back/main.bang")"
if [ "$tie_got" = "$tie_want" ]; then
  echo "✓ body-identity tie-back"
  pass=$((pass + 1))
else
  echo "✗ body-identity tie-back — expected [$tie_want], got [$tie_got]"
  fail=$((fail + 1))
fi

# Determinism belongs to the apparatus even though its text is deliberately not public API.
det_a="$("$bang" internal slice-fidelity examples/handle-custom-nested/main.bang)"
det_b="$("$bang" internal slice-fidelity examples/handle-custom-nested/main.bang)"
if [ "$det_a" = "$det_b" ]; then
  echo "✓ deterministic repeated measurement"
  pass=$((pass + 1))
else
  echo "✗ deterministic repeated measurement — first [$det_a], second [$det_b]"
  fail=$((fail + 1))
fi

# Retained red pole: whole-program strict initialization diverges before reaching `main`; the body
# slice intentionally omits that unreachable initializer and returns. This is not a slicer bug to
# normalize away — it is the witnessed reason `linkReady` remains false.
cat > "$tmpdir/strict-initializer.bang" <<'BANG'
let rec loop : Int -> Int ! {Div} = fun n => ($loop) n
let unused = ($loop) 0
let main = 1
BANG
strict_want="slice-fidelity asymmetric-execution fuel=100000 oracle-whole=outOfFuel oracle-slice=done:1 env-whole=stuck env-slice=done:1"
if strict_got="$("$bang" internal slice-fidelity "$tmpdir/strict-initializer.bang" 2>&1)"; then
  strict_status=0
else
  strict_status=$?
fi
if [ "$strict_status" -eq 1 ] && [ "$strict_got" = "$strict_want" ]; then
  echo "✓ strict-initializer boundary classified"
  pass=$((pass + 1))
else
  echo "✗ strict-initializer boundary — expected status 1 [$strict_want], got status $strict_status [$strict_got]"
  fail=$((fail + 1))
fi

expected_examples=61
if [ "$processed" -ne "$expected_examples" ]; then
  echo "✗ corpus accounting — processed $processed examples, expected $expected_examples"
  fail=$((fail + 1))
fi

echo "──────────────────────────────"
echo "slice fidelity classification: $pass passed, $fail failed ($processed corpus examples)"
[ "$fail" -eq 0 ]
