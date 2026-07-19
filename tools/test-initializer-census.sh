#!/usr/bin/env bash
# tool: role=test couples=Main.lean,Bang/Frontend/Query.lean,Bang/Frontend/TypeCheck.lean,examples/*/main.bang runs-in=verify
source "$(git rev-parse --show-toplevel 2>/dev/null)/tools/tool-log.sh" 2>/dev/null && tool_log "$(basename "$0")" || true
# test-initializer-census.sh — pin the inert-initializer language contract and its census lineage.
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"
bang="${BANG_BIN:-.lake/build/bin/bang}"

if [ -z "${BANG_BIN_FRESH:-}" ]; then
  echo "building bang runner…" >&2
  lake build bang >&2
fi

pass=0
fail=0
mains=(examples/*/main.bang)

check_eq() {
  local label="$1"
  local want="$2"
  local got="$3"
  if [ "$got" = "$want" ]; then
    echo "✓ $label"
    pass=$((pass + 1))
  else
    echo "✗ $label — expected [$want], got [$got]"
    fail=$((fail + 1))
  fi
}

check_contains() {
  local label="$1"
  local needle="$2"
  local got="$3"
  if [[ "$got" == *"$needle"* ]]; then
    echo "✓ $label"
    pass=$((pass + 1))
  else
    echo "✗ $label — expected substring [$needle], got [$got]"
    fail=$((fail + 1))
  fi
}

check_b019_refusal() {
  local label="$1"
  local file="$2"
  local binding="$3"
  local out exit_code
  out="$($bang check "$file" 2>&1)" && exit_code=0 || exit_code=$?
  check_eq "$label exit" "1" "$exit_code"
  check_contains "$label code" "error[B019]" "$out"
  check_contains "$label binding" "top-level initializer '$binding'" "$out"
}

check_eq "corpus accounting" "61" "${#mains[@]}"

census_out="$("$bang" internal initializer-census "${mains[@]}")"
census_rows="$(printf '%s\n' "$census_out" | wc -l | tr -d ' ')"
check_eq "census row accounting" "62" "$census_rows"

census_total="$(printf '%s\n' "$census_out" | tail -n 1)"
census_want="initializer-census total requested-subjects=61 resolved-subjects=61 empty-subjects=40 definition-only-subjects=7 computation-subjects=14 manifest-values=233 recursive-definitions=24 computation-forms=14 strict-initializers=271"
check_eq "one-sided syntax census" "$census_want" "$census_total"

tmpdir="$(mktemp -d)"
trap 'rm -rf "$tmpdir"' EXIT

# Green actor journey: a derived library, zero/one-arity constructor values, eager work behind a
# thunk, constructor-before-variable resolution, and a computed TRAILING entry body. ADR-0118
# distinguishes declaration initialization; it does not make `main` mandatory.
mkdir -p "$tmpdir/contract-legal"
cat > "$tmpdir/contract-legal/Lib.bang" <<'BANG'
pub data Box = Box(Int) deriving (Eq)
pub let wrapped = Some(3)
pub let empty : Option Int = None
pub let delayed = {1 + 2}
pub let boxed = Box(5)
BANG
cat > "$tmpdir/contract-legal/main.bang" <<'BANG'
use Lib (Box, wrapped, empty, delayed, boxed)
-- Constructor resolution deliberately precedes ordinary-variable lookup. This same-named inert
-- binding therefore cannot spoof the classifier: if Some(4) were treated as an application of
-- this thunk, full elaboration below would reject it as a non-function. It instead remains the
-- authoritative Option constructor and the probe accepts it for that exact reason.
let Some = {40 + 2}
let localWrapped = Some(4)
match localWrapped { Some(x) -> x, None -> 0 }
BANG
legal_json="$($bang check --json "$tmpdir/contract-legal/main.bang")" && legal_exit=0 || legal_exit=$?
check_eq "inert descriptions + trailing body exit" "0" "$legal_exit"
check_eq "inert descriptions + trailing body json" '{"ok":true,"diagnostics":[]}' "$legal_json"

# Red poles: ordinary eager work, eager ctor payload work, entry-local work, and a library spelling
# `main` all reach B019 before downstream type/lowering errors. Each fixture has exactly one refusal.
mkdir -p "$tmpdir/library-eager"
cat > "$tmpdir/library-eager/Lib.bang" <<'BANG'
pub let computed = 1 + 2
BANG
cat > "$tmpdir/library-eager/main.bang" <<'BANG'
import Lib
0
BANG
check_b019_refusal "library eager initializer" "$tmpdir/library-eager/main.bang" "Lib_computed"

mkdir -p "$tmpdir/ctor-payload-eager"
cat > "$tmpdir/ctor-payload-eager/Lib.bang" <<'BANG'
pub let computedWrapped = Some(1 + 2)
BANG
cat > "$tmpdir/ctor-payload-eager/main.bang" <<'BANG'
import Lib
0
BANG
check_b019_refusal "constructor eager payload" "$tmpdir/ctor-payload-eager/main.bang" "Lib_computedWrapped"

mkdir -p "$tmpdir/entry-eager"
cat > "$tmpdir/entry-eager/main.bang" <<'BANG'
let localComputed = 3 + 4
let main = localComputed
BANG
check_b019_refusal "entry non-main eager initializer" "$tmpdir/entry-eager/main.bang" "localComputed"

mkdir -p "$tmpdir/library-main"
cat > "$tmpdir/library-main/Lib.bang" <<'BANG'
pub let main = 5 + 6
BANG
cat > "$tmpdir/library-main/main.bang" <<'BANG'
import Lib
0
BANG
check_b019_refusal "library main is not distinguished" "$tmpdir/library-main/main.bang" "Lib_main"

mkdir -p "$tmpdir/computed-main"
printf 'let main = 1 + 2\n' > "$tmpdir/computed-main/main.bang"
main_json="$($bang check --json "$tmpdir/computed-main/main.bang")" && main_exit=0 || main_exit=$?
check_eq "computed entry main check exit" "0" "$main_exit"
check_eq "computed entry main check json" '{"ok":true,"diagnostics":[]}' "$main_json"
main_run="$($bang run "$tmpdir/computed-main/main.bang")"
check_eq "computed entry main runs" "3" "$main_run"

cat > "$tmpdir/strict-initializer.bang" <<'BANG'
let before = 1
let rec loop : Int -> Int ! {Div} = fun n => ($loop) n
let divergent = ($loop) 0
let after = 2
let main = after
BANG

strict_census="$("$bang" internal initializer-census "$tmpdir/strict-initializer.bang")"
strict_total="$(printf '%s\n' "$strict_census" | tail -n 1)"
strict_want="initializer-census total requested-subjects=1 resolved-subjects=1 empty-subjects=0 definition-only-subjects=0 computation-subjects=1 manifest-values=3 recursive-definitions=1 computation-forms=1 strict-initializers=5"
check_eq "strict witness syntax tie-back" "$strict_want" "$strict_total"

# The old asymmetric-execution pole is now unrepresentable for valid programs. Keep its exact source
# shape, but require B019 before cumulative rows or either engine can observe the divergence.
check_b019_refusal "strict initializer is unrepresentable" "$tmpdir/strict-initializer.bang" "divergent"

# `--no-typecheck` skips the type gate, not source-language well-formedness. The same B019 refusal
# must therefore precede evaluator selection on the raw runtime path.
strict_raw="$($bang run --no-typecheck "$tmpdir/strict-initializer.bang" 2>&1)" && strict_raw_exit=0 || strict_raw_exit=$?
check_eq "strict initializer raw path exit" "1" "$strict_raw_exit"
check_contains "strict initializer raw path refusal" "top-level initializer 'divergent' must be an inert description" "$strict_raw"

# Query operations retain structural source facts for an invalid subject, but no checked/core fact may
# survive the contract refusal. Pin that deliberate partial-result behavior instead of leaving it
# accidental for downstream agents.
strict_dump="$($bang query dump "$tmpdir/strict-initializer.bang")"
strict_query_state="$(printf '%s' "$strict_dump" | jq -c '{coreFingerprint,rowsAllNull:([.decls[].row]|all(. == null)),errorsAllB019:([.decls[].typeError]|all(contains("top-level initializer") and contains("divergent") and contains("inert description")))}')"
check_eq "strict initializer query invalidation" '{"coreFingerprint":null,"rowsAllNull":true,"errorsAllB019":true}' "$strict_query_state"

# Aggregate declaration queries remain chain-cumulative for valid programs: the one executable
# declaration (`main`) still wraps every selected declaration and may contribute `{Div}`. This keeps
# ADR-0117's no-per-binding-attribution rule live without relying on now-invalid eager siblings.
cat > "$tmpdir/computed-main-row.bang" <<'BANG'
let before = 1
let rec loop : Int -> Int ! {Div} = fun n => ($loop) n
let after = 2
let main = ($loop) 0
BANG
main_row_state="$($bang query dump "$tmpdir/computed-main-row.bang" | jq -c '[.decls[]|select(.kind=="let" or .kind=="letRec")|{name,row}]')"
check_eq "computed main keeps rows chain-cumulative" '[{"name":"before","row":"{Div}"},{"name":"loop","row":"{Div}"},{"name":"after","row":"{Div}"},{"name":"main","row":"{Div}"}]' "$main_row_state"

# The second stop condition: a runnable generic let-rec can lose its bare query projection. Keep
# both sides pinned so a future repair cannot be mistaken for a runtime regression or silently skip.
list_run="$("$bang" run examples/list-basics/main.bang)"
check_eq "generic let-rec still runs" "302" "$list_run"

length_fact="$("$bang" query type examples/list-basics/main.bang length)"
check_eq "generic let-rec row gap" '{"ok":false,"error":"unbound variable length"}' "$length_fact"

# Complete resolved-corpus coverage is 270/271 today. Count occurrences, not unique definitions:
# imported declarations intentionally recur once per consuming actor journey.
dump_stream="$(for main in "${mains[@]}"; do "$bang" query dump "$main"; done)"
coverage="$(printf '%s\n' "$dump_stream" | jq -s -c '{strict:([.[].decls[]|select(.kind=="let" or .kind=="letRec")]|length),known:([.[].decls[]|select((.kind=="let" or .kind=="letRec") and .row!=null)]|length),gaps:([.[].decls[]|select((.kind=="let" or .kind=="letRec") and .row==null)|{name,kind,typeError}] )}')"
coverage_want='{"strict":271,"known":270,"gaps":[{"name":"length","kind":"letRec","typeError":"unbound variable length"}]}'
check_eq "row coverage stop condition" "$coverage_want" "$coverage"

echo "──────────────────────────────"
echo "initializer census: $pass passed, $fail failed"
[ "$fail" -eq 0 ]
