#!/usr/bin/env bash
# tool: role=test couples=Main.lean,Bang/Frontend/Query.lean,Bang/Frontend/TypeCheck.lean,examples/*/main.bang runs-in=verify
source "$(git rev-parse --show-toplevel 2>/dev/null)/tools/tool-log.sh" 2>/dev/null && tool_log "$(basename "$0")" || true
# test-initializer-census.sh — pin the syntax census, row stop conditions, and inert-contract probe.
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

check_eq "corpus accounting" "61" "${#mains[@]}"

census_out="$("$bang" internal initializer-census "${mains[@]}")"
census_rows="$(printf '%s\n' "$census_out" | wc -l | tr -d ' ')"
check_eq "census row accounting" "62" "$census_rows"

census_total="$(printf '%s\n' "$census_out" | tail -n 1)"
census_want="initializer-census total requested-subjects=61 resolved-subjects=61 empty-subjects=40 definition-only-subjects=7 computation-subjects=14 manifest-values=233 recursive-definitions=24 computation-forms=17 strict-initializers=274"
check_eq "one-sided syntax census" "$census_want" "$census_total"

# Pre-decision kill shot for the proposed inert-top-level contract. Pin exact identities, not only
# the count: all 61 actor journeys may refuse only nqueens' three entry-local computed constants.
contract_probe="$($bang internal initializer-contract-probe "${mains[@]}")"
contract_probe_rows="$(printf '%s\n' "$contract_probe" | sed -n 's/^initializer-contract-probe subject=\([^ ]*\) module=\([^ ]*\) name=\(.*\)$/\1:\2:\3/p' | paste -sd '|' -)"
contract_probe_total="$(printf '%s\n' "$contract_probe" | tail -n 1)"
check_eq "inert-contract exact corpus refusals" \
  "examples/nqueens/main.bang:@entry:q4|examples/nqueens/main.bang:@entry:q5|examples/nqueens/main.bang:@entry:q6" \
  "$contract_probe_rows"
check_eq "inert-contract corpus accounting" \
  "initializer-contract-probe total requested-subjects=61 resolved-subjects=61 would-refuse=3" \
  "$contract_probe_total"

tmpdir="$(mktemp -d)"
trap 'rm -rf "$tmpdir"' EXIT

# Enforcement-grade constructor pole: named ctor applications with inert payloads are descriptions,
# both in a library and beside main. Ordinary computed non-main bindings remain the exact refusals;
# main itself remains executable under option A.
mkdir -p "$tmpdir/contract-probe"
cat > "$tmpdir/contract-probe/Lib.bang" <<'BANG'
pub let wrapped = Some(3)
pub let empty : Option Int = None
pub let computed = 1 + 2
pub let computedWrapped = Some(1 + 2)
BANG
cat > "$tmpdir/contract-probe/main.bang" <<'BANG'
use Lib (wrapped, computed)
-- Constructor resolution deliberately precedes ordinary-variable lookup. This same-named inert
-- binding therefore cannot spoof the classifier: if Some(4) were treated as an application of
-- this thunk, full elaboration below would reject it as a non-function. It instead remains the
-- authoritative Option constructor and the probe accepts it for that exact reason.
let Some = {40 + 2}
let localWrapped = Some(4)
let localComputed = 3 + 4
let main = match wrapped { Some(x) -> x + computed, None -> localComputed }
BANG
fixture_probe="$($bang internal initializer-contract-probe "$tmpdir/contract-probe/main.bang")"
fixture_probe_rows="$(printf '%s\n' "$fixture_probe" | sed -n 's/^initializer-contract-probe subject=.* module=\([^ ]*\) name=\(.*\)$/\1::\2/p' | paste -sd '|' -)"
fixture_probe_total="$(printf '%s\n' "$fixture_probe" | tail -n 1)"
check_eq "inert-contract constructor values stay legal" \
  "Lib::Lib_computed|Lib::Lib_computedWrapped|@entry::localComputed" "$fixture_probe_rows"
check_eq "inert-contract fixture accounting" \
  "initializer-contract-probe total requested-subjects=1 resolved-subjects=1 would-refuse=3" \
  "$fixture_probe_total"

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

# Public DeclFact rows are WHOLE query-projection rows. The divergent initializer taints even the
# textually earlier/later manifest values; this is deliberately not interpreted as five local Divs.
taint_rows="$("$bang" query dump "$tmpdir/strict-initializer.bang" | jq -r '[.decls[] | .name + ":" + (.row // "null")] | join(",")')"
check_eq "chain-cumulative row pole" "before:{Div},loop:{Div},divergent:{Div},after:{Div},main:{Div}" "$taint_rows"

# The second stop condition: a runnable generic let-rec can lose its bare query projection. Keep
# both sides pinned so a future repair cannot be mistaken for a runtime regression or silently skip.
list_run="$("$bang" run examples/list-basics/main.bang)"
check_eq "generic let-rec still runs" "302" "$list_run"

length_fact="$("$bang" query type examples/list-basics/main.bang length)"
check_eq "generic let-rec row gap" '{"ok":false,"error":"unbound variable length"}' "$length_fact"

# Complete resolved-corpus coverage is 273/274 today. Count occurrences, not unique definitions:
# imported declarations intentionally recur once per consuming actor journey.
dump_stream="$(for main in "${mains[@]}"; do "$bang" query dump "$main"; done)"
coverage="$(printf '%s\n' "$dump_stream" | jq -s -c '{strict:([.[].decls[]|select(.kind=="let" or .kind=="letRec")]|length),known:([.[].decls[]|select((.kind=="let" or .kind=="letRec") and .row!=null)]|length),gaps:([.[].decls[]|select((.kind=="let" or .kind=="letRec") and .row==null)|{name,kind,typeError}] )}')"
coverage_want='{"strict":274,"known":273,"gaps":[{"name":"length","kind":"letRec","typeError":"unbound variable length"}]}'
check_eq "row coverage stop condition" "$coverage_want" "$coverage"

echo "──────────────────────────────"
echo "initializer census: $pass passed, $fail failed"
[ "$fail" -eq 0 ]
