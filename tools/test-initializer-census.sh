#!/usr/bin/env bash
# tool: role=test couples=Main.lean,Bang/Frontend/Query.lean,Bang/Frontend/TypeCheck.lean,examples/*/main.bang runs-in=verify
source "$(git rev-parse --show-toplevel 2>/dev/null)/tools/tool-log.sh" 2>/dev/null && tool_log "$(basename "$0")" || true
# test-initializer-census.sh — pin the honest syntax census and the two row-fact stop conditions.
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

tmpdir="$(mktemp -d)"
trap 'rm -rf "$tmpdir"' EXIT
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
