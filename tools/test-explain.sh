#!/usr/bin/env bash
# tool: role=test couples=Bang/Frontend/DiagCodes.lean runs-in=verify
source "$(git rev-parse --show-toplevel 2>/dev/null)/tools/tool-log.sh" 2>/dev/null && tool_log "$(basename "$0")" || true
# test-explain.sh — the CLI gate for stable diagnostic codes + `bang explain` (plan 013 slice 5).
#
# The registry byte-exactness (codeForMsg / explain lookups) is already gated at the Lean `#guard`
# level (Bang/Frontend/DiagCodes.lean §4). This file gates the CLI SURFACE the #guards never touch:
#   - a TRIGGER program's diagnostic carries the right code end-to-end (`explainCode` in --json,
#     `error[Bxxx]` in the human path) — the retrofit is wired into Main's render, not just the table;
#   - `bang explain CODE` prints the registry teaching entry (summary + example);
#   - `bang explain BOGUS` is a LOUD unknown-code error on stderr, exit 1 (never a silent empty print);
#   - `check --json` carries the `explainCode` field on every diagnostic.
#
# GOTCHA (set -euo pipefail): an unguarded `$(cmd1 | cmd2)` capture can kill this script SILENTLY on a
# nonzero exit from either stage (a truncated false-green). Every capture below runs standalone with an
# explicit `&& … || …` exit-capture, or pipes into `grep` with `|| true`. The FINAL line asserts the
# expected check COUNT, so a silently-truncated run is caught by "did we even reach the count".
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"
bang=".lake/build/bin/bang"

if [ -z "${BANG_BIN_FRESH:-}" ]; then
  echo "building bang runner…" >&2
  lake build bang >&2
fi

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

# `trigger_carries_code SRC CODE` — the diagnostic for SRC carries `"explainCode":"CODE"` in --json.
trigger_carries_code() {
  local src="$1" code="$2"
  local out; out="$(printf '%s' "$src" | "$bang" check --json 2>/dev/null)" || true
  check "trigger-$code-explainCode" \
    "$(printf '%s' "$out" | grep -o "\"explainCode\":\"$code\"" || true)" \
    "\"explainCode\":\"$code\""
}

# ── PER-CODE TRIGGERS: each example-carrying registry code fires end-to-end through --json ──
# (the SRC strings mirror the registry's own `example?` fields — kept in sync by the shared design;
#  a drift there fails the DiagCodes #guards or this battery, never silently).
trigger_carries_code 'let let = 3 in let'                         'B001'
trigger_carries_code 'effect E { get : Int -> Int }
let main = 3'                                                     'B002'
trigger_carries_code 'let x = 3 in $x'                            'B004'
trigger_carries_code '1, 2'                                       'B008'
trigger_carries_code 'data List a = Nil | Cons(a, List a)
data IntList = Nil | Cons(Int, IntList)
Nil'                                                               'B012'
trigger_carries_code 'let rec outer : Int -> Int ! {Div} = fun n => let rec a : Int -> Int ! {Div} = fun m => ($b) m in let rec b : Int -> Int ! {Div} = fun m => ($a) m in ($a) n in ($outer) 3' 'B013'
trigger_carries_code 'let x = 3
let main = 4
x + main
data Marker = M
0'                                                                   'B016'
trigger_carries_code 'let rec passThroughOpt : Option a -> Option a = fun o => o in ($passThroughOpt (Some(3) : Option Int) : Option Char)' 'B017'
trigger_carries_code 'let eager = 1 + 2
let main = eager'                                                 'B019'

# ── B011 RETIRED (#144): its FORMER trigger now type-checks CLEAN, no diagnostic at all — the
# positive regression for the payload-arity-≤2 cap being lifted (a ≥3-ary ctor constructs/matches
# fine end-to-end, not just "some other code fires now"). ──
b011_former_trigger="$(printf 'data T = C(Int, Int, Int)\nlet main = 3' | "$bang" check --json 2>/dev/null)" && b011_exit=0 || b011_exit=$?
check "b011-retired-former-trigger-exit" "$b011_exit" "0"
check "b011-retired-former-trigger-now-clean" "$b011_former_trigger" '{"ok":true,"diagnostics":[]}'

# ── the HUMAN path prefixes the stable code (rustc `error[B004]:` shape) ──
human_err="$(printf 'let x = 3 in $x' | "$bang" check 2>&1 >/dev/null)" || true
if [[ "$human_err" == *"error[B004]"* ]]; then
  echo "✓ human-path-code-prefix"; pass=$((pass + 1))
else
  echo "✗ human-path-code-prefix — expected 'error[B004]', got [$human_err]"; fail=$((fail + 1))
fi

# an UNCODED diagnostic still gets the plain `error` prefix (no bogus code invented) + explainCode:null.
human_uncoded="$(printf 'let x 3 in x' | "$bang" check 2>&1 >/dev/null)" || true
if [[ "$human_uncoded" == error\ at* || "$human_uncoded" == error:* ]]; then
  echo "✓ human-path-uncoded-plain-error"; pass=$((pass + 1))
else
  echo "✗ human-path-uncoded-plain-error — expected a plain 'error' prefix, got [$human_uncoded]"; fail=$((fail + 1))
fi
json_uncoded="$(printf 'let x 3 in x' | "$bang" check --json 2>/dev/null)" || true
check "json-uncoded-explainCode-null" \
  "$(printf '%s' "$json_uncoded" | grep -o '"explainCode":null' || true)" '"explainCode":null'

# ── a CLEAN program has no diagnostics (no explainCode field to assert), exit 0 ──
clean_out="$(printf 'let x = 3 in x' | "$bang" check --json 2>/dev/null)" && clean_exit=0 || clean_exit=$?
check "clean-ok-true" "$clean_out" '{"ok":true,"diagnostics":[]}'
check "clean-exit" "$clean_exit" "0"

# ── `bang explain CODE` prints the registry entry (summary line + the teaching + the example) ──
exp_out="$("$bang" explain B004 2>/dev/null)" && exp_exit=0 || exp_exit=$?
check "explain-exit-0" "$exp_exit" "0"
check "explain-summary-line" \
  "$(printf '%s' "$exp_out" | head -1)" \
  "B004: forcing (\`\$\`) a value that is not a thunk"
if printf '%s' "$exp_out" | grep -q 'the only way to observe one'; then
  echo "✓ explain-teaching-text"; pass=$((pass + 1))
else
  echo "✗ explain-teaching-text — teaching body missing"; fail=$((fail + 1))
fi
if printf '%s' "$exp_out" | grep -q 'Triggering example:'; then
  echo "✓ explain-shows-example"; pass=$((pass + 1))
else
  echo "✗ explain-shows-example — example section missing"; fail=$((fail + 1))
fi

# ── explain is CASE-INSENSITIVE on the code ──
exp_lower_out="$("$bang" explain b004 2>/dev/null)" && exp_lower_exit=0 || exp_lower_exit=$?
exp_lower="${exp_lower_out%%$'\n'*}"
check "explain-case-insensitive-exit" "$exp_lower_exit" "0"
check "explain-case-insensitive" "$exp_lower" "B004: forcing (\`\$\`) a value that is not a thunk"

# ── `bang explain BOGUS` is a LOUD unknown-code error on stderr, exit 1 (never silent) ──
"$bang" explain B999 >/dev/null 2>&1 && bogus_exit=0 || bogus_exit=$?
check "explain-bogus-exit-1" "$bogus_exit" "1"
bogus_stdout="$("$bang" explain B999 2>/dev/null)" || true
check "explain-bogus-stdout-empty" "$bogus_stdout" ""
bogus_stderr="$("$bang" explain B999 2>&1 >/dev/null)" || true
if [[ "$bogus_stderr" == *"unknown diagnostic code"* ]]; then
  echo "✓ explain-bogus-stderr-loud"; pass=$((pass + 1))
else
  echo "✗ explain-bogus-stderr-loud — expected 'unknown diagnostic code', got [$bogus_stderr]"; fail=$((fail + 1))
fi

# ── explain with no arg / too many args is a usage error, exit 1 ──
"$bang" explain >/dev/null 2>&1 && noarg_exit=0 || noarg_exit=$?
check "explain-no-arg-exit-1" "$noarg_exit" "1"

echo "──────────────────────────────"
echo "explain: $pass passed, $fail failed"
want_total=26
got_total=$((pass + fail))
if [ "$got_total" -ne "$want_total" ]; then
  echo "✗ check-count-mismatch — expected $want_total checks to run, only $got_total did (script truncated?)"
  exit 1
fi
[ "$fail" -eq 0 ]
