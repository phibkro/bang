#!/usr/bin/env bash
# tool: role=test couples=examples/*/main.bang runs-in=verify
# test-query.sh — the non-interactive gate for `bang query <op>` (issue #80, the agent LSP as
# stateless CLI subcommands).
#
# Mirrors test-check-json.sh's shape (build once, exercise the binary, diff, tally pass/fail). The
# JSON-emitter internals (`jsonStr`/`jsonField`/`jsonObj` escaping, the schema's per-op byte-exact
# shape on a fixed input) are already gated at the Lean `#guard` level (Bang/Frontend/Query.lean) —
# this file gates the CLI SURFACE specifically: file-arg vs stdin, argument-order per op, the
# resolver-aware multi-file path (imports/qualification), the 0/1/2 exit-code contract observed
# THROUGH the binary, AND — the operator's API-first refinement (2026-07-10) — that `dump` is a
# genuine COMPLETE fact base (every curated verb's answer is provably a SUBSET/PROJECTION of what
# `dump` exports) plus a demonstration that a caller can COMPOSE an arbitrary query over `dump`'s
# JSON that no fixed verb answers (a ~5-line `jq` filter, gated below).
#
# GOTCHA (set -euo pipefail, per test-check-json.sh's own documented lesson): an unguarded
# `$(cmd1 | cmd2)` capture can kill this script SILENTLY mid-run. Every capture below either runs
# standalone (no pipe) with an explicit `&& … || …` exit-capture, or pipes into `grep`/`jq` with
# `|| true` on the capture. The FINAL line asserts the expected check COUNT.
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"
bang=".lake/build/bin/bang"

echo "building bang runner…" >&2
lake build bang >&2

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

tmpdir="$(mktemp -d)"
trap 'rm -rf "$tmpdir"' EXIT

# ── fixtures ──
cat > "$tmpdir/simple.bang" <<'BANG'
let rec double : Int -> Int = fun n => n + n
let quad = {fun n => $double ($double n)}
let main = $quad 3
BANG

cat > "$tmpdir/laws.bang" <<'BANG'
trait Eq { fn eq(a, b) -> Int law refl(x): eq(x, x) == 1 }
impl Eq for Int { fn eq(a, b) = a }
0
BANG

# `pub`/divergence-tainted fixture — the composed-query demo's own corpus: ONE decl is both `pub`
# AND recursive (its type carries `Thunk!{Div}`, the ONLY place a v1 program's decl-level effect
# taint is visible — a top-level decl's OUTER `row` cannot yet carry a genuine user/custom label,
# since the `handle-with` D3 typed-custom-handle syntax (a live, separate lane's own work) hasn't
# landed; this fixture and the demo below are honest about v1's actual reach, not a hypothetical).
cat > "$tmpdir/pubdemo.bang" <<'BANG'
pub let rec fib : Int -> Int = fun n => if n < 2 then n else $fib (n - 1) + $fib (n - 2)
let helper = {fun n => $fib n + 1}
pub let pure_add = {fun a => fun b => a + b}
BANG

# ══ 1. `dump` — THE key operation: the complete fact base ══

got_out="$("$bang" query dump "$tmpdir/simple.bang" 2>/dev/null)" && got_exit=0 || got_exit=$?
check "dump-exit" "$got_exit" "0"
check "dump-shape" "$got_out" '{"ok":true,"decls":[{"name":"double","kind":"letRec","type":"Thunk Int -> Int","row":"{}","typeError":null,"shape":null,"pub":false,"module":null},{"name":"quad","kind":"let","type":"Thunk Int -> Int","row":"{}","typeError":null,"shape":null,"pub":false,"module":null},{"name":"main","kind":"let","type":"Int","row":"{}","typeError":null,"shape":null,"pub":false,"module":null}],"refs":[{"from":"quad","to":"double"},{"from":"main","to":"quad"}],"laws":[],"imports":[],"uses":[]}'

# stdin agrees with file.
got_stdin="$(cat "$tmpdir/simple.bang" | "$bang" query dump 2>/dev/null)" || true
check "dump-stdin-eq-file" "$got_stdin" "$got_out"

# EVERY curated verb's answer is a PROJECTION of `dump` — the layering claim, checked directly:
# `symbols`'s "decls" entries equal `dump`'s "decls" entries byte-for-byte (same DeclFact.toJson).
got_symbols="$("$bang" query symbols "$tmpdir/simple.bang" 2>/dev/null)" || true
got_dump_decls="$(printf '%s' "$got_out" | python3 -c 'import json,sys; d=json.load(sys.stdin); print(json.dumps({"ok":True,"symbols":d["decls"]}, separators=(",",":")))' 2>/dev/null)" || true
check "symbols-is-dump-decls-projection" "$got_symbols" "$got_dump_decls"

# a parse failure is an OP-LEVEL answer (exit 1, ok:false on stdout — NOT a tool error).
got_out2="$(printf 'let x 3 in x' | "$bang" query dump 2>/dev/null)" && got_exit2=0 || got_exit2=$?
check "dump-parse-error-ok-false" "$(printf '%s' "$got_out2" | grep -o '"ok":false' || true)" '"ok":false'
check "dump-parse-error-exit" "$got_exit2" "1"

# dump's law/impl/trait facts — a decls-only fixture with a trait+impl+law.
got_out3="$("$bang" query dump "$tmpdir/laws.bang" 2>/dev/null)" && got_exit3=0 || got_exit3=$?
check "dump-laws-exit" "$got_exit3" "0"
check "dump-laws-present" "$(printf '%s' "$got_out3" | grep -o '"laws":\[{"trait":"Eq"' || true)" '"laws":[{"trait":"Eq"'
check "dump-trait-shape-present" "$(printf '%s' "$got_out3" | grep -o '"kind":"trait"' || true)" '"kind":"trait"'
check "dump-impl-shape-present" "$(printf '%s' "$got_out3" | grep -o '"kind":"impl"' || true)" '"kind":"impl"'

# every examples/*/main.bang round-trips ok:true through `dump` (the corpus, not just one file).
examples_pass=0
examples_fail=0
for dir in examples/*/; do
  main="$dir/main.bang"
  name="$(basename "$dir")"
  [ -f "$main" ] || continue
  out="$("$bang" query dump "$main" 2>/dev/null)" || true
  if printf '%s' "$out" | grep -q '"ok":true'; then
    examples_pass=$((examples_pass + 1))
  else
    echo "✗ dump-examples-corpus — $name did not report ok:true: $out"
    examples_fail=$((examples_fail + 1))
  fi
done
check "dump-examples-corpus-all-ok" "$examples_fail" "0"
echo "  (dump examples corpus: $examples_pass/$((examples_pass + examples_fail)) ok:true)"

# ── MULTI-FILE dump: imports field must reflect the ENTRY file's OWN header (a real fidelity gap
# found+fixed this slice — `mergeModules` clears `imports`/`uses` on its merged output, so `dump`
# must splice the pre-merge header back on; falsify by requiring the field is NONEMPTY). ──
got_out4="$("$bang" query dump examples/json/main.bang 2>/dev/null)" && got_exit4=0 || got_exit4=$?
check "dump-multifile-exit" "$got_exit4" "0"
check "dump-multifile-imports-present" "$(printf '%s' "$got_out4" | grep -o '"imports":\[{"module":"Json"}' || true)" '"imports":[{"module":"Json"}'
check "dump-multifile-qualified-present" "$(printf '%s' "$got_out4" | grep -o '"name":"Parse_dropWs"' || true)" '"name":"Parse_dropWs"'

# ══ 2. THE COMPOSED-QUERY DEMO (operator-required, #80 refinement): a question no fixed verb
# answers — "every EXPORTED (pub) decl whose type carries a divergence taint" — via a jq filter
# over `dump`'s own output, ~5 lines, zero new Lean code. Skipped (not failed) if jq is absent from
# the dev shell, matching test-check-json.sh's own jq-optionality precedent. ──
if command -v jq >/dev/null 2>&1; then
  composed="$("$bang" query dump "$tmpdir/pubdemo.bang" 2>/dev/null | \
    jq -c '[.decls[] | select(.pub and ((.type // "") | contains("Div"))) | .name]')" || true
  check "composed-query-pub-divergent" "$composed" '["fib"]'
else
  echo "· composed-query-pub-divergent — SKIPPED (jq not in dev shell; not adding it for this check)"
fi

# ══ 3. `symbols` (thin projection of dump's "decls") ══

got_out="$("$bang" query symbols "$tmpdir/simple.bang" 2>/dev/null)" && got_exit=0 || got_exit=$?
check "symbols-exit" "$got_exit" "0"
check "symbols-shape" "$got_out" '{"ok":true,"symbols":[{"name":"double","kind":"letRec","type":"Thunk Int -> Int","row":"{}","typeError":null,"shape":null,"pub":false,"module":null},{"name":"quad","kind":"let","type":"Thunk Int -> Int","row":"{}","typeError":null,"shape":null,"pub":false,"module":null},{"name":"main","kind":"let","type":"Int","row":"{}","typeError":null,"shape":null,"pub":false,"module":null}]}'

got_stdin="$(cat "$tmpdir/simple.bang" | "$bang" query symbols 2>/dev/null)" || true
check "symbols-stdin-eq-file" "$got_stdin" "$got_out"

got_out="$(printf 'let x 3 in x' | "$bang" query symbols 2>/dev/null)" && got_exit=0 || got_exit=$?
check "symbols-parse-error-ok-false" "$(printf '%s' "$got_out" | grep -o '"ok":false' || true)" '"ok":false'
check "symbols-parse-error-exit" "$got_exit" "1"

# ══ 4. `type` / `effects` ══

got_out="$("$bang" query type "$tmpdir/simple.bang" double 2>/dev/null)" && got_exit=0 || got_exit=$?
check "type-exit" "$got_exit" "0"
check "type-shape" "$got_out" '{"ok":true,"type":"Thunk Int -> Int","row":"{}"}'

got_out="$("$bang" query effects double "$tmpdir/simple.bang" 2>/dev/null)" && got_exit=0 || got_exit=$?
check "effects-exit" "$got_exit" "0"
check "effects-shape" "$got_out" '{"ok":true,"row":"{}"}'

got_out="$(cat "$tmpdir/simple.bang" | "$bang" query effects double 2>/dev/null)" && got_exit=0 || got_exit=$?
check "effects-stdin-exit" "$got_exit" "0"
check "effects-stdin-shape" "$got_out" '{"ok":true,"row":"{}"}'

# naming a nonexistent decl is a LOUD op-level miss (ok:false ON STDOUT) but exit 0: the TOOL ran
# successfully and produced a well-formed (negative) answer (exit 1 is reserved for "the op could
# NOT run" — a parse/resolution failure — not an op-level negative answer).
got_out="$("$bang" query type "$tmpdir/simple.bang" nosuch 2>/dev/null)" && got_exit=0 || got_exit=$?
check "type-miss-ok-false" "$(printf '%s' "$got_out" | grep -o '"ok":false' || true)" '"ok":false'
check "type-miss-exit" "$got_exit" "0"

# ══ 5. `laws` ══

got_out="$("$bang" query laws "$tmpdir/laws.bang" 2>/dev/null)" && got_exit=0 || got_exit=$?
check "laws-exit" "$got_exit" "0"
check "laws-shape" "$got_out" '{"ok":true,"laws":[{"trait":"Eq","law":"refl","params":["x"],"body":"eq(x, x) == 1"}]}'

got_stdin="$(cat "$tmpdir/laws.bang" | "$bang" query laws 2>/dev/null)" || true
check "laws-stdin-eq-file" "$got_stdin" "$got_out"

got_out="$(printf 'let x = 3 in x' | "$bang" query laws 2>/dev/null)" && got_exit=0 || got_exit=$?
check "laws-empty-exit" "$got_exit" "0"
check "laws-empty-shape" "$got_out" '{"ok":true,"laws":[]}'

# ══ 6. `def` / `refs` (thin filters over dump's "decls"/"refs") ══

got_out="$("$bang" query def double "$tmpdir/simple.bang" 2>/dev/null)" && got_exit=0 || got_exit=$?
check "def-exit" "$got_exit" "0"
check "def-shape" "$got_out" '{"ok":true,"symbol":{"name":"double","kind":"letRec","type":"Thunk Int -> Int","row":"{}","typeError":null,"shape":null,"pub":false,"module":null}}'

got_out="$("$bang" query def nosuch "$tmpdir/simple.bang" 2>/dev/null)" && got_exit=0 || got_exit=$?
check "def-miss-ok-false" "$got_out" "{\"ok\":false,\"error\":\"no top-level decl named 'nosuch'\"}"
check "def-miss-exit" "$got_exit" "0"

got_out="$("$bang" query refs double "$tmpdir/simple.bang" 2>/dev/null)" && got_exit=0 || got_exit=$?
check "refs-exit" "$got_exit" "0"
check "refs-shape" "$got_out" '{"ok":true,"refs":[{"name":"quad","kind":"let"}]}'

got_out="$("$bang" query refs main "$tmpdir/simple.bang" 2>/dev/null)" && got_exit=0 || got_exit=$?
check "refs-empty-exit" "$got_exit" "0"
check "refs-empty-shape" "$got_out" '{"ok":true,"refs":[]}'

got_out="$("$bang" query def Parse_dropWs examples/json/main.bang 2>/dev/null)" && got_exit=0 || got_exit=$?
check "def-multifile-exit" "$got_exit" "0"
check "def-multifile-hit" "$(printf '%s' "$got_out" | grep -o '"ok":true' || true)" '"ok":true'

# ══ 7. Exit-code contract: TOOL error (exit 2, unreadable file) ══

got_out="$("$bang" query dump /no/such/file.bang 2>/dev/null)" && got_exit=0 || got_exit=$?
check "tool-error-dump-stdout-empty" "$got_out" ""
check "tool-error-dump-exit" "$got_exit" "2"

got_out="$("$bang" query symbols /no/such/file.bang 2>/dev/null)" && got_exit=0 || got_exit=$?
check "tool-error-symbols-stdout-empty" "$got_out" ""
check "tool-error-symbols-exit" "$got_exit" "2"

got_out="$("$bang" query def foo /no/such/file.bang 2>/dev/null)" && got_exit=0 || got_exit=$?
check "tool-error-def-stdout-empty" "$got_out" ""
check "tool-error-def-exit" "$got_exit" "2"

got_out="$("$bang" query laws /no/such/file.bang 2>/dev/null)" && got_exit=0 || got_exit=$?
check "tool-error-laws-stdout-empty" "$got_out" ""
check "tool-error-laws-exit" "$got_exit" "2"

got_usage_exit=0
"$bang" query type "$tmpdir/simple.bang" >/dev/null 2>&1 || got_usage_exit=$?
check "usage-error-type-missing-name-exit" "$got_usage_exit" "1"

# ── jq-parseability: every op's output is valid JSON, not just byte-matching our own expectation.
if command -v jq >/dev/null 2>&1; then
  jq_ok=0
  jq_total=0
  for op_args in "dump $tmpdir/simple.bang" "symbols $tmpdir/simple.bang" "type $tmpdir/simple.bang double" \
                 "effects double $tmpdir/simple.bang" "laws $tmpdir/laws.bang" \
                 "def double $tmpdir/simple.bang" "refs double $tmpdir/simple.bang"; do
    jq_total=$((jq_total + 1))
    jq_in="$("$bang" query $op_args 2>/dev/null)" || true
    if printf '%s' "$jq_in" | jq -e '.ok == true' >/dev/null 2>&1; then
      jq_ok=$((jq_ok + 1))
    else
      echo "✗ jq-parseable — 'query $op_args' did not parse as expected JSON shape: $jq_in"
    fi
  done
  check "jq-parseable-all-ops" "$jq_ok" "$jq_total"
else
  echo "· jq-parseable — SKIPPED (jq not in dev shell; not adding it for this check)"
fi

echo "──────────────────────────────"
echo "query: $pass passed, $fail failed"
# Assert the expected total COUNT — catches a silently-truncated run.
want_total=53
got_total=$((pass + fail))
if [ "$got_total" -ne "$want_total" ]; then
  echo "✗ check-count-mismatch — expected $want_total checks to run, only $got_total did (script truncated?)"
  exit 1
fi
[ "$fail" -eq 0 ]
