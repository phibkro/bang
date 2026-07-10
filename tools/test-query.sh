#!/usr/bin/env bash
# tool: role=test couples=examples/*/main.bang runs-in=verify
# test-query.sh — the non-interactive gate for `bang query <op>` (issue #80, the agent LSP as
# stateless CLI subcommands).
#
# Mirrors test-check-json.sh's shape (build once, exercise the binary, diff, tally pass/fail). The
# JSON-emitter internals (`jsonStr`/`jsonField`/`jsonObj` escaping, the schema's per-op byte-exact
# shape on a fixed input) are already gated at the Lean `#guard` level (Bang/Frontend/Query.lean) —
# this file gates the CLI SURFACE specifically: file-arg vs stdin, argument-order per op, the
# resolver-aware multi-file path (imports/qualification), and the 0/1/2 exit-code contract observed
# THROUGH the binary (arg-parsing/file-reading/dispatch/exit-code plumbing is new code the `#guard`s
# never touch — the SAME rationale test-check-json.sh's own header states).
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

# ══ 1. `symbols` ══

# single-file, via file arg: every decl present, in source order, with checker-computed types.
got_out="$("$bang" query symbols "$tmpdir/simple.bang" 2>/dev/null)" && got_exit=0 || got_exit=$?
check "symbols-file-exit" "$got_exit" "0"
check "symbols-file-ok-true" "$(printf '%s' "$got_out" | grep -o '"ok":true' || true)" '"ok":true'
check "symbols-file-double-letrec" "$(printf '%s' "$got_out" | grep -o '"name":"double","kind":"letRec"' || true)" '"name":"double","kind":"letRec"'
check "symbols-file-quad-let" "$(printf '%s' "$got_out" | grep -o '"name":"quad","kind":"let"' || true)" '"name":"quad","kind":"let"'
check "symbols-file-main-type" "$(printf '%s' "$got_out" | grep -o '"name":"main","kind":"let","type":"Int"' || true)" '"name":"main","kind":"let","type":"Int"'

# stdin agrees with file (SAME entry point, `symbols` with no file arg reads stdin).
got_stdin="$(cat "$tmpdir/simple.bang" | "$bang" query symbols 2>/dev/null)" || true
check "symbols-stdin-eq-file" "$got_stdin" "$got_out"

# a parse failure is an OP-LEVEL answer (exit 1, ok:false on stdout — NOT a tool error).
got_out="$(printf 'let x 3 in x' | "$bang" query symbols 2>/dev/null)" && got_exit=0 || got_exit=$?
check "symbols-parse-error-ok-false" "$(printf '%s' "$got_out" | grep -o '"ok":false' || true)" '"ok":false'
check "symbols-parse-error-exit" "$got_exit" "1"

# every examples/*/main.bang round-trips ok:true through `symbols` (the corpus, not just one file).
examples_pass=0
examples_fail=0
for dir in examples/*/; do
  main="$dir/main.bang"
  name="$(basename "$dir")"
  [ -f "$main" ] || continue
  out="$("$bang" query symbols "$main" 2>/dev/null)" || true
  if printf '%s' "$out" | grep -q '"ok":true'; then
    examples_pass=$((examples_pass + 1))
  else
    echo "✗ symbols-examples-corpus — $name did not report ok:true: $out"
    examples_fail=$((examples_fail + 1))
  fi
done
check "symbols-examples-corpus-all-ok" "$examples_fail" "0"
echo "  (symbols examples corpus: $examples_pass/$((examples_pass + examples_fail)) ok:true)"

# ── MULTI-FILE (resolver-aware): examples/json/main.bang imports Json/Parse/Print — an imported
# decl's own top-level names must appear QUALIFIED (the merge convention `TypeCheck.mergeModules`
# already applies to `bang run`/`check --json`) — this is the CLI-surface half of that behavior
# (the pure merge itself is gated elsewhere); falsify by checking the UNQUALIFIED name is ABSENT.
got_out="$("$bang" query symbols examples/json/main.bang 2>/dev/null)" && got_exit=0 || got_exit=$?
check "symbols-multifile-exit" "$got_exit" "0"
check "symbols-multifile-qualified-present" "$(printf '%s' "$got_out" | grep -o '"name":"Parse_dropWs"' || true)" '"name":"Parse_dropWs"'
check "symbols-multifile-unqualified-absent" "$(printf '%s' "$got_out" | grep -c '"name":"dropWs"' || true)" "0"

# ══ 2. `type` / `effects` ══

got_out="$("$bang" query type "$tmpdir/simple.bang" double 2>/dev/null)" && got_exit=0 || got_exit=$?
check "type-exit" "$got_exit" "0"
check "type-shape" "$got_out" '{"ok":true,"type":"Thunk Int -> Int","row":"{}"}'

got_out="$("$bang" query effects double "$tmpdir/simple.bang" 2>/dev/null)" && got_exit=0 || got_exit=$?
check "effects-exit" "$got_exit" "0"
check "effects-shape" "$got_out" '{"ok":true,"row":"{}"}'

# `effects` reads stdin when no file is given (mirrors `check`/`fmt`'s stdin convention).
got_out="$(cat "$tmpdir/simple.bang" | "$bang" query effects double 2>/dev/null)" && got_exit=0 || got_exit=$?
check "effects-stdin-exit" "$got_exit" "0"
check "effects-stdin-shape" "$got_out" '{"ok":true,"row":"{}"}'

# naming a nonexistent decl is a LOUD op-level miss (ok:false ON STDOUT — the checker's own
# "unbound variable" surfaces through `typeStringOfProgP`'s `Except`) but exit 0: the TOOL ran
# successfully and produced a well-formed (negative) answer — the SAME "ok:false is still exit 0"
# convention `def-miss` below exercises (see usage text's EXIT CODES [bang query <op>] section:
# exit 1 is reserved for "the op could NOT run" — a parse/resolution failure — not an op-level
# negative answer).
got_out="$("$bang" query type "$tmpdir/simple.bang" nosuch 2>/dev/null)" && got_exit=0 || got_exit=$?
check "type-miss-ok-false" "$(printf '%s' "$got_out" | grep -o '"ok":false' || true)" '"ok":false'
check "type-miss-exit" "$got_exit" "0"

# ══ 3. `laws` ══

got_out="$("$bang" query laws "$tmpdir/laws.bang" 2>/dev/null)" && got_exit=0 || got_exit=$?
check "laws-exit" "$got_exit" "0"
check "laws-shape" "$got_out" '{"ok":true,"laws":[{"trait":"Eq","law":"refl","params":["x"],"body":"eq(x, x) == 1"}]}'

# stdin agrees with file.
got_stdin="$(cat "$tmpdir/laws.bang" | "$bang" query laws 2>/dev/null)" || true
check "laws-stdin-eq-file" "$got_stdin" "$got_out"

# no laws present ⟹ a vacuous, honest ok:true with an EMPTY array (mirrors `bang test`'s own
# "0 discovered is not a failure" convention).
got_out="$(printf 'let x = 3 in x' | "$bang" query laws 2>/dev/null)" && got_exit=0 || got_exit=$?
check "laws-empty-exit" "$got_exit" "0"
check "laws-empty-shape" "$got_out" '{"ok":true,"laws":[]}'

# ══ 4. `def` / `refs` ══

got_out="$("$bang" query def double "$tmpdir/simple.bang" 2>/dev/null)" && got_exit=0 || got_exit=$?
check "def-exit" "$got_exit" "0"
check "def-shape" "$got_out" '{"ok":true,"symbol":{"name":"double","kind":"letRec","type":"Thunk Int -> Int"}}'

# a miss is LOUD (ADR-0046 — never a guessed nearest-match) on stdout, exit 0 — the SAME "an
# op-level ok:false is still exit 0" convention `type-miss` above exercises.
got_out="$("$bang" query def nosuch "$tmpdir/simple.bang" 2>/dev/null)" && got_exit=0 || got_exit=$?
check "def-miss-ok-false" "$got_out" "{\"ok\":false,\"error\":\"no top-level decl named 'nosuch'\"}"
check "def-miss-exit" "$got_exit" "0"

# `refs double` finds `quad` (which calls `$double` twice) but not `main` (which never mentions it).
got_out="$("$bang" query refs double "$tmpdir/simple.bang" 2>/dev/null)" && got_exit=0 || got_exit=$?
check "refs-exit" "$got_exit" "0"
check "refs-shape" "$got_out" '{"ok":true,"refs":[{"name":"quad","kind":"let"}]}'

# `refs` on a name nothing mentions is a VALID, honest empty answer (not an error — `refs` doesn't
# itself validate the name exists, per Query.lean's own doc comment).
got_out="$("$bang" query refs main "$tmpdir/simple.bang" 2>/dev/null)" && got_exit=0 || got_exit=$?
check "refs-empty-exit" "$got_exit" "0"
check "refs-empty-shape" "$got_out" '{"ok":true,"refs":[]}'

# MULTI-FILE def/refs: the qualified name is what's addressable post-merge (documented v1
# characteristic — Query.lean's `defJsonP` doc comment).
got_out="$("$bang" query def Parse_dropWs examples/json/main.bang 2>/dev/null)" && got_exit=0 || got_exit=$?
check "def-multifile-exit" "$got_exit" "0"
check "def-multifile-hit" "$(printf '%s' "$got_out" | grep -o '"ok":true' || true)" '"ok":true'

# ══ 5. Exit-code contract: TOOL error (exit 2, unreadable file) ══

# `symbols`/`type`/`effects`/`def`/`refs`: tool error → STDERR message, NOTHING on stdout, exit 2
# (mirrors `check --json`'s own tool-error convention exactly — never folded into the JSON).
got_out="$("$bang" query symbols /no/such/file.bang 2>/dev/null)" && got_exit=0 || got_exit=$?
check "tool-error-symbols-stdout-empty" "$got_out" ""
check "tool-error-symbols-exit" "$got_exit" "2"

got_out="$("$bang" query def foo /no/such/file.bang 2>/dev/null)" && got_exit=0 || got_exit=$?
check "tool-error-def-stdout-empty" "$got_out" ""
check "tool-error-def-exit" "$got_exit" "2"

got_out="$("$bang" query laws /no/such/file.bang 2>/dev/null)" && got_exit=0 || got_exit=$?
check "tool-error-laws-stdout-empty" "$got_out" ""
check "tool-error-laws-exit" "$got_exit" "2"

# ── usage errors (a malformed `query` invocation, e.g. missing positional) is a 1, matching every
# other subcommand's usage-error convention (never a silent pick-first/pick-last). ──
got_usage_exit=0
"$bang" query type "$tmpdir/simple.bang" >/dev/null 2>&1 || got_usage_exit=$?
check "usage-error-type-missing-name-exit" "$got_usage_exit" "1"

# ── jq-parseability: every op's output is valid JSON, not just byte-matching our own expectation.
# Skip with a note if jq isn't in the dev shell (test-check-json.sh's own precedent: not adding jq
# to the flake for this). ──
if command -v jq >/dev/null 2>&1; then
  jq_ok=0
  jq_total=0
  for op_args in "symbols $tmpdir/simple.bang" "type $tmpdir/simple.bang double" \
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
want_total=43
got_total=$((pass + fail))
if [ "$got_total" -ne "$want_total" ]; then
  echo "✗ check-count-mismatch — expected $want_total checks to run, only $got_total did (script truncated?)"
  exit 1
fi
[ "$fail" -eq 0 ]
