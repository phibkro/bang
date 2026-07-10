#!/usr/bin/env bash
# tool: role=test couples=examples/*/main.bang runs-in=verify
# test-82-verbs.sh — the non-interactive gate for the #82 agent-tooling verbs over the landed
# Query rails (the analysis/ergonomics commands past the query/rewrite/lint/annotate set).
#
# ONE script for the lane, cases-per-verb (mirrors test-query.sh/test-lint.sh's shape: build once,
# exercise the binary, tally pass/fail). The pure per-verb logic (e.g. `Query.holeMarkersIn`/
# `holesOf`) is already gated at the Lean `#guard` level (Bang/Frontend/Query.lean) — this file
# gates the CLI SURFACE: file-arg vs stdin, resolver-aware multi-file, the 0/1/2 exit contract
# observed THROUGH the binary, and one FALSIFY-ONCE case per verb (a fixture where the verb is
# EXPECTED to fire, proving it discriminates rather than being a vacuous always-pass).
#
# GOTCHA (set -euo pipefail, per test-query.sh's own documented lesson): an unguarded
# `$(cmd1 | cmd2)` capture can kill this script SILENTLY mid-run. Every capture below either runs
# standalone (no pipe) with an explicit `&& … || …` exit-capture, or pipes into `grep`/`jq` with
# `|| true` on the capture. The FINAL line asserts the expected check COUNT.
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

tmpdir="$(mktemp -d)"
trap 'rm -rf "$tmpdir"' EXIT

# ══ VERB: holes (#82 item 3) — residual/underdetermined positions ══
#
# bang has no user-facing `_` hole syntax yet, but the checker DOES report underdetermined
# positions: a bare `id = {fun x => x}` cannot pin its arg/result type, so it reports
# `Thunk #1000003 -> #1000003` (a residual hole per position, `#N` with N ≥ holeBase). `holes`
# extracts those markers — the honest v1 surface. The exact marker NUMBER is inference-run-order-
# dependent, so cases assert PRESENCE of a hole (`#100`-prefixed marker) + the decl name, never a
# byte-exact number (which would be brittle across unrelated checker changes).

# a fixture with a genuinely underdetermined decl (`id`) AND a fully-pinned one (`main`).
cat > "$tmpdir/holes.bang" <<'BANG'
let id = {fun x => x}
let main = $id 3
BANG

# a fixture with NO holes: every decl fully pinned.
cat > "$tmpdir/nohole.bang" <<'BANG'
let rec double : Int -> Int = fun n => n + n
let main = $double 3
BANG

got_out="$("$bang" holes "$tmpdir/holes.bang" 2>/dev/null)" && got_exit=0 || got_exit=$?
check "holes-exit" "$got_exit" "0"
check "holes-ok-true" "$(printf '%s' "$got_out" | grep -o '"ok":true' || true)" '"ok":true'
# the underdetermined decl `id` is reported…
check "holes-id-present" "$(printf '%s' "$got_out" | grep -o '"name":"id"' || true)" '"name":"id"'
# …with at least one hole marker (a `#` followed by a holeBase-range number, ≥ 7 digits).
check "holes-marker-present" "$(printf '%s' "$got_out" | grep -oE '"#1[0-9]{6,}"' | head -1 || true)" "$(printf '%s' "$got_out" | grep -oE '"#1[0-9]{6,}"' | head -1 || true)"
check "holes-has-a-marker" "$(printf '%s' "$got_out" | grep -qE '"#1[0-9]{6,}"' && echo yes || echo no)" "yes"
# the fully-pinned `main : Int` is NOT reported as a hole (discrimination — the verb isn't vacuous).
check "holes-main-absent" "$(printf '%s' "$got_out" | grep -o '"name":"main"' || true)" ''

# stdin agrees with file.
got_stdin="$(cat "$tmpdir/holes.bang" | "$bang" holes 2>/dev/null)" || true
check "holes-stdin-eq-file" "$got_stdin" "$got_out"

# a fully-pinned program: EMPTY holes array, still ok:true / exit 0 (the caller inspects the array).
got_out2="$("$bang" holes "$tmpdir/nohole.bang" 2>/dev/null)" && got_exit2=0 || got_exit2=$?
check "holes-nohole-exit" "$got_exit2" "0"
check "holes-nohole-empty" "$got_out2" '{"ok":true,"holes":[]}'

# a parse failure is an OP-LEVEL answer (exit 1, ok:false on stdout — NOT a tool error).
got_out3="$(printf 'let x 3 in x' | "$bang" holes 2>/dev/null)" && got_exit3=0 || got_exit3=$?
check "holes-parse-error-ok-false" "$(printf '%s' "$got_out3" | grep -o '"ok":false' || true)" '"ok":false'
check "holes-parse-error-exit" "$got_exit3" "1"

# a TOOL error (unreadable file): nothing on stdout, exit 2 (the query/check convention).
got_out4="$("$bang" holes /no/such/file.bang 2>/dev/null)" && got_exit4=0 || got_exit4=$?
check "holes-tool-error-stdout-empty" "$got_out4" ""
check "holes-tool-error-exit" "$got_exit4" "2"

# every examples/*/main.bang round-trips ok:true through `holes` (the corpus, not just fixtures) —
# a resolver-aware smoke check that multi-file programs don't crash the verb.
examples_pass=0
examples_fail=0
for dir in examples/*/; do
  main="$dir/main.bang"
  name="$(basename "$dir")"
  [ -f "$main" ] || continue
  out="$("$bang" holes "$main" 2>/dev/null)" || true
  if printf '%s' "$out" | grep -q '"ok":true'; then
    examples_pass=$((examples_pass + 1))
  else
    echo "✗ holes-examples-corpus — $name did not report ok:true: $out"
    examples_fail=$((examples_fail + 1))
  fi
done
check "holes-examples-corpus-all-ok" "$examples_fail" "0"
echo "  (holes examples corpus: $examples_pass/$((examples_pass + examples_fail)) ok:true)"

# ══ VERB: impact (#82 item 5) — transitive dependents (pre-edit blast radius) ══
#
# `impact <file> <decl>` = the REVERSE closure over the SAME ref-graph `refs`/`dump` expose: every
# decl that reaches `decl` directly or through a chain. Fixture: main → quad → double, so editing
# `double` impacts BOTH `quad` (direct) and `main` (transitive); editing `main` impacts nothing.
cat > "$tmpdir/chain.bang" <<'BANG'
let rec double : Int -> Int = fun n => n + n
let quad = {fun n => $double ($double n)}
let main = $quad 3
BANG

got_out="$("$bang" impact "$tmpdir/chain.bang" double 2>/dev/null)" && got_exit=0 || got_exit=$?
check "impact-exit" "$got_exit" "0"
check "impact-ok-true" "$(printf '%s' "$got_out" | grep -o '"ok":true' || true)" '"ok":true'
check "impact-decl-echoed" "$(printf '%s' "$got_out" | grep -o '"decl":"double"' || true)" '"decl":"double"'
# BOTH the direct dependent (quad) and the TRANSITIVE one (main) are reported.
check "impact-direct-dependent" "$(printf '%s' "$got_out" | grep -o '"name":"quad"' || true)" '"name":"quad"'
check "impact-transitive-dependent" "$(printf '%s' "$got_out" | grep -o '"name":"main"' || true)" '"name":"main"'
# a LEAF-of-the-graph decl (main) has NO dependents — empty array (discrimination, not vacuous).
got_out2="$("$bang" impact "$tmpdir/chain.bang" main 2>/dev/null)" && got_exit2=0 || got_exit2=$?
check "impact-leaf-empty" "$got_out2" '{"ok":true,"decl":"main","dependents":[]}'
# a nonexistent decl is a LOUD op-level miss (ok:false ON STDOUT) but exit 0 (the tool ran).
got_out3="$("$bang" impact "$tmpdir/chain.bang" nosuch 2>/dev/null)" && got_exit3=0 || got_exit3=$?
check "impact-miss-ok-false" "$got_out3" "{\"ok\":false,\"error\":\"no top-level decl named 'nosuch'\"}"
check "impact-miss-exit" "$got_exit3" "0"
# TOOL error (unreadable file): nothing on stdout, exit 2.
got_out4="$("$bang" impact /no/such/file.bang double 2>/dev/null)" && got_exit4=0 || got_exit4=$?
check "impact-tool-error-stdout-empty" "$got_out4" ""
check "impact-tool-error-exit" "$got_exit4" "2"

# ══ VERB: semver-diff (#82 item 6) — public-surface diff → version bump ══
#
# `semver-diff <old> <new>` diffs the PUBLIC (`pub`) decl surface. Fixtures pin each bump class:
# a REMOVED pub decl ⟹ major; an ADDED pub decl ⟹ minor; no pub change ⟹ patch. A private (non-pub)
# decl's churn is INVISIBLE (not the public contract) — asserted by the patch case below.
cat > "$tmpdir/v1.bang" <<'BANG'
pub let add = {fun a => fun b => a + b}
pub let sub = {fun a => fun b => a - b}
let main = 0
BANG
# v2: `sub` REMOVED, `mul` ADDED — removal dominates ⟹ major.
cat > "$tmpdir/v2.bang" <<'BANG'
pub let add = {fun a => fun b => a + b}
pub let mul = {fun a => fun b => a * b}
let main = 0
BANG
# v3: only an ADD relative to v1 (`sub` kept, `mul` added) ⟹ minor.
cat > "$tmpdir/v3.bang" <<'BANG'
pub let add = {fun a => fun b => a + b}
pub let sub = {fun a => fun b => a - b}
pub let mul = {fun a => fun b => a * b}
let main = 0
BANG
# v4: same pub surface as v1, only a PRIVATE decl added ⟹ patch (private churn is invisible).
cat > "$tmpdir/v4.bang" <<'BANG'
pub let add = {fun a => fun b => a + b}
pub let sub = {fun a => fun b => a - b}
let helper = {fun n => n + 1}
let main = 0
BANG

got_out="$("$bang" semver-diff "$tmpdir/v1.bang" "$tmpdir/v2.bang" 2>/dev/null)" && got_exit=0 || got_exit=$?
check "semver-major-exit" "$got_exit" "0"
check "semver-major-bump" "$(printf '%s' "$got_out" | grep -o '"bump":"major"' || true)" '"bump":"major"'
check "semver-major-removed" "$(printf '%s' "$got_out" | grep -o '"removed":\["sub"\]' || true)" '"removed":["sub"]'
check "semver-major-added" "$(printf '%s' "$got_out" | grep -o '"added":\["mul"\]' || true)" '"added":["mul"]'

got_out="$("$bang" semver-diff "$tmpdir/v1.bang" "$tmpdir/v3.bang" 2>/dev/null)" && got_exit=0 || got_exit=$?
check "semver-minor-bump" "$(printf '%s' "$got_out" | grep -o '"bump":"minor"' || true)" '"bump":"minor"'

got_out="$("$bang" semver-diff "$tmpdir/v1.bang" "$tmpdir/v4.bang" 2>/dev/null)" && got_exit=0 || got_exit=$?
check "semver-patch-bump" "$(printf '%s' "$got_out" | grep -o '"bump":"patch"' || true)" '"bump":"patch"'
# private churn is invisible: no pub decl added/removed/changed.
check "semver-patch-empty" "$got_out" '{"ok":true,"bump":"patch","added":[],"removed":[],"changed":[]}'

# a parse failure on the NEW side is an op-level answer (ok:false, exit 1) naming the side.
got_out="$(printf 'let x 3' > "$tmpdir/bad.bang"; "$bang" semver-diff "$tmpdir/v1.bang" "$tmpdir/bad.bang" 2>/dev/null)" && got_exit=0 || got_exit=$?
check "semver-parse-error-ok-false" "$(printf '%s' "$got_out" | grep -o '"ok":false' || true)" '"ok":false'
check "semver-parse-error-exit" "$got_exit" "1"
# TOOL error (unreadable OLD file): nothing on stdout, exit 2.
got_out="$("$bang" semver-diff /no/such/old.bang "$tmpdir/v1.bang" 2>/dev/null)" && got_exit=0 || got_exit=$?
check "semver-tool-error-stdout-empty" "$got_out" ""
check "semver-tool-error-exit" "$got_exit" "2"

# ── jq-parseability: every verb's output is valid JSON, not just byte-matching our expectation.
if command -v jq >/dev/null 2>&1; then
  jq_ok=0
  jq_h="$("$bang" holes "$tmpdir/holes.bang" 2>/dev/null)" || true
  printf '%s' "$jq_h" | jq -e '.ok == true and (.holes | type == "array")' >/dev/null 2>&1 && jq_ok=$((jq_ok+1)) || echo "✗ jq holes: $jq_h"
  jq_i="$("$bang" impact "$tmpdir/chain.bang" double 2>/dev/null)" || true
  printf '%s' "$jq_i" | jq -e '.ok == true and (.dependents | type == "array")' >/dev/null 2>&1 && jq_ok=$((jq_ok+1)) || echo "✗ jq impact: $jq_i"
  jq_s="$("$bang" semver-diff "$tmpdir/v1.bang" "$tmpdir/v2.bang" 2>/dev/null)" || true
  printf '%s' "$jq_s" | jq -e '.ok == true and (.bump | type == "string")' >/dev/null 2>&1 && jq_ok=$((jq_ok+1)) || echo "✗ jq semver: $jq_s"
  check "jq-parseable-all-verbs" "$jq_ok" "3"
else
  echo "· jq-parseable-all-verbs — SKIPPED (jq not in dev shell; not adding it for this check)"
fi

echo "──────────────────────────────"
echo "82-verbs: $pass passed, $fail failed"
# Assert the expected total COUNT — catches a silently-truncated run. BASE is every check that
# always runs; jq's ONE guarded block contributes exactly one more `check()` call when jq is
# present (jq IS in the standard `nix develop` shell, so this is the steady-state path). The total
# tracks WHICH optional tools ran, so a genuinely truncated run is caught regardless of PATH.
want_total=35
if command -v jq >/dev/null 2>&1; then want_total=$((want_total + 1)); fi
got_total=$((pass + fail))
if [ "$got_total" -ne "$want_total" ]; then
  echo "✗ check-count-mismatch — expected $want_total checks to run, only $got_total did (script truncated?)"
  exit 1
fi
[ "$fail" -eq 0 ]
