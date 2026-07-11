#!/usr/bin/env bash
# tool: role=test couples=examples/*/main.bang runs-in=verify
source "$(git rev-parse --show-toplevel 2>/dev/null)/tools/tool-log.sh" 2>/dev/null && tool_log "$(basename "$0")" || true
# test-lint.sh — the non-interactive gate for `bang lint` (#82 item 2).
#
# Mirrors test-rewrite.sh/test-annotate.sh's shape (build once, exercise the binary, tally
# pass/fail). The pure per-rule logic (`deadPrivateFindings`/`unusedPubFindings`/
# `fmtDivergenceFinding`/`closure`) is already gated at the Lean `#guard` level
# (Bang/Frontend/Lint.lean) — this file gates the CLI SURFACE: human table vs `--json`, the exit
# contract (0 unless a `warning` finding is present), `--quiet-clean`, and one FALSIFY-ONCE case
# per rule (a fixture where the rule is EXPECTED to fire, proving the rule discriminates rather
# than being a vacuous always-pass).
#
# GOTCHA (set -euo pipefail, per test-rewrite.sh's own documented lesson): an unguarded
# `$(cmd1 | cmd2)` capture can kill this script SILENTLY mid-run. Every capture below either runs
# standalone (no pipe) with an explicit `&& … || …` exit-capture, or pipes into `grep` with
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

# ── fixtures ──

# a CLEAN program: no dead private decl, no unused pub, already canonically formatted.
cat > "$tmpdir/clean.bang" <<'BANG'
let rec double : Int -> Int = fun n => n + n
let main = $double 3
BANG
"$bang" rewrite fmt "$tmpdir/clean.bang" -w >/dev/null 2>&1   # ensure it's ACTUALLY canonical

# a `dead-private` fixture: `helper` is a non-pub top-level decl nothing references.
cat > "$tmpdir/deadprivate.bang" <<'BANG'
let rec double : Int -> Int = fun n => n + n
let helper = {fun n => n * 2}
let main = $double 3
BANG
"$bang" rewrite fmt "$tmpdir/deadprivate.bang" -w >/dev/null 2>&1

# an `unused-pub` fixture: `widget` is exported but nothing in-module references it.
cat > "$tmpdir/unusedpub.bang" <<'BANG'
pub let widget = {fun n => n + 1}
let rec double : Int -> Int = fun n => n + n
let main = $double 3
BANG
"$bang" rewrite fmt "$tmpdir/unusedpub.bang" -w >/dev/null 2>&1

# an `fmt-divergence` fixture: intentionally messy layout.
cat > "$tmpdir/messy.bang" <<'BANG'
let   rec   double : Int -> Int = fun n => n+n
let main = $double 3
BANG

# ══ 1. `bang lint` on a CLEAN file: no findings, exit 0 ══

got_clean="$("$bang" lint "$tmpdir/clean.bang" 2>/dev/null)" && got_clean_exit=0 || got_clean_exit=$?
check "lint-clean-exit" "$got_clean_exit" "0"
check "lint-clean-no-findings-message" "$got_clean" "no findings"

# `--quiet-clean` suppresses the "no findings" line on a clean report.
got_quiet="$("$bang" lint "$tmpdir/clean.bang" --quiet-clean 2>/dev/null)" && got_quiet_exit=0 || got_quiet_exit=$?
check "lint-quiet-clean-exit" "$got_quiet_exit" "0"
check "lint-quiet-clean-no-output" "$got_quiet" ""

# ══ 2. `dead-private` — FALSIFY: fires on the unreferenced private decl ══

got_dead="$("$bang" lint "$tmpdir/deadprivate.bang" 2>/dev/null)" && got_dead_exit=0 || got_dead_exit=$?
check "lint-dead-private-exit" "$got_dead_exit" "1"
check "lint-dead-private-names-helper" "$(printf '%s' "$got_dead" | grep -c 'dead-private helper' || true)" "1"
check "lint-dead-private-severity-warn" "$(printf '%s' "$got_dead" | grep -c '\[WARN\] dead-private' || true)" "1"

# `--json` carries the same finding.
got_dead_json="$("$bang" lint "$tmpdir/deadprivate.bang" --json 2>/dev/null)" && got_dead_json_exit=0 || got_dead_json_exit=$?
check "lint-dead-private-json-exit" "$got_dead_json_exit" "1"
check "lint-dead-private-json-ok-false" "$(printf '%s' "$got_dead_json" | grep -c '"ok":false' || true)" "1"
check "lint-dead-private-json-rule" "$(printf '%s' "$got_dead_json" | grep -c '"rule":"dead-private"' || true)" "1"

# ══ 3. `unused-pub` — FALSIFY: fires on the unreferenced pub decl, severity info (not warning) ══

got_pub="$("$bang" lint "$tmpdir/unusedpub.bang" 2>/dev/null)" && got_pub_exit=0 || got_pub_exit=$?
check "lint-unused-pub-exit" "$got_pub_exit" "0"   # info-only: exit 0 (no warning-severity finding)
check "lint-unused-pub-names-widget" "$(printf '%s' "$got_pub" | grep -c 'unused-pub widget' || true)" "1"
check "lint-unused-pub-severity-info" "$(printf '%s' "$got_pub" | grep -c '\[INFO\] unused-pub' || true)" "1"

# ══ 4. `fmt-divergence` — FALSIFY: fires on the messy layout, points at the fix ══

got_messy="$("$bang" lint "$tmpdir/messy.bang" 2>/dev/null)" && got_messy_exit=0 || got_messy_exit=$?
check "lint-fmt-divergence-exit" "$got_messy_exit" "1"
check "lint-fmt-divergence-names-rule" "$(printf '%s' "$got_messy" | grep -c 'fmt-divergence' || true)" "1"
check "lint-fmt-divergence-points-at-fix" "$(printf '%s' "$got_messy" | grep -c 'rewrite fmt -w' || true)" "1"

# fixing the layout (`bang rewrite fmt -w`) makes the finding disappear.
"$bang" rewrite fmt "$tmpdir/messy.bang" -w >/dev/null 2>&1
got_messy_fixed="$("$bang" lint "$tmpdir/messy.bang" 2>/dev/null)" && got_messy_fixed_exit=0 || got_messy_fixed_exit=$?
check "lint-fmt-divergence-fixed-exit" "$got_messy_fixed_exit" "0"
check "lint-fmt-divergence-fixed-clean" "$got_messy_fixed" "no findings"

# ══ 5b. `bang lint --fix` — the preservation-gated fixit (plan 013 slice 6) ══

# happy path: --fix removes the dead-private decl, DIFF mode by default (file untouched).
cp "$tmpdir/deadprivate.bang" "$tmpdir/fix-happy.bang"
before_fix_md5="$(md5sum "$tmpdir/fix-happy.bang" | cut -d' ' -f1)"
got_fix_diff="$("$bang" lint --fix "$tmpdir/fix-happy.bang" 2>/dev/null)" && got_fix_diff_exit=0 || got_fix_diff_exit=$?
after_fix_md5="$(md5sum "$tmpdir/fix-happy.bang" | cut -d' ' -f1)"
check "lint-fix-diff-exit" "$got_fix_diff_exit" "0"
check "lint-fix-diff-file-untouched" "$after_fix_md5" "$before_fix_md5"
check "lint-fix-diff-removes-helper" "$(printf '%s' "$got_fix_diff" | grep -c -- '-let helper' || true)" "1"

# -w APPLIES the fix; the rewritten program still runs (preservation held), and re-lint is clean.
"$bang" lint --fix "$tmpdir/fix-happy.bang" -w >/dev/null 2>&1
got_fix_run="$("$bang" run --engine=oracle "$tmpdir/fix-happy.bang" 2>/dev/null)" && got_fix_run_exit=0 || got_fix_run_exit=$?
want_fix_run="$("$bang" run --engine=oracle "$tmpdir/deadprivate.bang" 2>/dev/null)"
check "lint-fix-w-preserves-value" "$got_fix_run" "$want_fix_run"
check "lint-fix-w-run-exit" "$got_fix_run_exit" "0"
got_fix_relint="$("$bang" lint "$tmpdir/fix-happy.bang" 2>/dev/null)" && got_fix_relint_exit=0 || got_fix_relint_exit=$?
check "lint-fix-w-relint-clean" "$got_fix_relint" "no findings"
check "lint-fix-w-relint-exit" "$got_fix_relint_exit" "0"

# a program with NOTHING fixable (only unused-pub, which has no fixit) is a correct no-op.
got_fix_nofix="$("$bang" lint --fix "$tmpdir/unusedpub.bang" 2>/dev/null)" && got_fix_nofix_exit=0 || got_fix_nofix_exit=$?
check "lint-fix-no-fixable-exit" "$got_fix_nofix_exit" "0"
check "lint-fix-no-fixable-message" "$(printf '%s' "$got_fix_nofix" | grep -c 'no fixable findings' || true)" "1"

# ══ 5c. THE REFUSED FIXIT — a `dataD` decl `dead-private` flags but the fixit CANNOT safely
# delete (`declMentionsVar`'s scan never sees a TYPE name, only `.var` leaves — a ctor call like
# `Mk(1,2)` references the ctor `Mk`, never the owning type `Pair`; a `deriving` clause references
# the type by name in a DECL HEADER, not a `Surf` node). Confirmed LIVE while building this fixit,
# not a hypothetical: `applyDeadPrivateFix` refuses every type-level decl kind UNCONDITIONALLY
# (`safeToAutoDelete`'s own #guards), so `--fix` never even ATTEMPTS this deletion — the mechanism
# itself is what a "planted wrong fixit" would need the gate to catch; here the refusal happens one
# layer earlier (never construct the bad edit at all), which is the STRONGER guarantee. ══

cat > "$tmpdir/dataderive.bang" <<'BANG'
data Pair = Mk(Int, Int) deriving (Eq)
let main = if Mk(1, 2) == Mk(1, 2) then 1 else 0
BANG

# `dead-private` DOES fire on `Pair` (the underlying scan-gap the rule itself still has —
# documented, not silently hidden: the FINDING is honest, only the auto-fixit is refused).
got_data_lint="$("$bang" lint "$tmpdir/dataderive.bang" 2>/dev/null)" && got_data_lint_exit=0 || got_data_lint_exit=$?
check "lint-dataderive-flags-pair" "$(printf '%s' "$got_data_lint" | grep -c 'dead-private Pair' || true)" "1"

# `--fix` reports it unfixable (no dataD/traitD/implD/effectD ever gets auto-deleted) — file
# untouched, EVEN before any preservation re-elaboration runs (the refusal is unconditional).
before_data_md5="$(md5sum "$tmpdir/dataderive.bang" | cut -d' ' -f1)"
got_data_fix="$("$bang" lint --fix "$tmpdir/dataderive.bang" 2>/dev/null)" && got_data_fix_exit=0 || got_data_fix_exit=$?
after_data_md5="$(md5sum "$tmpdir/dataderive.bang" | cut -d' ' -f1)"
check "lint-fix-refuses-dataD-exit" "$got_data_fix_exit" "0"
check "lint-fix-refuses-dataD-message" "$(printf '%s' "$got_data_fix" | grep -c 'no fixable findings' || true)" "1"
check "lint-fix-refuses-dataD-file-untouched" "$after_data_md5" "$before_data_md5"

# -w confirms the SAME refusal, and the program still runs to its ORIGINAL value (1) — proof the
# refusal, not luck, is what kept this program correct.
got_data_run_before="$("$bang" run --engine=oracle "$tmpdir/dataderive.bang" 2>/dev/null)"
"$bang" lint --fix "$tmpdir/dataderive.bang" -w >/dev/null 2>&1
got_data_run_after="$("$bang" run --engine=oracle "$tmpdir/dataderive.bang" 2>/dev/null)" && got_data_run_after_exit=0 || got_data_run_after_exit=$?
check "lint-fix-refuses-dataD-w-value-preserved" "$got_data_run_after" "$got_data_run_before"
check "lint-fix-refuses-dataD-w-run-exit" "$got_data_run_after_exit" "0"

# ══ 5d. `bang lint --fix` usage hygiene ══

got_fix_unreadable_exit=0
"$bang" lint --fix /no/such/file.bang >/dev/null 2>&1 || got_fix_unreadable_exit=$?
check "lint-fix-unreadable-file-exit" "$got_fix_unreadable_exit" "2"

got_fix_nofile="$("$bang" lint --fix 2>&1 >/dev/null)" && got_fix_nofile_exit=0 || got_fix_nofile_exit=$?
check "lint-fix-no-file-exit" "$got_fix_nofile_exit" "1"

# ══ 5. Usage / exit-code hygiene ══

got_unreadable_exit=0
"$bang" lint /no/such/file.bang >/dev/null 2>&1 || got_unreadable_exit=$?
check "lint-unreadable-file-exit" "$got_unreadable_exit" "2"

got_stdin="$(cat "$tmpdir/clean.bang" | "$bang" lint 2>/dev/null)" && got_stdin_exit=0 || got_stdin_exit=$?
check "lint-stdin-exit" "$got_stdin_exit" "0"
check "lint-stdin-clean" "$got_stdin" "no findings"

echo "──────────────────────────────"
echo "lint: $pass passed, $fail failed"
# Assert the expected total COUNT — catches a silently-truncated run.
want_total=38
got_total=$((pass + fail))
if [ "$got_total" -ne "$want_total" ]; then
  echo "✗ check-count-mismatch — expected $want_total checks to run, only $got_total did (script truncated?)"
  exit 1
fi
[ "$fail" -eq 0 ]
