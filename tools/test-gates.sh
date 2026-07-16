#!/usr/bin/env bash
# tool: role=check couples=tools/check.sh,tools/hooks/post-edit-check.sh,tools/burndown.sh,tools/docfacts_proof.py runs-in=verify
# test-gates.sh — falsification tests for the fail-closed developer/proof gates.
set -euo pipefail

ROOT="$(git rev-parse --show-toplevel)"
cd "$ROOT"
tmpdir="$(mktemp -d)"
trap 'rm -rf "$tmpdir"' EXIT

checked=0
check() {
  local name="$1" got="$2" want="$3"
  checked=$((checked + 1))
  if [ "$got" != "$want" ]; then
    echo "FAIL: $name" >&2
    echo "  got:  $got" >&2
    echo "  want: $want" >&2
    exit 1
  fi
}

mkdir -p "$tmpdir/bin" "$tmpdir/lean"
printf 'theorem fixture : True := by trivial\n' > "$tmpdir/lean/Fixture.lean"
cat > "$tmpdir/bin/lake" <<'SH'
#!/usr/bin/env bash
printf '%s\n' "${FAKE_LAKE_OUT:-}"
exit "${FAKE_LAKE_RC:-0}"
SH
chmod +x "$tmpdir/bin/lake"

# The old checker swallowed this status and missed the path-prefixed/category
# diagnostic. Both facts are asserted so output parsing cannot launder failure.
set +e
check_out="$(PATH="$tmpdir/bin:$PATH" FAKE_LAKE_RC=7 \
  FAKE_LAKE_OUT="$tmpdir/lean/Fixture.lean:1:0: error(lean.unknownIdentifier): bad" \
  bash tools/check.sh "$tmpdir/lean/Fixture.lean" 2>&1)"
check_rc=$?
set -e
check "per-file-invalid-exit" "$check_rc" "7"
check "per-file-path-diagnostic" \
  "$(printf '%s\n' "$check_out" | grep -c 'error(lean.unknownIdentifier): bad' || true)" "1"
check "per-file-no-false-green" \
  "$(printf '%s\n' "$check_out" | grep -c '✓ no errors or warnings' || true)" "0"

# More than 40 lines in the unfamiliar-format fallback used to SIGPIPE `printf`
# through `head` under pipefail, replacing Lean's distinctive status with 141.
long_out="$(for n in $(seq 1 60); do printf 'unclassified failure line %s\n' "$n"; done)"
set +e
long_check_out="$(PATH="$tmpdir/bin:$PATH" FAKE_LAKE_RC=23 \
  FAKE_LAKE_OUT="$long_out" bash tools/check.sh "$tmpdir/lean/Fixture.lean" 2>&1)"
long_check_rc=$?
set -e
check "per-file-long-fallback-preserves-exit" "$long_check_rc" "23"
check "per-file-long-fallback-no-false-green" \
  "$(printf '%s\n' "$long_check_out" | grep -c '✓ no errors or warnings' || true)" "0"

set +e
clean_out="$(PATH="$tmpdir/bin:$PATH" FAKE_LAKE_RC=0 FAKE_LAKE_OUT='' \
  bash tools/check.sh "$tmpdir/lean/Fixture.lean" 2>&1)"
clean_rc=$?
set -e
check "per-file-valid-exit" "$clean_rc" "0"
check "per-file-valid-green" \
  "$(printf '%s\n' "$clean_out" | grep -c '✓ no errors or warnings' || true)" "1"

printf 'def knownBad : Nat := definitelyMissing\n' > "$tmpdir/lean/KnownBad.lean"
set +e
real_bad_out="$(bash tools/check.sh "$tmpdir/lean/KnownBad.lean" 2>&1)"
real_bad_rc=$?
set -e
check "per-file-real-invalid-exit-nonzero" "$((real_bad_rc != 0))" "1"
check "per-file-real-invalid-diagnostic" \
  "$(printf '%s\n' "$real_bad_out" | grep -c 'definitelyMissing' || true)" "1"

# The post-edit hook is intentionally advisory, but it must surface the complete
# path-prefixed diagnostic as structured agent context instead of a false green.
# It reads but does not modify the real Spec file.
hook_input="$(printf '{\"tool_input\":{\"file_path\":\"%s/Bang/Spec.lean\"}}' "$ROOT")"
set +e
hook_out="$(printf '%s' "$hook_input" | PATH="$tmpdir/bin:$PATH" \
  CLAUDE_PROJECT_DIR="$ROOT" BANG_POST_EDIT_CHECK_NO_NIX=1 FAKE_LAKE_RC=9 \
  FAKE_LAKE_OUT='Bang/Spec.lean:1:0: error: injected hook failure' \
  bash tools/hooks/post-edit-check.sh 2>&1)"
hook_rc=$?
set -e
check "post-edit-advisory-exit" "$hook_rc" "0"
check "post-edit-surfaces-path-diagnostic" \
  "$(printf '%s\n' "$hook_out" | grep -c 'error: injected hook failure' || true)" "1"

# Burndown counts code tokens, not mentions in nested/line comments or strings.
mkdir -p "$tmpdir/burndown"
cat > "$tmpdir/burndown/Counts.lean" <<'LEAN'
-- sorry axiom
/- outer sorry /- nested sorry -/ axiom -/
def prose := "sorry axiom"
theorem pending : True := by sorry
axiom declared : True
LEAN
burndown_out="$(bash tools/burndown.sh "$tmpdir/burndown")"
check "burndown-real-sorry-token" \
  "$(printf '%s\n' "$burndown_out" | awk '$1 == "TOTAL" {print $2}')" "1"
check "burndown-real-axiom-decl" \
  "$(printf '%s\n' "$burndown_out" | awk '$1 == "TOTAL" {print $3}')" "1"

# The landed proof fact is the machine-readable baseline. Exercise the exact
# live-check comparison with injected new dependencies; both must be rejected.
proof_out="$(TMPDIR="$tmpdir" python3 - <<'PY'
import copy
import os
import sys
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, "tools")
import docfacts_proof as proof

baseline = proof.build_fact(proof.synthetic_report_entries())
proof.validate_fact(baseline)
baseline_path = Path(os.environ["TMPDIR"]) / "proof-baseline.json"
baseline_path.write_text(proof.render_json(baseline), encoding="utf-8")

def rejected(axiom):
    live = copy.deepcopy(baseline)
    target = next(
        item for item in live["enrollments"]
        if item["writtenRef"] == "compile_well_typed"
    )
    target["axioms"] = sorted(set(target["axioms"] + [axiom]))
    target["axiomTrust"] = "flagged"
    with patch.object(proof, "FACT_PATH", baseline_path), \
         patch.object(proof, "live_fact", return_value=live):
        try:
            proof.check_output(live=True)
        except proof.ProofFactsError:
            return True
    return False

print(f"new-sorry={int(rejected('sorryAx'))}")
print(f"new-untrusted={int(rejected('Bang.unsoundAxiom'))}")
PY
)"
check "proof-live-rejects-new-sorry" \
  "$(printf '%s\n' "$proof_out" | sed -n 's/^new-sorry=//p')" "1"
check "proof-live-rejects-new-untrusted" \
  "$(printf '%s\n' "$proof_out" | sed -n 's/^new-untrusted=//p')" "1"

check "final-check-count" "$checked" "15"
echo "gate falsification tests: 15/15 passed"
