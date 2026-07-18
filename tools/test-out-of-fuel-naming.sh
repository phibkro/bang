#!/usr/bin/env bash
# tool: role=test couples=Bang/Core/Semantics/Eval.lean,Bang/Core/IR.lean,Bang/Core/Fingerprint.lean,Bang/Frontend/Surface.lean,Bang/Frontend/NamedCore.lean,Bang/Witness/ProofExport.lean,web/run-service/README.md,docs/notes/questions/Q32-memoization-combinator.md runs-in=verify
source "$(git rev-parse --show-toplevel 2>/dev/null)/tools/tool-log.sh" 2>/dev/null && tool_log "$(basename "$0")" || true
# Falsification poles for #172's semantic rename. The fuel-bounded Result/Outcome
# constructors must stay distinct from the legacy Comp/NComp sentinel and real
# allocation-memory terminology.
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"

python3 - <<'PY'
from pathlib import Path
import re
import subprocess


def read(path: str) -> str:
    return Path(path).read_text(encoding="utf-8")


def constructor_names(text: str, inductive: str, stop: str) -> list[str]:
    body = text.split(f"inductive {inductive}", 1)[1].split(stop, 1)[0]
    return re.findall(r"^\s*\|\s*([A-Za-z][A-Za-z0-9_]*)\b", body, re.MULTILINE)


def assert_contract(eval_text: str, surface_text: str) -> None:
    assert constructor_names(eval_text, "Result", "/-!") == [
        "done", "outOfFuel", "escapedCap", "stuck"
    ]
    assert constructor_names(surface_text, "Outcome", "-- (`Outcome.beq") == [
        "parseErr", "typeErr", "yields", "outOfFuel", "escaped", "stuck"
    ]
    assert "| 0, _              => .outOfFuel" in eval_text
    assert "| .outOfFuel  => .outOfFuel" in surface_text


eval_text = read("Bang/Core/Semantics/Eval.lean")
surface_text = read("Bang/Frontend/Surface.lean")
assert_contract(eval_text, surface_text)
print("  ✓ Result and Outcome expose outOfFuel, never an oom constructor")

assert "@[match_pattern, deprecated Result.outOfFuel" in eval_text
assert "def Result.oom" in eval_text
assert "@[match_pattern, deprecated Outcome.outOfFuel" in surface_text
assert "def Outcome.oom" in surface_text
assert "@[deprecated assertOutOfFuel" in surface_text
assert "def assertOom" in surface_text
typecheck_text = read("Bang/Frontend/TypeCheck.lean")
assert "@[deprecated assertTypedOutOfFuel" in typecheck_text
assert "def assertTypedOom" in typecheck_text
print("  ✓ bounded deprecated aliases retain source compatibility")

# There must be no use of the old qualified names outside their declarations.
qualified = []
tracked = subprocess.run(
    ["git", "ls-files", "-z"], check=True, capture_output=True
).stdout.decode("utf-8").split("\0")
for name in tracked:
    if not name:
        continue
    path = Path(name)
    if path.as_posix() == "tools/test-out-of-fuel-naming.sh":
        continue
    if path.suffix != ".lean":
        continue
    for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if "Result.oom" in line and "def Result.oom" not in line:
            qualified.append(f"{path}:{number}: Result.oom")
        if "Outcome.oom" in line and "def Outcome.oom" not in line:
            qualified.append(f"{path}:{number}: Outcome.oom")
assert not qualified, "stale qualified names:\n" + "\n".join(qualified)
print("  ✓ no repository consumer uses the compatibility constructor names")

ir_text = read("Bang/Core/IR.lean")
named_text = read("Bang/Frontend/NamedCore.lean")
export_text = read("Bang/Witness/ProofExport.lean")
fingerprint_text = read("Bang/Core/Fingerprint.lean")
assert re.search(r"^\s*\| oom\s+: Comp$", ir_text, re.MULTILINE)
assert re.search(r"^\s*\| oom\s+: NComp$", named_text, re.MULTILINE)
assert re.search(r"\| \.oom\s+=> tag 21", fingerprint_text)
assert '=> "Bang.Comp.oom"' in export_text
print("  ✓ Comp.oom, NComp.oom, and shared structural tag 21 remain byte-stable")

assert "OOM-kill" in read("web/run-service/README.md")
assert "surprising `oom`" in read("docs/notes/questions/Q32-memoization-combinator.md")
tour_text = read("docs/notes/interactive-tour-design.md")
assert "| Memory blowup |" in tour_text and "MemoryMax (cgroup)" in tour_text
print("  ✓ genuine allocation-memory terminology remains intact")

# Falsify both boundaries in memory: restoring either old constructor must be rejected.
for name, bad_eval, bad_surface in [
    ("Result constructor relapse", eval_text.replace("| outOfFuel : Result α", "| oom : Result α", 1), surface_text),
    ("Outcome constructor relapse", eval_text, surface_text.replace("| outOfFuel : Outcome", "| oom : Outcome", 1)),
]:
    try:
        assert_contract(bad_eval, bad_surface)
    except AssertionError:
        print(f"  ✓ falsified {name}")
    else:
        raise AssertionError(f"mutation unexpectedly passed: {name}")
PY

probe="$(mktemp --tmpdir bang-out-of-fuel-compat-XXXXXX.lean)"
probe_log="$(mktemp --tmpdir bang-out-of-fuel-compat-XXXXXX.log)"
trap 'rm -f "$probe" "$probe_log"' EXIT
cat >"$probe" <<'LEAN'
import Bang.Frontend.TypeCheck

open Bang
open Bang.Surface

def legacyResultConstruct : Result Nat := .oom
def legacyResultQualified : Result Nat := Result.oom
def legacyResultMatch : Result Nat → Nat
  | .done _ => 0
  | .oom => 1
  | .escapedCap => 2
  | .stuck => 3

def legacyOutcomeConstruct : Outcome := .oom
def legacyOutcomeQualified : Outcome := Outcome.oom
def legacyOutcomeMatch : Outcome → Nat
  | .parseErr _ _ => 0
  | .typeErr _ => 1
  | .yields _ => 2
  | .oom => 3
  | .escaped => 4
  | .stuck => 5

def legacySurfaceHelper : Bool := assertOom 0 "0"
def legacyTypedHelper : Bool := Bang.TypeCheck.assertTypedOom 0 "0"
LEAN

lake env lean "$probe" >"$probe_log" 2>&1 || {
  cat "$probe_log" >&2
  echo "FAIL: deprecated compatibility aliases do not elaborate" >&2
  exit 1
}
grep -Fq 'deprecated: Use `Bang.Result.outOfFuel` instead' "$probe_log"
grep -Fq 'deprecated: Use `Bang.Surface.Outcome.outOfFuel` instead' "$probe_log"
echo "  ✓ deprecated aliases compile for construction, exhaustive patterns, and helper calls"

echo "test-out-of-fuel-naming: 8/8 poles passed."
