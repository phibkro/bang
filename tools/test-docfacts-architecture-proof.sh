#!/usr/bin/env bash
# tool: role=test couples=docfacts/architecture.json,docfacts/proof.json,tools/docfacts_architecture.py,tools/docfacts_proof.py runs-in=fitness
set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "$0")" && pwd)
ROOT=$(git -C "$SCRIPT_DIR/.." rev-parse --show-toplevel)
cd "$ROOT"

python3 tools/docfacts_architecture.py --self-test
python3 tools/docfacts_architecture.py --check
python3 tools/docfacts_proof.py --self-test
python3 tools/docfacts_proof.py --check
python3 tools/docfacts_proof.py --cross-check

python3 - <<'PY'
import copy
import json
import sys
from pathlib import Path

from jsonschema.exceptions import ValidationError

root = Path.cwd()
sys.path.insert(0, str(root / "tools"))
from docfacts_architecture import SELF_TEST_POLES as ARCHITECTURE_POLES
from docfacts_proof import SELF_TEST_POLES as PROOF_POLES, validate_cross_fact

architecture = json.loads((root / "docfacts/architecture.json").read_text(encoding="utf-8"))
proof = json.loads((root / "docfacts/proof.json").read_text(encoding="utf-8"))

assert len(proof["specHeadlines"]) == 18, "Spec headline cardinality pole moved"
assert len(proof["enrollments"]) == 27, "Audit enrollment cardinality pole moved"
assert architecture["target"]["name"] == "Wasm 3.0"
assert architecture["engines"]["default"] == "env"
assert architecture["engines"]["aliases"] == {"--compiled": "compiled"}
assert ARCHITECTURE_POLES == 21, "architecture pole total moved"
assert PROOF_POLES == 15, "proof pole total moved"

mismatched = copy.deepcopy(proof)
mismatched["proofArrows"][1]["to"] = "mismatched-target"
try:
    validate_cross_fact(architecture, mismatched)
except ValidationError:
    pass
else:
    raise AssertionError("cross-fact endpoint mismatch was accepted")

print(
    "docfacts architecture/proof: PASS — "
    f"{len(architecture['modules'])} modules, "
    f"{len(architecture['adrs'])} ADRs, "
    f"{len(proof['specHeadlines'])} Spec headlines, "
    f"{len(proof['enrollments'])} Audit enrollments, "
    f"{ARCHITECTURE_POLES}+{PROOF_POLES} falsification poles."
)
PY
