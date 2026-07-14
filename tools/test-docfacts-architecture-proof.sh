#!/usr/bin/env bash
# tool: role=test couples=docfacts/architecture.json,docfacts/proof.json,tools/docfacts_architecture.py,tools/docfacts_proof.py runs-in=fitness
set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "$0")" && pwd)
ROOT=$(git -C "$SCRIPT_DIR/.." rev-parse --show-toplevel)
cd "$ROOT"

python3 tools/symbols.py --self-test
python3 tools/docfacts_architecture.py --self-test
python3 tools/docfacts_architecture.py --check
python3 tools/docfacts_proof.py --self-test
python3 tools/docfacts_proof.py --check
python3 tools/docfacts_proof.py --cross-check
python3 tools/check-architecture-assertions.py --self-test

python3 - <<'PY'
import copy
import json
import runpy
import sys
from pathlib import Path

from jsonschema.exceptions import ValidationError

root = Path.cwd()
sys.path.insert(0, str(root / "tools"))
from docfacts_architecture import SELF_TEST_POLES as ARCHITECTURE_POLES
from docfacts_proof import SELF_TEST_POLES as PROOF_POLES, validate_cross_fact
from genblock import splice

architecture = json.loads((root / "docfacts/architecture.json").read_text(encoding="utf-8"))
proof = json.loads((root / "docfacts/proof.json").read_text(encoding="utf-8"))

assert len(proof["specHeadlines"]) == 18, "Spec headline cardinality pole moved"
assert len(proof["enrollments"]) == 27, "Audit enrollment cardinality pole moved"
assert architecture["target"]["name"] == "Wasm 3.0"
assert architecture["engines"]["default"] == "env"
assert architecture["engines"]["aliases"] == {"--compiled": "compiled"}
assert ARCHITECTURE_POLES == 21, "architecture pole total moved"
assert PROOF_POLES == 16, "proof pole total moved"

mismatched = copy.deepcopy(proof)
mismatched["proofArrows"][1]["to"] = "mismatched-target"
try:
    validate_cross_fact(architecture, mismatched)
except ValidationError:
    pass
else:
    raise AssertionError("cross-fact endpoint mismatch was accepted")

for malformed in (
    "END body BEGIN",
    "BEGIN body END\nBEGIN body END",
):
    try:
        splice(malformed, "BEGIN", "END", "BEGIN generated END")
    except ValueError:
        pass
    else:
        raise AssertionError("malformed generated markers were accepted")

renderer = runpy.run_path(str(root / "tools/check-architecture-assertions.py"))
assert renderer["code"]("` **FLAGGED** `") == "`` ` **FLAGGED** ` ``"
assert renderer["mermaid_id"]("source-execution") == "n_source_execution"
import_graph = runpy.run_path(str(root / "tools/gen-import-graph.py"))
assert import_graph["node_id"]("Bang.Core.IR") == "component_Bang_dot_Core_dot_IR"
assert import_graph["node_id"]("Bang.A_B") != import_graph["node_id"]("Bang.A.B")
component_view = import_graph["render"](architecture)
assert "Frontend.Surface" not in component_view
for component in import_graph["COMPONENT_ORDER"]:
    assert f'{import_graph["node_id"](component)}["{component}<br/>' in component_view

print(
    "docfacts architecture/proof: PASS — "
    f"{len(architecture['modules'])} modules, "
    f"{len(architecture['adrs'])} ADRs, "
    f"{len(proof['specHeadlines'])} Spec headlines, "
    f"{len(proof['enrollments'])} Audit enrollments, "
    f"{ARCHITECTURE_POLES}+{PROOF_POLES} falsification poles."
)
PY
