#!/usr/bin/env bash
# tool: role=test couples=CONTEXT.md,docfacts/architecture.json,docfacts/proof-claims.json,docfacts/proof.json,docfacts/schema/proof-claims.schema.json,tools/docfacts_architecture.py,tools/docfacts_proof.py,tools/gen-proof-state.py runs-in=fitness
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

assert len(proof["specHeadlines"]) == 23, "Spec headline cardinality pole moved"
assert len(proof["enrollments"]) == 33, "Audit enrollment cardinality pole moved"
assert {item["kind"] for item in proof["specHeadlines"]} == {"theorem"}
assert all(item["claimKind"] != "theorem" for item in proof["enrollments"]), (
    "syntactic Lean theorem kind collapsed into semantic claim status"
)
assert architecture["target"]["name"] == "Wasm 3.0"
assert architecture["engines"]["default"] == "env"
assert architecture["engines"]["selectors"] == {
    "--engine=oracle": "oracle",
    "--engine=compiled": "compiled",
    "--engine=env": "env",
}
assert architecture["engines"]["aliases"] == {"--compiled": "compiled"}
assert architecture["engines"]["duplicatePolicy"] == "reject"
assert architecture["engines"]["selectorCommands"] == ["run", "eval", "repl"]
assert ARCHITECTURE_POLES == 29, "architecture pole total moved"
assert PROOF_POLES == 25, "proof pole total moved"

mismatched = copy.deepcopy(proof)
mismatched["proofArrows"][1]["to"] = "mismatched-target"
try:
    validate_cross_fact(architecture, mismatched)
except ValidationError:
    pass
else:
    raise AssertionError("cross-fact endpoint mismatch was accepted")

laundered_architecture = copy.deepcopy(architecture)
next(
    arrow
    for arrow in laundered_architecture["arrows"]
    if arrow["id"] == "evald-to-calcvm"
)["theoremRefs"] = ["Bang.compileC_satisfies_current_instrWF"]
try:
    validate_cross_fact(laundered_architecture, proof)
except ValidationError:
    pass
else:
    raise AssertionError("architecture arrow accepted semantically incompatible theorem support")

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

proof_state = runpy.run_path(str(root / "tools/gen-proof-state.py"))
semantic_inventory = proof_state["semantic_inventory"](str(root))
role_counts = {}
for record in semantic_inventory.values():
    role_counts[record["claimRole"]] = role_counts.get(record["claimRole"], 0) + 1
assert role_counts == {
    "canonical": 18,
    "supporting": 8,
    "deprecated-alias": 5,
    "alias": 1,
    "placeholder": 1,
}, "proof-state semantic roles drifted"
context = (root / "CONTEXT.md").read_text(encoding="utf-8")
assert "**claims:** 22 trusted-axiom (⊆ trusted-3) · 0 pending (build in flight) · 4 flagged (aliases/placeholders excluded)" in context
assert "**enrollment roles:** 18 canonical · 8 supporting · 6 aliases · 1 placeholder" in context
assert "**flagged:** `handler_compiles`" not in context
assert "**placeholder:** `handler_lowering_placeholder`" in context

print(
    "docfacts architecture/proof: PASS — "
    f"{len(architecture['modules'])} modules, "
    f"{len(architecture['adrs'])} ADRs, "
    f"{len(proof['specHeadlines'])} Spec headlines, "
    f"{len(proof['enrollments'])} Audit enrollments, "
    f"{ARCHITECTURE_POLES}+{PROOF_POLES} falsification poles."
)
PY
