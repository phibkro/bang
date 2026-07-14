#!/usr/bin/env python3
# tool: role=gen couples=Bang/**/*.lean,Main.lean,docs/decisions/*.md,docfacts/schema/architecture.schema.json,docfacts/architecture.json runs-in=fitness
"""Generate and validate the source-derived BANG architecture documentation fact."""

from __future__ import annotations

import argparse
import copy
import json
import sys
import tempfile
from collections import defaultdict
from pathlib import Path

from jsonschema.exceptions import ValidationError

import adr_facts
from architecture_facts import (
    ArchitectureFactsError,
    derive_decision_details,
    derive_engine_details,
    proof_arrow_semantics,
)
from docfacts_common import (
    check_evidence_sources,
    check_sorted_unique,
    checked_repo_path,
    reject_duplicate_ids,
    reload_and_validate,
    render_json,
    schema_validator,
    serialization_consumer_pole,
    validate_evidence_commands,
)
from import_facts import ImportFactsError, scan_bang
from symbols import SymbolFactsError, collect_public_symbols

ROOT = Path(__file__).resolve().parent.parent
SCHEMA_PATH = ROOT / "docfacts/schema/architecture.schema.json"
FACT_PATH = ROOT / "docfacts/architecture.json"
SELF_TEST_POLES = 21


def evidence() -> list[dict]:
    return [
        {
            "id": "frontend-differential",
            "label": "differential-tested",
            "claim": "Surface text is parsed, type-checked, lowered to Comp, and exercised against the execution oracles by the real example battery.",
            "sources": [
                "Bang/Frontend/Surface.lean",
                "Bang/Frontend/TypeCheck.lean",
                "tools/check-examples.sh",
            ],
            "commands": ["bash tools/check-examples.sh"],
        },
        {
            "id": "kernel-implemented",
            "label": "implemented",
            "claim": "Source.eval directly interprets lowered Comp as the substitution-based kernel oracle.",
            "sources": [
                "Bang/Core/Semantics.lean",
                "Bang/Core/Semantics/Eval.lean",
                "Main.lean",
            ],
            "commands": ["lake build Bang.Core.Semantics"],
        },
        {
            "id": "evald-source-proof",
            "label": "proven",
            "claim": "Bang.CalcVM.evalD_agrees_source proves that an evalD return from empty stores for a VcapFree Comp is reproduced by Source.eval; the claim retains those premises and does not assert an unconditional equivalence.",
            "sources": ["Bang/Backend/AbstractMachine.lean", "Bang/Audit.lean"],
            "commands": ["lake env lean Bang/Audit.lean"],
        },
        {
            "id": "calcvm-calculation-proof",
            "label": "proven",
            "claim": "Bang.CalcVM.compile_correct proves that a terminating evalD run from empty stores has some fuel for which exec of compile returns the same terminal; the existential-fuel and evalD-success premises remain explicit.",
            "sources": ["Bang/Backend/AbstractMachine.lean", "Bang/Audit.lean"],
            "commands": ["lake env lean Bang/Audit.lean"],
        },
        {
            "id": "env-implemented-differential",
            "label": "differential-tested",
            "claim": "The env/readback path is implemented as the default engine and is differentially tested against the oracle; evalE_agrees_evalD is not Audit-enrolled, so this fact does not label the boundary proven.",
            "sources": [
                "Bang/Backend/EnvMachine.lean",
                "Main.lean",
                "tools/check-examples-env.sh",
            ],
            "commands": ["bash tools/check-examples-env.sh"],
        },
        {
            "id": "formal-target-simulation-proof",
            "label": "proven",
            "claim": "Bang.compile_forward_sim proves value-preserving source execution to the formal target execution for VcapFree source Comp. The Lean namespace Wasmfx is historical; ADR-0059 makes Wasm 3.0 the product target.",
            "sources": [
                "Bang/Spec.lean",
                "Bang/Backend/Wasm.lean",
                "Bang/Audit.lean",
                "docs/decisions/0059-wasm3-grade-directed-pluggable-backend.md",
            ],
            "commands": ["lake env lean Bang/Audit.lean"],
        },
        {
            "id": "wat-emitter-implemented",
            "label": "implemented",
            "claim": "The concrete WasmGC emitter lowers Comp to WAT independently of the formal Wasm model.",
            "sources": ["Bang/Backend/WasmEmit.lean"],
            "commands": ["lake build Bang.Backend.WasmEmit"],
        },
        {
            "id": "wasmtime-differential",
            "label": "differential-tested",
            "claim": "Emitted WAT is run by real Wasmtime and compared with the source result by the emission differential harnesses.",
            "sources": ["tools/emit-rung4-diff.sh", "tools/emit-rung5-effects-diff.sh"],
            "commands": [
                "bash tools/emit-rung4-diff.sh",
                "bash tools/emit-rung5-effects-diff.sh",
            ],
        },
        {
            "id": "lr-theorems-enrolled",
            "label": "implemented",
            "claim": "The binary-LR contextual-equivalence theorem statements are implemented and Audit-enrolled, but their live axiom sets determine trust; this architecture fact does not promote flagged entries to proven.",
            "sources": [
                "Bang/Spec.lean",
                "Bang/Meta/LR.lean",
                "Bang/Meta/BinaryLR.lean",
                "Bang/Audit.lean",
            ],
            "commands": ["lake env lean Bang/Audit.lean"],
        },
    ]


def nodes() -> list[dict]:
    records = [
        (
            "calcvm",
            "CalcVM compile + exec",
            "machine",
            ["Bang/Backend/AbstractMachine.lean"],
        ),
        ("comp", "Graded-CBPV Comp", "core-ir", ["Bang/Core/IR.lean"]),
        ("emitted-wat", "WasmGC / WAT", "emitted-wat", ["Bang/Backend/WasmEmit.lean"]),
        (
            "env-engine",
            "evalE default engine",
            "environment-machine",
            ["Bang/Backend/EnvMachine.lean", "Main.lean"],
        ),
        ("evald", "evalD", "state-semantics", ["Bang/Backend/AbstractMachine.lean"]),
        (
            "formal-target",
            "Formal Wasm 3.0 machine",
            "formal-target",
            [
                "Bang/Backend/Wasm.lean",
                "docs/decisions/0059-wasm3-grade-directed-pluggable-backend.md",
            ],
        ),
        (
            "source-eval",
            "Source.eval oracle",
            "source-semantics",
            ["Bang/Core/Semantics/Eval.lean"],
        ),
        (
            "source-execution",
            "Source execution",
            "source-execution",
            ["Bang/Spec.lean"],
        ),
        (
            "source-program-left",
            "Source program P",
            "source-program",
            ["Bang/Spec.lean", "Bang/Meta/BinaryLR.lean"],
        ),
        (
            "source-program-right",
            "Source program Q",
            "source-program",
            ["Bang/Spec.lean", "Bang/Meta/BinaryLR.lean"],
        ),
        ("source-text", "Source text", "text", ["Bang/Frontend/Surface.lean"]),
        (
            "target-execution",
            "Formal target execution",
            "target-execution",
            ["Bang/Backend/Wasm.lean"],
        ),
        ("wasmtime", "Wasmtime", "runtime", ["tools/emit-rung4-diff.sh"]),
    ]
    return [
        {"id": record_id, "name": name, "kind": kind, "sources": sources}
        for record_id, name, kind, sources in records
    ]


def arrows() -> list[dict]:
    return [
        {
            "id": "source-execution-to-formal-target",
            "from": "source-execution",
            "to": "target-execution",
            "direction": "forward",
            "method": "annotated forward simulation",
            "theoremRefs": ["Bang.compile_forward_sim"],
            "adrRefs": ["0035", "0059"],
            "evidenceId": "formal-target-simulation-proof",
        },
        {
            "id": "comp-to-emitted-wat",
            "from": "comp",
            "to": "emitted-wat",
            "direction": "forward",
            "method": "WasmGC text emission",
            "theoremRefs": [],
            "adrRefs": [],
            "evidenceId": "wat-emitter-implemented",
        },
        {
            "id": "comp-to-source-eval",
            "from": "comp",
            "to": "source-eval",
            "direction": "forward",
            "method": "kernel interpretation",
            "theoremRefs": [],
            "adrRefs": [],
            "evidenceId": "kernel-implemented",
        },
        {
            "id": "emitted-wat-to-wasmtime",
            "from": "emitted-wat",
            "to": "wasmtime",
            "direction": "forward",
            "method": "real-engine execution",
            "theoremRefs": [],
            "adrRefs": [],
            "evidenceId": "wasmtime-differential",
        },
        {
            "id": "evald-to-calcvm",
            "from": "evald",
            "to": "calcvm",
            "direction": "forward",
            "method": "calculation",
            "theoremRefs": ["Bang.CalcVM.compile_correct"],
            "adrRefs": ["0016"],
            "evidenceId": "calcvm-calculation-proof",
        },
        {
            "id": "evald-to-env",
            "from": "evald",
            "to": "env-engine",
            "direction": "forward",
            "method": "environment evaluation and readback",
            "theoremRefs": [],
            "adrRefs": [],
            "evidenceId": "env-implemented-differential",
        },
        {
            "id": "source-eval-to-evald",
            "from": "source-eval",
            "to": "evald",
            "direction": "forward",
            "method": "state reification",
            "theoremRefs": ["Bang.CalcVM.evalD_agrees_source"],
            "adrRefs": ["0016"],
            "evidenceId": "evald-source-proof",
        },
        {
            "id": "source-text-to-comp",
            "from": "source-text",
            "to": "comp",
            "direction": "forward",
            "method": "frontend lowering",
            "theoremRefs": [],
            "adrRefs": [],
            "evidenceId": "frontend-differential",
        },
    ]


def proof_arrows() -> list[dict]:
    metadata = {
        "contextual-equivalence": {
            "adrRefs": ["0035"],
            "evidenceId": "lr-theorems-enrolled",
        },
        "source-target-forward-simulation": {
            "adrRefs": ["0035", "0059"],
            "evidenceId": "formal-target-simulation-proof",
        },
    }
    return [
        semantics | metadata[semantics["id"]] for semantics in proof_arrow_semantics()
    ]


def build_adrs(implemented_ids: set[str]) -> list[dict]:
    collected = adr_facts.collect(ROOT / "docs/decisions")
    records = []
    for adr in collected:
        fields = adr["fields"]
        status = adr_facts.status_of(fields)
        lifecycle = []
        if status == "Proposed":
            lifecycle = ["proposed"]
        elif status == "Superseded":
            lifecycle = ["superseded"]
        elif status == "Accepted" and adr["num"] in implemented_ids:
            lifecycle = ["implemented"]
        records.append(
            {
                "id": adr["num"],
                "status": status,
                "title": adr["title"],
                "summary": fields.get("summary", ""),
                "path": f"docs/decisions/{adr['file']}",
                "relationships": adr_facts.relationship_fields(fields),
                "derived": {
                    "supersededBy": adr["superseded_by"],
                    "amendedBy": adr["amended_by"],
                },
                "lifecycle": lifecycle,
            }
        )
    return records


def build_fact() -> dict:
    imports = scan_bang(ROOT)
    public_by_module: dict[str, list[dict]] = defaultdict(list)
    source_paths = [ROOT / module.path for module in imports.modules.values()]
    for symbol in collect_public_symbols(ROOT, source_paths):
        public_by_module[symbol["module"]].append(
            {key: symbol[key] for key in ("name", "kind", "line", "visibilityBasis")}
        )
    modules = []
    tier_counts: dict[str, list[int]] = defaultdict(lambda: [0, 0])
    for name, module in sorted(imports.modules.items()):
        symbols = sorted(
            public_by_module.get(name, []),
            key=lambda item: (item["line"], item["kind"], item["name"]),
        )
        modules.append(
            {
                "name": name,
                "path": module.path.as_posix(),
                "tier": module.tier,
                "loc": module.loc,
                "directImports": sorted(module.imports),
                "publicSymbols": symbols,
            }
        )
        tier_counts[module.tier][0] += 1
        tier_counts[module.tier][1] += module.loc
    decisions = derive_decision_details(ROOT)
    engine_details = derive_engine_details(ROOT / "Main.lean")
    pipeline_arrows = sorted(arrows(), key=lambda item: item["id"])
    method_arrows = proof_arrows()
    implemented_ids = set(engine_details["decisionRefs"])
    for arrow in pipeline_arrows + method_arrows:
        implemented_ids.update(arrow["adrRefs"])
    return {
        "schemaVersion": 1,
        "kind": "architecture",
        "id": "architecture",
        "title": "BANG architecture",
        "summary": "Source-derived module, engine, decision, pipeline, and evidence facts for the verified-core/tested-superset architecture.",
        "target": decisions["target"],
        "proofMethods": decisions["proofMethods"],
        "engines": engine_details,
        "tiers": [
            {"name": name, "moduleCount": values[0], "loc": values[1]}
            for name, values in sorted(tier_counts.items())
        ],
        "modules": modules,
        "nodes": nodes(),
        "arrows": pipeline_arrows,
        "proofArrows": method_arrows,
        "adrs": build_adrs(implemented_ids),
        "evidence": sorted(evidence(), key=lambda item: item["id"]),
    }


def validate_fact(fact: dict) -> None:
    schema_validator(SCHEMA_PATH).validate(fact)
    authoritative = build_fact()
    for field in ("target", "proofMethods", "engines", "tiers", "modules", "adrs"):
        if fact[field] != authoritative[field]:
            raise ValidationError(
                f"{field} does not match its source-derived inventory"
            )
    check_sorted_unique(fact["tiers"], lambda item: item["name"], "tiers")
    check_sorted_unique(fact["modules"], lambda item: item["name"], "modules")
    check_sorted_unique(fact["nodes"], lambda item: item["id"], "nodes")
    check_sorted_unique(fact["arrows"], lambda item: item["id"], "arrows")
    check_sorted_unique(fact["proofArrows"], lambda item: item["id"], "proof arrows")
    check_sorted_unique(fact["adrs"], lambda item: item["id"], "ADRs")
    check_sorted_unique(fact["evidence"], lambda item: item["id"], "evidence")
    for module in fact["modules"]:
        if module["directImports"] != sorted(set(module["directImports"])):
            raise ValidationError(
                f"direct imports are not sorted/unique: {module['name']}"
            )
        expected_symbols = sorted(
            module["publicSymbols"],
            key=lambda item: (item["line"], item["kind"], item["name"]),
        )
        if module["publicSymbols"] != expected_symbols or len(
            {(s["name"], s["kind"], s["line"]) for s in expected_symbols}
        ) != len(expected_symbols):
            raise ValidationError(
                f"public symbols are not deterministic: {module['name']}"
            )
        checked_repo_path(ROOT, module["path"])
    check_evidence_sources(ROOT, fact["evidence"])
    for node in fact["nodes"]:
        for source in node["sources"]:
            checked_repo_path(ROOT, source)
    validate_evidence_commands(ROOT, fact["evidence"])

    all_structural = fact["nodes"] + fact["arrows"] + fact["proofArrows"]
    reject_duplicate_ids(fact["evidence"] + all_structural, "architecture/evidence")
    node_ids = {node["id"] for node in fact["nodes"]}
    evidence_by_id = {record["id"]: record for record in fact["evidence"]}
    for arrow in fact["arrows"] + fact["proofArrows"]:
        if arrow["from"] not in node_ids or arrow["to"] not in node_ids:
            raise ValidationError(f"arrow endpoint is not a node: {arrow['id']}")
        if arrow["evidenceId"] not in evidence_by_id:
            raise ValidationError(f"arrow evidence is missing: {arrow['id']}")
        if (
            evidence_by_id[arrow["evidenceId"]]["label"] == "proven"
            and not arrow["theoremRefs"]
        ):
            raise ValidationError(f"proven arrow has no theorem support: {arrow['id']}")

    semantic_keys = (
        "id",
        "from",
        "to",
        "endpointType",
        "direction",
        "method",
        "theoremRefs",
    )
    actual_semantics = [
        {key: arrow[key] for key in semantic_keys} for arrow in fact["proofArrows"]
    ]
    if actual_semantics != proof_arrow_semantics():
        raise ValidationError(
            "LR contextual equivalence and forward simulation semantics drifted"
        )

    by_adr = {adr["id"]: adr for adr in fact["adrs"]}
    if fact["engines"]["decisionRefs"] != sorted(set(fact["engines"]["decisionRefs"])):
        raise ValidationError("engine decision refs are not sorted/unique")
    implemented_ids = set(fact["engines"]["decisionRefs"])
    for arrow in fact["arrows"] + fact["proofArrows"]:
        if arrow["adrRefs"] != sorted(set(arrow["adrRefs"])):
            raise ValidationError(f"ADR refs are not sorted/unique: {arrow['id']}")
        implemented_ids.update(arrow["adrRefs"])
    unknown_decisions = implemented_ids - set(by_adr)
    if unknown_decisions:
        raise ValidationError(
            f"architecture cites unknown ADRs: {sorted(unknown_decisions)}"
        )
    for adr in fact["adrs"]:
        expected = []
        if adr["status"] == "Proposed":
            expected = ["proposed"]
        elif adr["status"] == "Superseded":
            expected = ["superseded"]
            if not adr["derived"]["supersededBy"]:
                raise ValidationError(f"superseded ADR has no successor: {adr['id']}")
        elif adr["status"] == "Accepted" and adr["id"] in implemented_ids:
            expected = ["implemented"]
        if adr["lifecycle"] != expected:
            raise ValidationError(
                f"invalid ADR lifecycle for {adr['id']}: {adr['lifecycle']}"
            )
        for successor in adr["derived"]["supersededBy"]:
            if adr["id"] not in adr_facts.nums(
                by_adr[successor]["relationships"].get("supersedes", "")
            ):
                raise ValidationError(
                    f"broken inverse supersession: {adr['id']} -> {successor}"
                )


def parse_fact(serialized: str) -> dict:
    return reload_and_validate(
        serialized, schema_validator(SCHEMA_PATH), [validate_fact]
    )


def render_consumer(fact: dict) -> str:
    return f"# {fact['title']}\n\n{fact['summary']}\n"


def expect_invalid(name: str, fact: dict) -> bool:
    try:
        validate_fact(fact)
    except (
        ValidationError,
        KeyError,
        ArchitectureFactsError,
        ImportFactsError,
        SymbolFactsError,
    ):
        print(f"✓ known-bad {name} rejected")
        return True
    print(f"✗ known-bad {name} was accepted", file=sys.stderr)
    return False


def self_test() -> int:
    base = build_fact()
    validate_fact(base)
    cases = []

    def mutate(name, change):
        fact = copy.deepcopy(base)
        change(fact)
        cases.append((name, fact))

    mutate("stale-target-wasmfx", lambda fact: fact["target"].update(name="WasmFX"))
    mutate(
        "stale-tier",
        lambda fact: fact["modules"][0].update(
            tier="Core" if fact["modules"][0]["tier"] != "Core" else "Backend"
        ),
    )
    mutate("missing-module", lambda fact: fact["modules"].pop())
    mutate(
        "invented-import",
        lambda fact: fact["modules"][0]["directImports"].append("Bang.Core.Invented"),
    )
    mutate(
        "wrong-engine-default", lambda fact: fact["engines"].update(default="oracle")
    )
    mutate(
        "wrong-engine-alias",
        lambda fact: fact["engines"]["aliases"].update({"--compiled": "env"}),
    )
    proposed_index = next(
        index for index, adr in enumerate(base["adrs"]) if adr["status"] == "Proposed"
    )
    mutate(
        "stale-adr-proposed-status",
        lambda fact: fact["adrs"][proposed_index].update(status="Accepted"),
    )
    superseded_index = next(
        index for index, adr in enumerate(base["adrs"]) if adr["status"] == "Superseded"
    )
    mutate(
        "stale-adr-superseded-status",
        lambda fact: fact["adrs"][superseded_index].update(status="Accepted"),
    )
    accepted_index = next(
        index
        for index, adr in enumerate(base["adrs"])
        if adr["status"] == "Accepted" and not adr["lifecycle"]
    )
    mutate(
        "accepted-is-implemented-trap",
        lambda fact: fact["adrs"][accepted_index].update(lifecycle=["implemented"]),
    )
    mutate(
        "broken-inverse-supersession",
        lambda fact: fact["adrs"][superseded_index]["derived"].update(supersededBy=[]),
    )
    mutate("missing-evidence-source", lambda fact: fact["evidence"][0].pop("sources"))
    mutate(
        "false-evidence-source",
        lambda fact: fact["evidence"][0].update(sources=["docs/not-real.md"]),
    )
    mutate(
        "escaping-evidence-source",
        lambda fact: fact["evidence"][0].update(sources=["../outside.md"]),
    )
    mutate(
        "missing-evidence-command", lambda fact: fact["evidence"][0].update(commands=[])
    )
    mutate(
        "duplicate-evidence-id",
        lambda fact: fact["evidence"][1].update(id=fact["evidence"][0]["id"]),
    )
    mutate(
        "duplicate-architecture-id",
        lambda fact: fact["arrows"][0].update(id=fact["nodes"][0]["id"]),
    )
    mutate(
        "collapsed-lr-simulation",
        lambda fact: fact["proofArrows"][0].update(
            endpointType="source-to-target-executions",
            direction="forward",
            method="annotated forward simulation",
            theoremRefs=["Bang.compile_forward_sim"],
        ),
    )
    proven_arrow_index = next(
        index
        for index, arrow in enumerate(base["arrows"])
        if next(item for item in base["evidence"] if item["id"] == arrow["evidenceId"])[
            "label"
        ]
        == "proven"
    )
    mutate(
        "proven-arrow-without-theorem",
        lambda fact: fact["arrows"][proven_arrow_index].update(theoremRefs=[]),
    )
    mutate(
        "removed-import",
        lambda fact: fact["modules"][
            next(i for i, m in enumerate(fact["modules"]) if m["directImports"])
        ]["directImports"].pop(),
    )

    passed = sum(expect_invalid(name, fact) for name, fact in cases)

    with tempfile.TemporaryDirectory() as directory:
        path = Path(directory) / "0110-frontmatter-boundary.md"
        path.write_text(
            "# 0110 — Boundary probe\n\n"
            "<!-- adr-frontmatter -->\n\n"
            "- **Status**: Proposed\n"
            "- **Summary**: first line\n"
            "  continued line\n"
            "## Decision\n\nBody text.\n",
            encoding="utf-8",
        )
        parsed = adr_facts.parse_adr(path)
        boundary = parsed["fields"]["summary"] == "first line continued line"
    print(
        "✓ ADR frontmatter stops before unindented body prose"
        if boundary
        else "✗ ADR frontmatter absorbed unindented body prose",
        file=sys.stdout if boundary else sys.stderr,
    )
    passed += boundary

    serialized = serialization_consumer_pole(base, parse_fact, render_consumer)
    print(
        "✓ serialized JSON is the architecture consumer boundary"
        if serialized
        else "✗ architecture consumer bypassed serialized JSON",
        file=sys.stdout if serialized else sys.stderr,
    )
    passed += serialized
    total = len(cases) + 2
    if total != SELF_TEST_POLES:
        print(
            f"docfacts-architecture: internal pole count mismatch: {total}",
            file=sys.stderr,
        )
        return 1
    print(f"docfacts-architecture self-test: {passed}/{total} poles passed.")
    return 0 if passed == total else 1


def write_output() -> int:
    fact = build_fact()
    validate_fact(fact)
    FACT_PATH.write_text(render_json(fact), encoding="utf-8")
    print(f"docfacts-architecture: generated {FACT_PATH.relative_to(ROOT)}")
    return 0


def check_output() -> int:
    expected = build_fact()
    validate_fact(expected)
    expected_json = render_json(expected)
    if (
        not FACT_PATH.is_file()
        or FACT_PATH.read_text(encoding="utf-8") != expected_json
    ):
        print(
            f"docfacts-architecture: stale or missing {FACT_PATH.relative_to(ROOT)}",
            file=sys.stderr,
        )
        return 1
    parse_fact(FACT_PATH.read_text(encoding="utf-8"))
    print(
        f"docfacts-architecture: OK — {len(expected['modules'])} modules, {len(expected['adrs'])} ADRs, {len(expected['arrows'])} pipeline arrows."
    )
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    try:
        if args.self_test:
            return self_test()
        if args.check:
            return check_output()
        return write_output()
    except (
        OSError,
        json.JSONDecodeError,
        ValidationError,
        ArchitectureFactsError,
        ImportFactsError,
        SymbolFactsError,
        AssertionError,
    ) as error:
        print(f"docfacts-architecture: FAIL — {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
