#!/usr/bin/env python3
# tool: role=gen couples=docfacts/architecture.json,docfacts/proof.json,docfacts/schema/architecture.schema.json,docfacts/schema/proof.schema.json,docs/architecture/core-overview.md,docfacts_architecture.py,docfacts_proof.py,genblock.py runs-in=fitness
"""Render/check architecture and proof projections from committed documentation facts."""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
from collections import Counter
from pathlib import Path

from docfacts_architecture import parse_fact as parse_architecture_fact
from docfacts_proof import parse_fact as parse_proof_fact, validate_cross_fact
from genblock import splice, validate_mermaid
from jsonschema.exceptions import ValidationError

PIPELINE_BEGIN = "<!-- BEGIN GENERATED architecture-pipeline (just architecture-assertions) — do not hand-edit -->"
PIPELINE_END = "<!-- END GENERATED architecture-pipeline -->"
ASSERTIONS_BEGIN = "<!-- BEGIN GENERATED architecture-assertions (just architecture-assertions) — do not hand-edit -->"
ASSERTIONS_END = "<!-- END GENERATED architecture-assertions -->"
PROOF_ARROWS_BEGIN = "<!-- BEGIN GENERATED proof-arrows (just architecture-assertions) — do not hand-edit -->"
PROOF_ARROWS_END = "<!-- END GENERATED proof-arrows -->"
AUDITED_AXIOMS_BEGIN = "<!-- BEGIN GENERATED audited-axioms (just architecture-assertions) — do not hand-edit -->"
AUDITED_AXIOMS_END = "<!-- END GENERATED audited-axioms -->"

REGIONS = (
    (PIPELINE_BEGIN, PIPELINE_END),
    (ASSERTIONS_BEGIN, ASSERTIONS_END),
    (PROOF_ARROWS_BEGIN, PROOF_ARROWS_END),
    (AUDITED_AXIOMS_BEGIN, AUDITED_AXIOMS_END),
)


class ArchitectureRendererError(ValueError):
    """Committed facts or generated regions cannot be rendered safely."""


def md(value: object) -> str:
    return str(value).replace("|", r"\|").replace("\n", " ")


def code(value: object) -> str:
    text = md(value)
    longest = max((len(run) for run in re.findall(r"`+", text)), default=0)
    fence = "`" * (longest + 1)
    if text.startswith(("`", " ")) or text.endswith(("`", " ")):
        text = f" {text} "
    return f"{fence}{text}{fence}"


def mermaid_id(value: str) -> str:
    return "n_" + value.encode("utf-8").hex()


def mermaid_label(value: object) -> str:
    return str(value).replace("\\", r"\\").replace('"', r"\"").replace("\n", " ")


def evidence_by_id(fact: dict) -> dict[str, dict]:
    return {item["id"]: item for item in fact["evidence"]}


def node_by_id(architecture: dict) -> dict[str, dict]:
    return {item["id"]: item for item in architecture["nodes"]}


def theorem_enrollments(proof: dict, theorem_refs: list[str]) -> list[dict]:
    by_report = {item["reportName"]: item for item in proof["enrollments"]}
    result = []
    for theorem_ref in theorem_refs:
        if theorem_ref not in by_report:
            raise ArchitectureRendererError(
                f"proof theorem is not Audit-enrolled: {theorem_ref}"
            )
        result.append(by_report[theorem_ref])
    return result


def source_list(paths: list[str]) -> str:
    return ", ".join(code(path) for path in paths)


def evidence_text(
    record: dict, include_sources: bool = True, status: str | None = None
) -> str:
    parts = [status or md(record["label"])]
    if include_sources:
        parts.append(source_list(record["sources"]))
    if record["commands"]:
        parts.append(
            "validate: " + ", ".join(code(item) for item in record["commands"])
        )
    return "; ".join(parts)


def support_status(proof: dict, arrow: dict, evidence: dict) -> str:
    enrollments = theorem_enrollments(proof, arrow["theoremRefs"])
    flagged = [item for item in enrollments if item["classification"] == "flagged"]
    if flagged:
        names = ", ".join(code(item["reportName"]) for item in flagged)
        return f"{md(evidence['label'])}; flagged support: {names}"
    return md(evidence["label"])


def render_pipeline(architecture: dict) -> str:
    nodes = node_by_id(architecture)
    evidence = evidence_by_id(architecture)
    referenced = sorted(
        {
            endpoint
            for arrow in architecture["arrows"]
            for endpoint in (arrow["from"], arrow["to"])
        }
    )
    lines = [
        PIPELINE_BEGIN,
        "```mermaid",
        "flowchart LR",
    ]
    for node_id in referenced:
        node = nodes[node_id]
        lines.append(f'  {mermaid_id(node_id)}["{mermaid_label(node["name"])}"]')
    for arrow in architecture["arrows"]:
        record = evidence[arrow["evidenceId"]]
        label = mermaid_label(f"{record['label']} · {arrow['method']}")
        lines.append(
            f"  {mermaid_id(arrow['from'])} -->|{label}| {mermaid_id(arrow['to'])}"
        )
    lines += [
        "```",
        "",
        "**Reading the diagram:** each edge label is the serialized evidence label followed by the serialized method; labels do not imply a stronger status.",
        "",
        "| Representation | Kind | Sources | Outgoing boundaries |",
        "|---|---|---|---|",
    ]
    for node_id in referenced:
        node = nodes[node_id]
        outgoing = []
        for arrow in architecture["arrows"]:
            if arrow["from"] != node_id:
                continue
            record = evidence[arrow["evidenceId"]]
            outgoing.append(
                f"{md(arrow['method'])} → {code(nodes[arrow['to']]['name'])} ({md(record['label'])})"
            )
        lines.append(
            f"| {code(node['name'])} | {md(node['kind'])} | {source_list(node['sources'])} | "
            f"{'; '.join(outgoing) if outgoing else '—'} |"
        )
    lines.append(PIPELINE_END)
    return "\n".join(lines)


def adr_link(adr: dict) -> str:
    return f"[ADR-{adr['id']}](../decisions/{Path(adr['path']).name})"


def render_assertions(architecture: dict, proof: dict) -> str:
    architecture_evidence = evidence_by_id(architecture)
    adrs = {item["id"]: item for item in architecture["adrs"]}
    proof_arrows = {item["id"]: item for item in architecture["proofArrows"]}
    nodes = node_by_id(architecture)
    contextual = proof_arrows["contextual-equivalence"]
    simulation = proof_arrows["source-target-forward-simulation"]
    tier_counts = " · ".join(
        f"{item['name']} {item['moduleCount']}" for item in architecture["tiers"]
    )
    edge_count = sum(len(module["directImports"]) for module in architecture["modules"])
    aliases = ", ".join(
        f"{code(flag)} aliases {code(engine)}"
        for flag, engine in architecture["engines"]["aliases"].items()
    )
    engine_sources = sorted(
        set(nodes["env-engine"]["sources"])
        | {adrs[item]["path"] for item in architecture["engines"]["decisionRefs"]}
    )

    rows = [
        (
            "Compiler target",
            f"**{md(architecture['target']['name'])}**, {md(architecture['target']['backend'])}; WasmFX: {md(architecture['target']['wasmfxRole'])}",
            source_list(architecture["target"]["sources"]),
        ),
        (
            "Source equivalence",
            f"{md(contextual['method'])}: {', '.join(code(item) for item in contextual['theoremRefs'])}",
            evidence_text(
                architecture_evidence[contextual["evidenceId"]],
                status=support_status(
                    proof,
                    contextual,
                    architecture_evidence[contextual["evidenceId"]],
                ),
            ),
        ),
        (
            "Compilation correctness",
            f"{md(simulation['method'])}: {', '.join(code(item) for item in simulation['theoremRefs'])}",
            evidence_text(
                architecture_evidence[simulation["evidenceId"]],
                status=support_status(
                    proof,
                    simulation,
                    architecture_evidence[simulation["evidenceId"]],
                ),
            ),
        ),
        (
            "CLI engines",
            f"{', '.join(code(item) for item in architecture['engines']['variants'])}; default **{code(architecture['engines']['default'])}**; {aliases}",
            source_list(engine_sources),
        ),
        (
            "Module graph",
            f"{len(architecture['modules'])} modules · {edge_count} internal edges · {tier_counts}",
            f"{len(architecture['modules'])} serialized module records in {code('docfacts/architecture.json')}",
        ),
        (
            "Architecture lineage",
            "ADR-0016 two-hop shape; target refined by ADR-0059",
            ", ".join(
                f"{adr_link(adrs[item])} ({md(adrs[item]['status'])}; {', '.join(adrs[item]['lifecycle'])})"
                for item in ("0016", "0059")
            ),
        ),
    ]
    lines = [
        ASSERTIONS_BEGIN,
        "### Architecture assertions",
        "",
        "_Generated from validated committed architecture and proof facts. The JSON is the consumer seam; source checks remain in the fact producers._",
        "",
        "| Fact | Current value | Source/evidence |",
        "|---|---|---|",
    ]
    lines.extend(f"| {name} | {value} | {source} |" for name, value, source in rows)
    lines.append(ASSERTIONS_END)
    return "\n".join(lines)


def render_proof_arrows(architecture: dict, proof: dict) -> str:
    nodes = node_by_id(architecture)
    evidence = evidence_by_id(proof)
    referenced = sorted(
        {
            endpoint
            for arrow in proof["proofArrows"]
            for endpoint in (arrow["from"], arrow["to"])
        }
    )
    lines = [
        PROOF_ARROWS_BEGIN,
        "```mermaid",
        "flowchart LR",
    ]
    for node_id in referenced:
        lines.append(
            f'  {mermaid_id(node_id)}["{mermaid_label(nodes[node_id]["name"])}"]'
        )
    for arrow in proof["proofArrows"]:
        status = support_status(proof, arrow, evidence[arrow["evidenceId"]])
        label = mermaid_label(f"{arrow['method']} · {status}")
        connector = (
            "<-->" if arrow["direction"] == "bidirectional-contextual" else "-->"
        )
        lines.append(
            f"  {mermaid_id(arrow['from'])} {connector}|{label}| {mermaid_id(arrow['to'])}"
        )
    lines += [
        "```",
        "",
        "| Question / endpoint type | Direction | Method and theorem refs | Evidence status |",
        "|---|---|---|---|",
    ]
    for arrow in proof["proofArrows"]:
        record = evidence[arrow["evidenceId"]]
        theorem_refs = ", ".join(code(item) for item in arrow["theoremRefs"])
        lines.append(
            f"| {md(arrow['endpointType'])}: {code(nodes[arrow['from']]['name'])} → {code(nodes[arrow['to']]['name'])} | "
            f"{md(arrow['direction'])} | {md(arrow['method'])}; {theorem_refs} | "
            f"{support_status(proof, arrow, record)}; validate: {', '.join(code(item) for item in record['commands'])} |"
        )
    lines.append(PROOF_ARROWS_END)
    return "\n".join(lines)


def render_audited_axioms(proof: dict) -> str:
    counts = Counter(item["classification"] for item in proof["enrollments"])
    no_axioms = sum(not item["axioms"] for item in proof["enrollments"])
    audit_evidence = evidence_by_id(proof)["audit-generated"]
    validator = ", ".join(code(item) for item in audit_evidence["commands"])
    lines = [
        AUDITED_AXIOMS_BEGIN,
        f"**Census:** {len(proof['enrollments'])} enrolled theorems · {counts['trusted']} trusted · {counts['flagged']} flagged · {no_axioms} with no axioms.",
        "",
        f"_Live validator: {validator}._",
        "",
        "| Theorem | Source | Axiom set | Status/evidence |",
        "|---|---|---|---|",
    ]
    for item in proof["enrollments"]:
        source = item["definitionSource"]
        source_text = (
            "—" if source is None else code(f"{source['path']}:{source['line']}")
        )
        axioms = (
            "—"
            if not item["axioms"]
            else ", ".join(code(axiom) for axiom in item["axioms"])
        )
        status = md(item["classification"])
        if item.get("evidenceLabel"):
            status += f" · {md(item['evidenceLabel'])}"
        lines.append(
            f"| {code(item['reportName'])} | {source_text} | {axioms} | {status} |"
        )
    lines.append(AUDITED_AXIOMS_END)
    return "\n".join(lines)


def render_regions(architecture: dict, proof: dict) -> dict[tuple[str, str], str]:
    validate_cross_fact(architecture, proof)
    return {
        (PIPELINE_BEGIN, PIPELINE_END): render_pipeline(architecture),
        (ASSERTIONS_BEGIN, ASSERTIONS_END): render_assertions(architecture, proof),
        (PROOF_ARROWS_BEGIN, PROOF_ARROWS_END): render_proof_arrows(
            architecture, proof
        ),
        (AUDITED_AXIOMS_BEGIN, AUDITED_AXIOMS_END): render_audited_axioms(proof),
    }


def render_regions_from_serialized(
    architecture_serialized: str, proof_serialized: str
) -> dict[tuple[str, str], str]:
    architecture = parse_architecture_fact(architecture_serialized)
    proof = parse_proof_fact(proof_serialized)
    return render_regions(architecture, proof)


def load_regions(root: Path) -> dict[tuple[str, str], str]:
    return render_regions_from_serialized(
        (root / "docfacts/architecture.json").read_text(encoding="utf-8"),
        (root / "docfacts/proof.json").read_text(encoding="utf-8"),
    )


def apply_regions(document: str, regions: dict[tuple[str, str], str]) -> str:
    for begin, end in REGIONS:
        if document.count(begin) != 1 or document.count(end) != 1:
            raise ArchitectureRendererError(
                f"core overview must contain exactly one {begin} / {end} region"
            )
        document = splice(document, begin, end, regions[(begin, end)])
    return document


def self_test(root: Path) -> int:
    architecture_object = json.loads(
        (root / "docfacts/architecture.json").read_text(encoding="utf-8")
    )
    proof_object = json.loads(
        (root / "docfacts/proof.json").read_text(encoding="utf-8")
    )
    architecture_serialized = json.dumps(architecture_object)
    proof_serialized = json.dumps(proof_object)
    architecture_object["target"]["name"] = "Unserialized mutation"
    proof_object["enrollments"][0]["axioms"] = []
    rendered = "\n".join(
        render_regions_from_serialized(
            architecture_serialized, proof_serialized
        ).values()
    )
    if "Wasm 3.0" not in rendered or "Unserialized mutation" in rendered:
        raise ArchitectureRendererError(
            "overview renderer bypassed the serialized architecture boundary"
        )
    if "sorryAx" not in rendered:
        raise ArchitectureRendererError(
            "overview renderer bypassed the serialized proof boundary"
        )
    print(
        "architecture-assertions self-test: PASS — actual overview renderer is isolated by serialized JSON reload."
    )
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check", action="store_true", help="fail if any generated region is stale"
    )
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="exercise the serialized renderer boundary",
    )
    parser.add_argument(
        "--root",
        default=os.environ.get("REFS_ROOT", "."),
        help="repository root (default: REFS_ROOT or current directory)",
    )
    args = parser.parse_args()
    root = Path(args.root).resolve()
    doc = root / "docs/architecture/core-overview.md"

    try:
        subprocess.run(
            ["bash", str(Path(__file__).with_name("tool-log.sh")), Path(__file__).name],
            check=False,
        )
        if args.self_test:
            return self_test(root)
        regions = load_regions(root)
        current = doc.read_text(encoding="utf-8")
        updated = apply_regions(current, regions)
        for key in (
            (PIPELINE_BEGIN, PIPELINE_END),
            (PROOF_ARROWS_BEGIN, PROOF_ARROWS_END),
        ):
            status, message = validate_mermaid(regions[key])
            if status == "fail":
                raise ArchitectureRendererError(
                    f"generated Mermaid does not compile (not written): {message}"
                )
    except (
        OSError,
        json.JSONDecodeError,
        ValidationError,
        ArchitectureRendererError,
        KeyError,
        ValueError,
    ) as error:
        print(f"architecture-assertions: FAIL — {error}")
        return 1

    if args.check:
        if updated != current:
            print(
                "architecture-assertions: FAIL — one or more generated regions are stale; run `just architecture-assertions`."
            )
            return 1
        print(
            "architecture-assertions: PASS — 4 generated regions match validated committed architecture/proof facts."
        )
        return 0

    doc.write_text(updated, encoding="utf-8")
    print(
        "architecture-assertions: regenerated 4 regions in docs/architecture/core-overview.md."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
