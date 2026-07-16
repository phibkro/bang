#!/usr/bin/env python3
# tool: role=gen couples=docfacts/architecture.json,docfacts/schema/architecture.schema.json,docs/architecture/core-overview.md,docfacts_architecture.py,genblock.py runs-in=fitness
"""Generate BANG's C4 component dependency view from serialized architecture facts."""

import json
import os
import re
import sys
from collections import Counter
from pathlib import Path

from docfacts_architecture import parse_fact
from genblock import (
    marker_bounds,
    semantic_mermaid_id,
    splice as _splice,
    validate_mermaid,
)
from jsonschema.exceptions import ValidationError

ROOT = Path(os.environ.get("REFS_ROOT", ".")).resolve()
DOC = ROOT / "docs/architecture/core-overview.md"
FACT = ROOT / "docfacts/architecture.json"
GEN_BEGIN = (
    "<!-- BEGIN GENERATED import-graph (just import-graph) — do not hand-edit -->"
)
GEN_END = "<!-- END GENERATED import-graph -->"

COMPONENT_ORDER = ["Frontend", "Core", "Backend", "Meta", "Witness", "Reify", "Apex"]
COMPONENT_DESCRIPTION = {
    "Core": "IR · typing · semantics · soundness",
    "Frontend": "text → typed core",
    "Backend": "calculated + abstract target machines · separate WasmGC emitter",
    "Meta": "contextual-equivalence metatheory",
    "Witness": "executable evidence and counterexamples",
    "Reify": "calculated-machine proof laboratory",
    "Apex": "public theorem façade · audit · distribution",
}


def node_id(name: str) -> str:
    return semantic_mermaid_id(name, prefix="component")


def import_edges(modules: list[dict]) -> list[tuple[str, str]]:
    return sorted(
        (module["name"], imported)
        for module in modules
        for imported in module["directImports"]
    )


def component_edges(modules: list[dict]) -> Counter[tuple[str, str]]:
    tier_by_module = {module["name"]: module["tier"] for module in modules}
    edges: Counter[tuple[str, str]] = Counter()
    for importer, imported in import_edges(modules):
        source = tier_by_module[importer]
        target = tier_by_module[imported]
        if source != target:
            edges[source, target] += 1
    return edges


def render(fact: dict) -> str:
    tiers = {item["name"]: item for item in fact["tiers"]}
    edges = component_edges(fact["modules"])
    dependency_count = sum(edges.values())
    all_edge_count = len(import_edges(fact["modules"]))

    lines = [
        GEN_BEGIN,
        "BANG uses the [C4 abstraction hierarchy](https://c4model.com/abstractions) "
        "to choose a useful zoom level for this page:",
        "",
        "| C4 abstraction | BANG mapping | This view |",
        "|---|---|---|",
        "| Software system | BANG implementation and toolchain | Shown as the outer boundary |",
        "| Container | Lean compiler/reference toolchain | Shown as the application boundary |",
        f"| Component | {len(tiers)} repository tiers (`Frontend`, `Core`, …) | Dependency nodes below |",
        f"| Code | {len(fact['modules'])} Lean modules and {all_edge_count} direct imports | Serialized in `docfacts/architecture.json`; intentionally not drawn |",
        "",
        "A C4 [component](https://c4model.com/abstractions/component) is related functionality "
        "behind a defined interface and is not separately deployable. That matches these tiers "
        "better than C4's application/data-store [container](https://c4model.com/abstractions/container) term.",
        "",
        "```mermaid",
        "flowchart LR",
        '  subgraph system_BANG["Software system: BANG implementation"]',
        '    subgraph container_Lean_toolchain["Container: Lean compiler/reference toolchain"]',
    ]

    for component in COMPONENT_ORDER:
        tier = tiers[component]
        lines.append(
            f'      {node_id(component)}["{component}<br/>{tier["moduleCount"]} modules · {tier["loc"]} LOC"]'
        )
    lines += ["    end", "  end"]

    for (source, target), count in sorted(
        edges.items(),
        key=lambda item: (
            COMPONENT_ORDER.index(item[0][0]),
            COMPONENT_ORDER.index(item[0][1]),
        ),
    ):
        lines.append(
            f"  {node_id(source)} -->|{count} code import{'s' if count != 1 else ''}| {node_id(target)}"
        )
    lines += [
        "```",
        "",
        "**Reading the diagram:** arrows are dependencies between C4 components; edge labels "
        f"aggregate the {dependency_count} code-level imports that cross a component boundary. "
        "Internal module-to-module imports are deliberately omitted from the visual.",
        "",
        "| Component (repository tier) | Responsibility | Modules | LOC | Depends on |",
        "|---|---|---:|---:|---|",
    ]

    for component in COMPONENT_ORDER:
        tier = tiers[component]
        dependencies = [
            f"`{target}` ({edges[component, target]})"
            for target in COMPONENT_ORDER
            if edges[component, target]
        ]
        lines.append(
            f"| `{component}` | {COMPONENT_DESCRIPTION[component]} | "
            f"{tier['moduleCount']} | {tier['loc']} | "
            f"{', '.join(dependencies) if dependencies else '—'} |"
        )
    lines.append(GEN_END)
    return "\n".join(lines)


def splice(md: str, block: str) -> str:
    return _splice(md, GEN_BEGIN, GEN_END, block)


def load_fact() -> dict:
    if not FACT.is_file():
        raise OSError(f"{FACT} missing")
    return parse_fact(FACT.read_text(encoding="utf-8"))


def main() -> int:
    try:
        __import__("subprocess").run(
            ["bash", str(Path(__file__).with_name("tool-log.sh")), Path(__file__).name],
            check=False,
        )
    except Exception:
        pass

    args = sys.argv[1:]
    try:
        fact = load_fact()
        block = render(fact)
    except (
        OSError,
        json.JSONDecodeError,
        ValidationError,
        KeyError,
        ValueError,
    ) as exc:
        print(f"import-graph: FAIL — {exc}", file=sys.stderr)
        return 1

    if not DOC.exists():
        print(f"import-graph: {DOC} missing", file=sys.stderr)
        return 1
    md = DOC.read_text(encoding="utf-8")
    try:
        marker_bounds(md, GEN_BEGIN, GEN_END)
    except ValueError as exc:
        print(f"import-graph: FAIL — {exc}", file=sys.stderr)
        return 1

    if "--validate" in args:
        committed = re.search(
            re.escape(GEN_BEGIN) + r"(.*?)" + re.escape(GEN_END), md, re.DOTALL
        )
        status, msg = validate_mermaid(committed.group(1) if committed else "")
        print(f"── import-graph (mermaid compile) ──\n{status.upper()}: {msg}")
        return 1 if status == "fail" else 0

    new = splice(md, block)
    edges = component_edges(fact["modules"])
    if "--check" in args:
        if new != md:
            print(
                "── import-graph ──\nFAIL: core-overview.md component graph is stale — run `just import-graph`."
            )
            return 1
        print(
            f"── import-graph ──\nPASS: {len(fact['tiers'])} components / "
            f"{len(edges)} component dependencies from {len(fact['modules'])} modules."
        )
        return 0

    status, msg = validate_mermaid(block)
    if status == "fail":
        print(
            f"── import-graph ──\nFAIL: generated mermaid does not compile (NOT written):\n{msg}"
        )
        return 1
    DOC.write_text(new, encoding="utf-8")
    suffix = (
        "mermaid compiles ✓" if status == "pass" else f"compile-check {status}: {msg}"
    )
    print(
        f"import-graph: regenerated C4 component graph ({len(fact['tiers'])} components, "
        f"{len(edges)} dependency pairs; {suffix})."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
