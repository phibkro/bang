#!/usr/bin/env python3
# tool: role=lib couples=Bang/**/*.lean,gen-import-graph.py,arch-check.py runs-in=fitness
"""Shared, fail-loud facts for BANG's internal Lean module graph."""

from __future__ import annotations

import argparse
import os
import re
from dataclasses import dataclass
from pathlib import Path

from leanlex import strip_comments

IMPORT_RE = re.compile(
    r"^[ \t]*(?:public[ \t]+)?import[ \t]+(Bang(?:\.[A-Za-z_][A-Za-z0-9_']*)+)",
    re.MULTILINE,
)
TIER_DIRS = frozenset({"Core", "Frontend", "Backend", "Meta", "Witness", "Reify"})
APEX_MODULES = frozenset(
    {
        "Bang.Spec",
        "Bang.Audit",
        "Bang.Distribution",
        "Bang.Distribution.LatticeStore",
        "Bang.Examples",
    }
)


class ImportFactsError(ValueError):
    """The source tree does not have one unambiguous internal module graph."""


@dataclass(frozen=True)
class ModuleFact:
    name: str
    path: Path
    loc: int
    tier: str
    imports: tuple[str, ...]

    @property
    def short_name(self) -> str:
        return self.name.removeprefix("Bang.")


@dataclass(frozen=True)
class ImportFacts:
    root: Path
    modules: dict[str, ModuleFact]
    edges: tuple[tuple[str, str], ...]


def module_name_from_path(path: Path, bang_dir: Path) -> str:
    try:
        rel = path.relative_to(bang_dir).with_suffix("")
    except ValueError as exc:
        raise ImportFactsError(f"module is outside {bang_dir}: {path}") from exc
    return "Bang." + ".".join(rel.parts)


def tier_from_module_name(name: str) -> str:
    if name in APEX_MODULES:
        return "Apex"
    parts = name.split(".")
    if len(parts) >= 3 and parts[0] == "Bang" and parts[1] in TIER_DIRS:
        return parts[1]
    raise ImportFactsError(
        f"unclassified module {name}: place it under Bang/<Tier>/ or explicitly classify a root Apex module"
    )


def parse_imports(text: str) -> tuple[str, ...]:
    code = strip_comments(text)
    return tuple(IMPORT_RE.findall(code))


def scan_bang(root: str | Path = ".") -> ImportFacts:
    root_path = Path(root).resolve()
    bang_dir = root_path / "Bang"
    if not bang_dir.is_dir():
        raise ImportFactsError(f"missing BANG source directory: {bang_dir}")

    modules: dict[str, ModuleFact] = {}
    for path in sorted(bang_dir.rglob("*.lean")):
        name = module_name_from_path(path, bang_dir)
        text = path.read_text(encoding="utf-8")
        modules[name] = ModuleFact(
            name=name,
            path=path.relative_to(root_path),
            loc=text.count("\n") + 1,
            tier=tier_from_module_name(name),
            imports=parse_imports(text),
        )

    missing = sorted(
        (fact.name, imported)
        for fact in modules.values()
        for imported in fact.imports
        if imported not in modules
    )
    if missing:
        details = "\n".join(
            f"  {source} imports missing {target}" for source, target in missing
        )
        raise ImportFactsError(f"internal imports have no source module:\n{details}")

    edges = tuple(
        sorted(
            (fact.name, imported)
            for fact in modules.values()
            for imported in fact.imports
        )
    )
    return ImportFacts(root=root_path, modules=modules, edges=edges)


def self_test(root: str | Path = ".") -> None:
    facts = scan_bang(root)

    distribution = facts.modules["Bang.Distribution"]
    assert "Bang.Spec" in distribution.imports, "public import Bang.Spec was not parsed"

    prop_test = facts.modules["Bang.Frontend.Surface.PropTest"]
    assert "Bang.Frontend.Surface" in prop_test.imports, "classic import was not parsed"

    comment_probe = """-- import Bang.Fake.Line
/- public import Bang.Fake.Block -/
public import Bang.Spec -- import Bang.Fake.Trailing
"""
    assert parse_imports(comment_probe) == ("Bang.Spec",), (
        "comment-shaped imports became edges"
    )

    assert facts.modules["Bang.Backend.Wasm"].tier == "Backend"
    assert facts.modules["Bang.Meta.BinaryLR"].tier == "Meta"
    assert facts.modules["Bang.Spec"].tier == "Apex"
    assert facts.modules["Bang.Distribution.LatticeStore"].tier == "Apex"
    assert len(facts.edges) > len(facts.modules), "implausibly sparse module graph"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--root",
        default=os.environ.get("REFS_ROOT", "."),
        help="repository root (default: REFS_ROOT or current directory)",
    )
    parser.add_argument(
        "--self-test", action="store_true", help="run parser and classification poles"
    )
    args = parser.parse_args()

    try:
        facts = scan_bang(args.root)
        if args.self_test:
            self_test(args.root)
            print(
                f"import-facts: PASS — {len(facts.modules)} modules, {len(facts.edges)} internal edges; "
                "classic/public/comment poles hold."
            )
        else:
            print(
                f"import-facts: {len(facts.modules)} modules, {len(facts.edges)} internal edges"
            )
        return 0
    except (ImportFactsError, AssertionError) as exc:
        print(f"import-facts: FAIL — {exc}")
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
