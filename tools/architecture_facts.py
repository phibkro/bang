#!/usr/bin/env python3
# tool: role=lib couples=Main.lean,docs/decisions/0016-*.md,docs/decisions/0035-*.md,docs/decisions/0059-*.md runs-in=fitness
"""Source-derived architecture facts shared by documentation projections."""

from __future__ import annotations

import re
from pathlib import Path


class ArchitectureFactsError(ValueError):
    """An authority no longer contains one unambiguous architecture fact."""


def read_source(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8")
    except FileNotFoundError as exc:
        raise ArchitectureFactsError(f"missing authority: {path}") from exc


def require_source(
    text: str,
    pattern: str,
    source: Path,
    description: str,
) -> re.Match[str]:
    match = re.search(pattern, text, re.MULTILINE | re.DOTALL)
    if not match:
        raise ArchitectureFactsError(f"cannot derive {description} from {source}")
    return match


def derive_engine_facts(main_path: Path) -> tuple[tuple[str, ...], str, str]:
    text = read_source(main_path)
    block = require_source(
        text,
        r"inductive Engine where(?P<body>.*?)\n\n/-- Parse the engine selector.*?\ndef parseEngine .*?:=\n(?P<parser>.*?)(?=\n\n/-- Parse `--fuel)",
        main_path,
        "engine declarations and parseEngine",
    )
    engines = tuple(re.findall(r"^\s*\|\s*(\w+)\s*$", block.group("body"), re.MULTILINE))
    parser = block.group("parser")
    branches = tuple(re.findall(r"(?:then|else)\s+\.([A-Za-z_]\w*)", parser))
    if not engines or not branches or any(branch not in engines for branch in branches):
        raise ArchitectureFactsError(f"ambiguous engine branches in {main_path}")
    alias = require_source(
        parser,
        r'flags\.contains "(--compiled)"',
        main_path,
        "compiled alias",
    ).group(1)
    return engines, branches[-1], alias


def derive_decision_facts(root: Path) -> tuple[str, str, str]:
    adr0016 = root / "docs/decisions/0016-two-hop-architecture-calcvm-and-wasmfx.md"
    adr0035 = root / "docs/decisions/0035-lr-for-equivalence-simulation-for-compilation.md"
    adr0059 = root / "docs/decisions/0059-wasm3-grade-directed-pluggable-backend.md"
    base = read_source(adr0016)
    proof = read_source(adr0035)
    target = read_source(adr0059)

    require_source(base, r"two-hop", adr0016, "two-hop architecture")
    target_name = require_source(
        target,
        r"compile to \*\*(Wasm 3\.0)\*\* with a \*\*grade-directed, pluggable backend\*\*",
        adr0059,
        "primary target",
    ).group(1)
    require_source(
        target,
        r"WasmFX is a\s+post-standardization fast-path for the `general` case only",
        adr0059,
        "WasmFX future slot",
    )
    require_source(
        proof,
        r"Biorthogonal LR proves .*contextual-equivalence.*annotated simulation.*`compile_forward_sim`",
        adr0035,
        "proof-method split",
    )
    return target_name, "binary biorthogonal LR", "annotated forward simulation"
