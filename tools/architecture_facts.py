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
    matches = list(re.finditer(pattern, text, re.MULTILINE | re.DOTALL))
    if len(matches) != 1:
        raise ArchitectureFactsError(
            f"cannot derive one {description} from {source}: found {len(matches)}"
        )
    return matches[0]


def derive_engine_details(main_path: Path) -> dict:
    # Do not run Lean comment stripping over CLI string literals such as
    # "--engine=oracle": the lightweight lexer deliberately is not string-aware.
    text = read_source(main_path)
    engine_block = require_source(
        text,
        r"inductive Engine where(?P<body>.*?)(?=\n(?:deriving|/--|def)\b)",
        main_path,
        "Engine declaration",
    )
    variants = tuple(
        re.findall(
            r"^\s*\|\s*([A-Za-z_]\w*)\s*$", engine_block.group("body"), re.MULTILINE
        )
    )
    if variants != ("oracle", "compiled", "env"):
        raise ArchitectureFactsError(
            f"unexpected Engine variants in {main_path}: {variants}"
        )

    parser_block = require_source(
        text,
        r"def parseEngine \(flags : List String\) : Engine :=\n(?P<body>.*?)(?=\n\n/-- Parse `--fuel)",
        main_path,
        "parseEngine body",
    ).group("body")
    branches = []
    for precedence, match in enumerate(
        re.finditer(
            r"(?:if|else if)\s+(?P<condition>.*?)\s+then\s+\.(?P<engine>\w+)",
            parser_block,
        ),
        1,
    ):
        flags = re.findall(r'flags\.contains\s+"([^"]+)"', match.group("condition"))
        engine = match.group("engine")
        if not flags or engine not in variants:
            raise ArchitectureFactsError(f"ambiguous parseEngine branch in {main_path}")
        branches.append({"engine": engine, "flags": flags, "precedence": precedence})
    default = require_source(
        parser_block,
        r"else\s+\.([A-Za-z_]\w*)\s*$",
        main_path,
        "parseEngine default",
    ).group(1)
    if default not in variants or [branch["engine"] for branch in branches] != [
        "oracle",
        "compiled",
    ]:
        raise ArchitectureFactsError(f"unexpected selector precedence in {main_path}")

    aliases = {
        flag: branch["engine"]
        for branch in branches
        for flag in branch["flags"]
        if not flag.startswith("--engine=")
    }
    if aliases != {"--compiled": "compiled"}:
        raise ArchitectureFactsError(
            f"unexpected engine aliases in {main_path}: {aliases}"
        )

    run_block = require_source(
        text,
        r"def runComp \(engine : Engine\).*?:= do\n(?P<body>.*?)(?=\n\n(?:def|/--)\b)",
        main_path,
        "runComp dispatch",
    ).group("body")
    require_source(
        run_block,
        r"\| \.compiled\s*=>\s*runCompiled fuel c",
        main_path,
        "compiled dispatch",
    )
    require_source(
        run_block, r"\| \.env\s*=>\s*runEnv fuel c", main_path, "env dispatch"
    )
    require_source(
        run_block,
        r"\| \.oracle\s*=>.*?Bang\.Source\.eval fuel c",
        main_path,
        "oracle dispatch",
    )

    default_fuel = int(
        require_source(
            text, r"def defaultFuel : Nat :=\s*(\d+)", main_path, "default fuel"
        ).group(1)
    )
    compiled_fuel = int(
        require_source(
            text, r"def compiledFuel : Nat :=\s*(\d+)", main_path, "compiled fuel"
        ).group(1)
    )
    scale = int(
        require_source(
            text,
            r"Bang\.CalcVM\.exec \((\d+) \* srcFuel\)",
            main_path,
            "compiled runtime fuel scale",
        ).group(1)
    )
    if compiled_fuel != scale * default_fuel:
        raise ArchitectureFactsError(
            f"compiledFuel {compiled_fuel} != runtime scale {scale} × defaultFuel {default_fuel}"
        )

    return {
        "variants": list(variants),
        "default": default,
        "aliases": aliases,
        "selectorPrecedence": branches,
        "runCompTargets": {
            "oracle": "Bang.Source.eval",
            "compiled": "runCompiled",
            "env": "runEnv",
        },
        "fuel": {
            "default": default_fuel,
            "compiledDefault": compiled_fuel,
            "compiledScale": scale,
        },
        "decisionRefs": ["0094"],
    }


def derive_engine_facts(main_path: Path) -> tuple[tuple[str, ...], str, str]:
    """Compatibility projection used by the existing architecture assertion generator."""
    details = derive_engine_details(main_path)
    return tuple(details["variants"]), details["default"], "--compiled"


def derive_decision_details(root: Path) -> dict:
    adr0016 = root / "docs/decisions/0016-two-hop-architecture-calcvm-and-wasmfx.md"
    adr0035 = (
        root / "docs/decisions/0035-lr-for-equivalence-simulation-for-compilation.md"
    )
    adr0059 = root / "docs/decisions/0059-wasm3-grade-directed-pluggable-backend.md"
    base = read_source(adr0016)
    proof = read_source(adr0035)
    target = read_source(adr0059)

    require_source(
        base, r"The architecture is two-hop:", adr0016, "two-hop architecture"
    )
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
    return {
        "target": {
            "name": target_name,
            "backend": "grade-directed pluggable backend",
            "wasmfxRole": "future general-case fast path",
            "sources": [
                "docs/decisions/0016-two-hop-architecture-calcvm-and-wasmfx.md",
                "docs/decisions/0059-wasm3-grade-directed-pluggable-backend.md",
            ],
        },
        "proofMethods": {
            "sourceEquivalence": "binary biorthogonal LR",
            "compilation": "annotated forward simulation",
        },
    }


def derive_decision_facts(root: Path) -> tuple[str, str, str]:
    """Compatibility projection used by the existing architecture assertion generator."""
    details = derive_decision_details(root)
    return (
        details["target"]["name"],
        details["proofMethods"]["sourceEquivalence"],
        details["proofMethods"]["compilation"],
    )


def proof_arrow_semantics() -> list[dict]:
    """The shared semantic identity of the two proof arrows (ADR-0035)."""
    return [
        {
            "id": "contextual-equivalence",
            "from": "source-program-left",
            "to": "source-program-right",
            "endpointType": "source-programs",
            "direction": "bidirectional-contextual",
            "method": "binary biorthogonal LR",
            "theoremRefs": ["Bang.lr_fundamental", "Bang.lr_sound"],
        },
        {
            "id": "source-target-forward-simulation",
            "from": "source-execution",
            "to": "target-execution",
            "endpointType": "source-to-target-executions",
            "direction": "forward",
            "method": "annotated forward simulation",
            "theoremRefs": ["Bang.compile_forward_sim"],
        },
    ]
