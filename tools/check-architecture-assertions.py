#!/usr/bin/env python3
# tool: role=gen couples=Bang/**/*.lean,Main.lean,docs/decisions/0016-*.md,docs/decisions/0035-*.md,docs/decisions/0059-*.md,docs/architecture/core-overview.md,import_facts.py runs-in=fitness
"""Generate/check the current architecture snapshot from code and accepted ADRs."""

from __future__ import annotations

import argparse
import os
import re
import subprocess
from collections import Counter
from pathlib import Path

from genblock import splice
from import_facts import ImportFactsError, scan_bang

GEN_BEGIN = "<!-- BEGIN GENERATED architecture-assertions (just architecture-assertions) — do not hand-edit -->"
GEN_END = "<!-- END GENERATED architecture-assertions -->"


class AssertionSourceError(ValueError):
    """An authority no longer contains one unambiguous architecture fact."""


def read(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8")
    except FileNotFoundError as exc:
        raise AssertionSourceError(f"missing authority: {path}") from exc


def require(text: str, pattern: str, source: Path, description: str) -> re.Match[str]:
    match = re.search(pattern, text, re.MULTILINE | re.DOTALL)
    if not match:
        raise AssertionSourceError(f"cannot derive {description} from {source}")
    return match


def derive_engine_facts(main_path: Path) -> tuple[tuple[str, ...], str, str]:
    text = read(main_path)
    block = require(
        text,
        r"inductive Engine where(?P<body>.*?)\n\n/-- Parse the engine selector.*?\ndef parseEngine .*?:=\n(?P<parser>.*?)(?=\n\n/-- Parse `--fuel)",
        main_path,
        "engine declarations and parseEngine",
    )
    engines = tuple(re.findall(r"^\s*\|\s*(\w+)\s*$", block.group("body"), re.MULTILINE))
    parser = block.group("parser")
    branches = tuple(re.findall(r"(?:then|else)\s+\.([A-Za-z_]\w*)", parser))
    if not engines or not branches or any(branch not in engines for branch in branches):
        raise AssertionSourceError(f"ambiguous engine branches in {main_path}")
    alias = require(parser, r'flags\.contains "(--compiled)"', main_path, "compiled alias").group(1)
    return engines, branches[-1], alias


def derive_decision_facts(root: Path) -> tuple[str, str, str]:
    adr0016 = root / "docs/decisions/0016-two-hop-architecture-calcvm-and-wasmfx.md"
    adr0035 = root / "docs/decisions/0035-lr-for-equivalence-simulation-for-compilation.md"
    adr0059 = root / "docs/decisions/0059-wasm3-grade-directed-pluggable-backend.md"

    base = read(adr0016)
    proof = read(adr0035)
    target = read(adr0059)

    require(base, r"two-hop", adr0016, "two-hop architecture")
    target_name = require(
        target,
        r"compile to \*\*(Wasm 3\.0)\*\* with a \*\*grade-directed, pluggable backend\*\*",
        adr0059,
        "primary target",
    ).group(1)
    require(
        target,
        r"WasmFX is a\s+post-standardization fast-path for the `general` case only",
        adr0059,
        "WasmFX future slot",
    )
    require(
        proof,
        r"Biorthogonal LR proves .*contextual-equivalence.*annotated simulation.*`compile_forward_sim`",
        adr0035,
        "proof-method split",
    )
    return target_name, "binary biorthogonal LR", "annotated forward simulation"


def derive_theorem_facts(root: Path) -> tuple[str, ...]:
    spec_path = root / "Bang/Spec.lean"
    audit_path = root / "Bang/Audit.lean"
    spec = read(spec_path)
    audit = read(audit_path)
    names = ("lr_sound", "lr_fundamental", "compile_forward_sim")
    for name in names:
        require(spec, rf"^theorem {name}\b", spec_path, f"theorem {name}")
        require(audit, rf"^#print axioms {name}\b", audit_path, f"Audit enrollment for {name}")
    return names


def validate_current_snapshots(root: Path, target: str, default_engine: str) -> None:
    snapshots = {
        root / "README.md": (target, "forward simulation", "logical relation", "ADR-0059"),
        root / "ONBOARDING.md": (target, "forward simulation", "logical relation", "ADR-0059"),
        root / "docs/architecture/core-overview.md": (target, "forward simulation", "logical relation", "ADR-0059"),
        root / "CLAUDE.md": (target, "ADR-0059", "ADR-0035"),
    }
    for path, markers in snapshots.items():
        text = read(path)
        for marker in markers:
            if marker not in text:
                raise AssertionSourceError(f"current snapshot {path} is missing derived marker {marker!r}")
        if re.search(r"WasmFX (?:backend )?is the (?:verified )?(?:compiler |compilation )?target", text):
            raise AssertionSourceError(f"current snapshot {path} restores WasmFX as the primary target")

    readme = read(root / "README.md")
    onboarding = read(root / "ONBOARDING.md")
    for path, text in ((root / "README.md", readme), (root / "ONBOARDING.md", onboarding)):
        if not re.search(rf"`{re.escape(default_engine)}`\s*\|\s*Default", text):
            raise AssertionSourceError(
                f"current snapshot {path} does not identify derived default engine {default_engine!r}"
            )


def render(root: Path) -> str:
    facts = scan_bang(root)
    engines, default_engine, alias = derive_engine_facts(root / "Main.lean")
    target, equivalence_method, compilation_method = derive_decision_facts(root)
    lr_sound, lr_fundamental, compile_forward_sim = derive_theorem_facts(root)
    validate_current_snapshots(root, target, default_engine)
    tier_counts = Counter(fact.tier for fact in facts.modules.values())
    tiers = " · ".join(f"{tier} {tier_counts[tier]}" for tier in sorted(tier_counts))

    lines = [
        GEN_BEGIN,
        "### Architecture assertions",
        "",
        "_Generated from Lean source, module paths, and accepted ADRs. This is a reviewable projection, not a second architecture authority._",
        "",
        "| Fact | Current value | Authority |",
        "|---|---|---|",
        f"| Compiler target | **{target}**, grade-directed; WasmFX is only a future general-case fast path | [ADR-0059](../decisions/0059-wasm3-grade-directed-pluggable-backend.md) |",
        f"| Source equivalence | {equivalence_method}: `{lr_sound}`, `{lr_fundamental}` | [ADR-0035](../decisions/0035-lr-for-equivalence-simulation-for-compilation.md), `Bang/Spec.lean`, `Bang/Audit.lean` |",
        f"| Compilation correctness | {compilation_method}: `{compile_forward_sim}` | [ADR-0035](../decisions/0035-lr-for-equivalence-simulation-for-compilation.md), `Bang/Spec.lean`, `Bang/Audit.lean` |",
        f"| CLI engines | {', '.join(f'`{engine}`' for engine in engines)}; default **`{default_engine}`**; `{alias}` aliases compiled | `Main.lean:Engine`, `Main.lean:parseEngine` |",
        f"| Module graph | {len(facts.modules)} modules · {len(facts.edges)} internal edges · {tiers} | `tools/import_facts.py` over `Bang/**/*.lean` |",
        "| Architecture lineage | ADR-0016 two-hop shape, target revised by ADR-0059 | [ADR-0016](../decisions/0016-two-hop-architecture-calcvm-and-wasmfx.md), [ADR-0059](../decisions/0059-wasm3-grade-directed-pluggable-backend.md) |",
        GEN_END,
    ]
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="fail if the committed block is stale")
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
        block = render(root)
        current = read(doc)
        updated = splice(current, GEN_BEGIN, GEN_END, block)
    except (AssertionSourceError, ImportFactsError, ValueError) as exc:
        print(f"architecture-assertions: FAIL — {exc}")
        return 1

    if args.check:
        if updated != current:
            print("architecture-assertions: FAIL — generated snapshot is stale; run `just architecture-assertions`.")
            return 1
        print("architecture-assertions: PASS — generated snapshot matches code and accepted ADRs.")
        return 0

    doc.write_text(updated, encoding="utf-8")
    print("architecture-assertions: regenerated docs/architecture/core-overview.md snapshot.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
