#!/usr/bin/env python3
# tool: role=gen couples=Bang/**/*.lean,Main.lean,docs/decisions/0016-*.md,docs/decisions/0035-*.md,docs/decisions/0059-*.md,docs/architecture/core-overview.md,architecture_facts.py,import_facts.py runs-in=fitness
"""Generate/check the current architecture snapshot from code and accepted ADRs."""

from __future__ import annotations

import argparse
import os
import re
import subprocess
from collections import Counter
from pathlib import Path

from architecture_facts import (
    ArchitectureFactsError as AssertionSourceError,
    derive_decision_facts,
    derive_engine_facts,
    read_source as read,
    require_source as require,
)
from genblock import splice
from import_facts import ImportFactsError, scan_bang

GEN_BEGIN = "<!-- BEGIN GENERATED architecture-assertions (just architecture-assertions) — do not hand-edit -->"
GEN_END = "<!-- END GENERATED architecture-assertions -->"


def derive_theorem_facts(root: Path) -> tuple[str, ...]:
    spec_path = root / "Bang/Spec.lean"
    audit_path = root / "Bang/Audit.lean"
    spec = read(spec_path)
    audit = read(audit_path)
    names = ("lr_sound", "lr_fundamental", "compile_forward_sim")
    for name in names:
        require(spec, rf"^theorem {name}\b", spec_path, f"theorem {name}")
        require(
            audit,
            rf"^#print axioms {name}\b",
            audit_path,
            f"Audit enrollment for {name}",
        )
    return names


def validate_current_snapshots(root: Path, target: str, default_engine: str) -> None:
    snapshots = {
        root / "README.md": (
            target,
            "forward simulation",
            "logical relation",
            "ADR-0059",
        ),
        root / "ONBOARDING.md": (
            target,
            "forward simulation",
            "logical relation",
            "ADR-0059",
        ),
        root / "docs/architecture/core-overview.md": (
            target,
            "forward simulation",
            "logical relation",
            "ADR-0059",
        ),
        root / "CLAUDE.md": (target, "ADR-0059", "ADR-0035"),
    }
    for path, markers in snapshots.items():
        text = read(path)
        for marker in markers:
            if marker not in text:
                raise AssertionSourceError(
                    f"current snapshot {path} is missing derived marker {marker!r}"
                )
        if re.search(
            r"WasmFX (?:backend )?is the (?:verified )?(?:compiler |compilation )?target",
            text,
        ):
            raise AssertionSourceError(
                f"current snapshot {path} restores WasmFX as the primary target"
            )

    readme = read(root / "README.md")
    onboarding = read(root / "ONBOARDING.md")
    for path, text in (
        (root / "README.md", readme),
        (root / "ONBOARDING.md", onboarding),
    ):
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
    parser.add_argument(
        "--check", action="store_true", help="fail if the committed block is stale"
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
        block = render(root)
        current = read(doc)
        updated = splice(current, GEN_BEGIN, GEN_END, block)
    except (AssertionSourceError, ImportFactsError, ValueError) as exc:
        print(f"architecture-assertions: FAIL — {exc}")
        return 1

    if args.check:
        if updated != current:
            print(
                "architecture-assertions: FAIL — generated snapshot is stale; run `just architecture-assertions`."
            )
            return 1
        print(
            "architecture-assertions: PASS — generated snapshot matches code and accepted ADRs."
        )
        return 0

    doc.write_text(updated, encoding="utf-8")
    print(
        "architecture-assertions: regenerated docs/architecture/core-overview.md snapshot."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
