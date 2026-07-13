#!/usr/bin/env python3
# tool: role=check couples=Bang/**/*.lean,import_facts.py runs-in=fitness
"""Enforce BANG's path-derived inward dependency V over shared import facts."""

from __future__ import annotations

import argparse
import os
import subprocess
from pathlib import Path

from import_facts import ImportFactsError, scan_bang

RANK = {
    "Core": 0,
    "Frontend": 1,
    "Backend": 1,
    "Meta": 2,
    "Witness": 2,
    "Reify": 2,
    "Apex": 3,
}


def forbidden(importer: str, imported: str) -> bool:
    if {importer, imported} == {"Frontend", "Backend"}:
        return True
    return RANK[importer] < RANK[imported]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "root",
        nargs="?",
        default=os.environ.get("REFS_ROOT", "."),
        help="repository root (default: REFS_ROOT or current directory)",
    )
    args = parser.parse_args()

    try:
        subprocess.run(
            ["bash", str(Path(__file__).with_name("tool-log.sh")), Path(__file__).name],
            check=False,
        )
        facts = scan_bang(args.root)
    except ImportFactsError as exc:
        print(f"── arch-check (import-direction fitness function) ──\nFAIL: {exc}")
        return 1

    violations: list[str] = []
    for importer, imported in facts.edges:
        importer_fact = facts.modules[importer]
        imported_fact = facts.modules[imported]
        if forbidden(importer_fact.tier, imported_fact.tier):
            violations.append(
                f"VIOLATION: {importer} [{importer_fact.tier}] imports "
                f"{imported} [{imported_fact.tier}] — the V forbids "
                f"{importer_fact.tier} → {imported_fact.tier}"
            )

    print("── arch-check (import-direction fitness function) ──")
    if violations:
        print("\n".join(violations))
        print(f"FAIL: {len(violations)} dependency-direction violation(s).")
        return 1

    print(
        f"PASS: the V holds across {len(facts.edges)} internal edges — Core imports neither edge; "
        "Frontend and Backend meet only at Core."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
