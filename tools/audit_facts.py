#!/usr/bin/env python3
# tool: role=lib couples=Bang/Audit.lean,gen-proof-state.py runs-in=fitness
"""Audit headline, command, axiom-report, and trusted-three classification facts."""

from __future__ import annotations

import os
import re
import subprocess

TRUSTED = frozenset({"propext", "Classical.choice", "Quot.sound"})
HEADLINE_RE = re.compile(r"^\s*#print axioms\s+(\S+)\s*$")
DEPENDS_RE = re.compile(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", re.DOTALL)
NODEPS_RE = re.compile(r"'([^']+)' does not depend on any axioms")


class AuditFactsError(ValueError):
    """Audit source or output does not resolve to one unambiguous fact."""


def headlines(lean_root: str) -> list[str]:
    path = os.path.join(lean_root, "Bang", "Audit.lean")
    with open(path, encoding="utf-8") as audit:
        return [
            match.group(1)
            for line in audit.read().splitlines()
            if (match := HEADLINE_RE.match(line))
        ]


def run(cmd: list[str], cwd: str):
    try:
        process = subprocess.run(
            cmd,
            cwd=cwd,
            capture_output=True,
            text=True,
            timeout=900,
        )
        return process.returncode, (process.stdout or "") + (process.stderr or "")
    except FileNotFoundError:
        return None
    except subprocess.TimeoutExpired:
        return 1, ""


def axiom_report(lean_root: str, build: bool):
    audit = os.path.join(lean_root, "Bang", "Audit.lean")
    if build and run(["lake", "build", "Bang.Audit"], lean_root) is None:
        return None
    if os.path.exists(audit):
        os.utime(audit, None)
    result = run(["lake", "env", "lean", "Bang/Audit.lean"], lean_root)
    return None if result is None else result[1]


def parse_axioms(text: str) -> dict[str, list[str]]:
    found: dict[str, list[str]] = {}
    for name in NODEPS_RE.findall(text):
        found[name] = []
    for name, axioms in DEPENDS_RE.findall(text):
        found[name] = [axiom.strip() for axiom in axioms.split(",") if axiom.strip()]
    return found


def resolve_headline(headline: str, report: dict[str, list[str]]) -> list[str] | None:
    matches = [
        (name, axioms)
        for name, axioms in report.items()
        if name == headline
        or name.endswith("." + headline)
        or headline.endswith("." + name)
    ]
    if len(matches) > 1:
        names = ", ".join(name for name, _ in matches)
        raise AuditFactsError(f"ambiguous Audit headline {headline!r}: {names}")
    return matches[0][1] if matches else None


def classify(
    lean_root: str,
    report: dict[str, list[str]],
) -> tuple[list[str], list[str], list[tuple[str, list[str]]]]:
    clean: list[str] = []
    pending: list[str] = []
    flagged: list[tuple[str, list[str]]] = []
    for headline in headlines(lean_root):
        axioms = resolve_headline(headline, report)
        if axioms is None:
            pending.append(headline)
        elif set(axioms) <= TRUSTED:
            clean.append(headline)
        else:
            flagged.append((headline, axioms))
    return clean, pending, flagged
