#!/usr/bin/env python3
# tool: role=lib couples=Bang/Audit.lean,gen-proof-state.py runs-in=fitness
"""Audit enrollment, command, axiom-report, and trusted-three classification facts."""

from __future__ import annotations

import os
import re
import subprocess
from dataclasses import dataclass
from pathlib import Path

TRUSTED = frozenset({"propext", "Classical.choice", "Quot.sound"})
HEADLINE_RE = re.compile(r"^\s*#print axioms\s+(\S+)\s*$")
DEPENDS_RE = re.compile(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", re.DOTALL)
NODEPS_RE = re.compile(r"'([^']+)' does not depend on any axioms")


class AuditFactsError(ValueError):
    """Audit source or output does not resolve to one unambiguous fact."""


@dataclass(frozen=True)
class Enrollment:
    written_ref: str
    line: int


def enrollments(lean_root: str | Path) -> list[Enrollment]:
    path = Path(lean_root) / "Bang/Audit.lean"
    result = []
    for line_number, line in enumerate(
        path.read_text(encoding="utf-8").splitlines(), 1
    ):
        if match := HEADLINE_RE.match(line):
            result.append(Enrollment(match.group(1), line_number))
    if not result:
        raise AuditFactsError(f"no active #print axioms enrollments in {path}")
    refs = [entry.written_ref for entry in result]
    if len(refs) != len(set(refs)):
        raise AuditFactsError(f"duplicate Audit enrollment in {path}")
    return result


def headlines(lean_root: str) -> list[str]:
    return [entry.written_ref for entry in enrollments(lean_root)]


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


def authoritative_axiom_output(lean_root: str | Path) -> str:
    root = str(Path(lean_root).resolve())
    build = run(["lake", "build", "Bang.Audit"], root)
    if build is None:
        raise AuditFactsError(
            "lake is unavailable; authoritative Audit build cannot run"
        )
    if build[0] != 0:
        raise AuditFactsError(f"lake build Bang.Audit failed ({build[0]}):\n{build[1]}")
    audit = Path(root) / "Bang/Audit.lean"
    if not audit.is_file():
        raise AuditFactsError(f"missing Audit authority: {audit}")
    os.utime(audit, None)
    elaboration = run(["lake", "env", "lean", "Bang/Audit.lean"], root)
    if elaboration is None:
        raise AuditFactsError(
            "lake is unavailable; authoritative Audit elaboration cannot run"
        )
    if elaboration[0] != 0:
        raise AuditFactsError(
            f"lake env lean Bang/Audit.lean failed ({elaboration[0]}):\n{elaboration[1]}"
        )
    if not elaboration[1].strip():
        raise AuditFactsError(
            "authoritative Audit elaboration produced empty kernel output"
        )
    return elaboration[1]


def axiom_report(lean_root: str, build: bool):
    """Compatibility API for gen-proof-state.py; unlike docfacts, it may return None."""
    audit = os.path.join(lean_root, "Bang", "Audit.lean")
    if build:
        built = run(["lake", "build", "Bang.Audit"], lean_root)
        if built is None or built[0] != 0:
            return None
    if os.path.exists(audit):
        os.utime(audit, None)
    result = run(["lake", "env", "lean", "Bang/Audit.lean"], lean_root)
    return None if result is None else result[1]


def normalize_axiom(axiom: str) -> str:
    value = " ".join(axiom.split())
    return "sorryAx" if value.startswith("sorryAx ") else value


def parse_axiom_entries(text: str) -> list[tuple[str, list[str]]]:
    entries: list[tuple[int, str, list[str]]] = []
    for match in NODEPS_RE.finditer(text):
        entries.append((match.start(), match.group(1), []))
    for match in DEPENDS_RE.finditer(text):
        axioms = sorted(
            {
                normalize_axiom(axiom)
                for axiom in match.group(2).split(",")
                if axiom.strip()
            }
        )
        entries.append((match.start(), match.group(1), axioms))
    entries.sort(key=lambda entry: entry[0])
    return [(name, axioms) for _, name, axioms in entries]


def parse_axioms(text: str) -> dict[str, list[str]]:
    """Preserve the historical report projection used by gen-proof-state.py."""
    found: dict[str, list[str]] = {}
    for name in NODEPS_RE.findall(text):
        found[name] = []
    for name, axioms in DEPENDS_RE.findall(text):
        found[name] = [axiom.strip() for axiom in axioms.split(",") if axiom.strip()]
    return found


def reference_matches(written_ref: str, report_name: str) -> bool:
    if report_name == written_ref:
        return True
    if "." in written_ref:
        return False
    return report_name == f"Bang.{written_ref}"


def resolve_reports(
    audit_entries: list[Enrollment], report_entries: list[tuple[str, list[str]]]
) -> list[tuple[Enrollment, str, list[str]]]:
    if not report_entries:
        raise AuditFactsError("Audit kernel output contains no axiom reports")
    resolved = []
    used: set[int] = set()
    for enrollment in audit_entries:
        matches = [
            (index, name, axioms)
            for index, (name, axioms) in enumerate(report_entries)
            if reference_matches(enrollment.written_ref, name)
        ]
        if len(matches) != 1:
            names = ", ".join(name for _, name, _ in matches) or "none"
            raise AuditFactsError(
                f"Audit enrollment {enrollment.written_ref!r} resolved to {len(matches)} reports: {names}"
            )
        index, name, axioms = matches[0]
        if index in used:
            raise AuditFactsError(
                f"kernel report {name!r} resolves more than one enrollment"
            )
        used.add(index)
        resolved.append((enrollment, name, sorted(set(axioms))))
    extras = [
        name for index, (name, _) in enumerate(report_entries) if index not in used
    ]
    if extras:
        raise AuditFactsError(
            f"kernel output contains unenrolled axiom reports: {', '.join(extras)}"
        )
    canonical = [name for _, name, _ in resolved]
    if len(canonical) != len(set(canonical)):
        raise AuditFactsError("canonical Audit report names are not unique")
    return resolved


def resolve_headline(headline: str, report: dict[str, list[str]]) -> list[str] | None:
    matches = [
        (name, axioms)
        for name, axioms in report.items()
        if reference_matches(headline, name)
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
