#!/usr/bin/env python3
# tool: role=lib couples=docs/decisions/*.md,docs/notes/OPEN_QUESTIONS.md,gen-adr-index.py runs-in=fitness
"""Authoritative ADR frontmatter, relationship, question, and status facts."""

from __future__ import annotations

import re
from pathlib import Path

FIELD_RE = re.compile(
    r"^\s*[-*]\s*\*{0,2}([A-Za-z][\w -]*?)\*{0,2}\s*:\s*\*{0,2}\s*(.*\S)?\s*$"
)
H1_RE = re.compile(r"^#\s+(.*\S)\s*$")
TITLE_STRIP_RE = re.compile(r"^(?:ADR[- ]?)?\d{4}\s*[·—–-]\s*", re.IGNORECASE)
SENTINEL = "<!-- adr-frontmatter -->"
Q_INDEX_RE = re.compile(r"^- \[Q(\d+)\b.*?\]\([^)]*\)(?:\s*·\s*(.*))?$")
RELATIONSHIP_FIELDS = (
    "supersedes",
    "amends",
    "refines",
    "seealso",
    "dependson",
    "resolves",
)


def norm_key(key: str) -> str:
    return re.sub(r"[ \-]", "", key).lower()


def nums(value: str) -> list[str]:
    return re.findall(r"\b(\d{4})\b", value)


def qnums(value: str) -> list[str]:
    if not re.match(r"^\s*Q\d+\b", value):
        return []
    return re.findall(r"\bQ(\d+)\b", value)


def _frontmatter_fields(
    lines: list[str], path: Path
) -> tuple[dict[str, str], dict[str, str], int]:
    if SENTINEL not in lines:
        raise SystemExit(
            f"FAIL: {path.name} has no `{SENTINEL}` frontmatter block.\n"
            "      Every ADR needs the machine-frontmatter block (run the sweep)."
        )
    start = lines.index(SENTINEL) + 1
    fields: dict[str, str] = {}
    field_heads: dict[str, str] = {}
    current: str | None = None
    block_end = len(lines)
    saw_field = False
    for index in range(start, len(lines)):
        line = lines[index]
        match = FIELD_RE.match(line)
        if match:
            current = norm_key(match.group(1))
            value = (match.group(2) or "").strip()
            fields[current] = value
            field_heads[current] = value
            saw_field = True
            continue
        if not line.strip():
            if saw_field:
                block_end = index
                break
            continue
        if current is None or not line[:1].isspace():
            block_end = index
            break
        fields[current] = " ".join(
            part for part in (fields[current], line.strip()) if part
        )
    return fields, field_heads, block_end


def parse_adr(path: Path) -> dict:
    num = path.name[:4]
    title = None
    lines = path.read_text(encoding="utf-8").splitlines()

    for line in lines:
        match = H1_RE.match(line)
        if match:
            title = TITLE_STRIP_RE.sub("", match.group(1)).strip()
            break

    fields, field_heads, block_end = _frontmatter_fields(lines, path)
    prose_status = None
    for line in lines[block_end:]:
        match = FIELD_RE.match(line)
        if match and norm_key(match.group(1)) == "status":
            prose_status = (match.group(2) or "").strip()
            break
    if prose_status is None:
        for index, line in enumerate(lines):
            if line.strip() == "## Status":
                for following in lines[index + 1 :]:
                    if following.strip():
                        prose_status = following.strip()
                        break
                break

    return {
        "num": num,
        "file": path.name,
        "title": title,
        "fields": fields,
        "field_heads": field_heads,
        "prose_status": prose_status,
    }


def status_of(fields: dict[str, str]) -> str:
    raw = fields.get("status", "")
    return raw.split()[0].rstrip(".") if raw else "—"


def collect(decisions: Path) -> list[dict]:
    adrs = [
        parse_adr(path) for path in sorted(decisions.glob("[0-9][0-9][0-9][0-9]-*.md"))
    ]
    by_num = {adr["num"]: adr for adr in adrs}
    for adr in adrs:
        adr["superseded_by"] = []
        adr["amended_by"] = []
    for adr in adrs:
        for target in nums(adr["fields"].get("supersedes", "")):
            if target in by_num:
                by_num[target]["superseded_by"].append(adr["num"])
        for target in nums(adr["fields"].get("amends", "")):
            if target in by_num:
                by_num[target]["amended_by"].append(adr["num"])
    for adr in adrs:
        adr["superseded_by"].sort()
        adr["amended_by"].sort()
    return adrs


def relationship_fields(fields: dict[str, str]) -> dict[str, str]:
    names = {
        "supersedes": "supersedes",
        "amends": "amends",
        "refines": "refines",
        "seealso": "seeAlso",
        "dependson": "dependsOn",
        "resolves": "resolves",
    }
    return {names[key]: fields[key] for key in RELATIONSHIP_FIELDS if fields.get(key)}


def parse_open_questions(path: Path) -> dict[int, dict]:
    out: dict[int, dict] = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        match = Q_INDEX_RE.match(line)
        if not match:
            continue
        question = int(match.group(1))
        marker = (match.group(2) or "").strip()
        resolved = "✓ RESOLVED" in marker
        partial = marker.startswith("◑") or "PARTIAL" in marker
        adrs = nums(marker) if (resolved or partial) else []
        out[question] = {"resolved": resolved, "partial": partial, "adrs": adrs}
    return out


def status_word(raw: str | None) -> str | None:
    return raw.split()[0].rstrip(".").lower() if raw else None


def status_consistency_check(adrs: list[dict]) -> list[str]:
    errors: list[str] = []
    for adr in adrs:
        sentinel = status_word(adr["fields"].get("status"))
        prose = status_word(adr.get("prose_status"))
        if prose is not None and sentinel != prose:
            errors.append(
                f"{adr['num']}: sentinel Status `{sentinel}` ≠ prose Status "
                f"`{prose}` ({adr['file']}). Reconcile the two copies."
            )
    return errors


def crossref_check(adrs: list[dict], open_questions: Path) -> list[str]:
    errors: list[str] = []
    question_map = parse_open_questions(open_questions)
    adr_resolves: dict[int, list[str]] = {}
    for adr in adrs:
        for question in qnums(adr["fields"].get("resolves", "")):
            adr_resolves.setdefault(int(question), []).append(adr["num"])

    for question, info in question_map.items():
        if not info["resolved"]:
            continue
        for adr in info["adrs"]:
            if adr not in adr_resolves.get(question, []):
                errors.append(
                    f"Q{question}: OPEN_QUESTIONS marks it RESOLVED by ADR-{adr}, but "
                    f"{adr}-*.md does not declare `Resolves: Q{question}`."
                )

    for question, declaring_adrs in adr_resolves.items():
        info = question_map.get(question)
        if info is None:
            errors.append(
                f"Q{question}: declared resolved by {', '.join(declaring_adrs)}, but Q{question} is "
                "absent from OPEN_QUESTIONS.md."
            )
        elif not (info["resolved"] or info["partial"]):
            errors.append(
                f"Q{question}: declared resolved by {', '.join(declaring_adrs)}, but "
                f"OPEN_QUESTIONS.md still marks Q{question} as OPEN. Flip its status marker."
            )
    return errors
