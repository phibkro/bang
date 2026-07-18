#!/usr/bin/env python3
"""Validate agentic usability session JSON files and print a Markdown summary."""

from __future__ import annotations

import json
import sys
from collections import Counter, defaultdict
from pathlib import Path


OUTCOMES = {"success", "partial", "failure", "blocked", "excluded"}
SEVERITIES = {"critical", "high", "medium", "low", "instrument"}
EVIDENCE_GRADES = {"A", "B", "C", "D"}


def fail(message: str) -> None:
    raise ValueError(message)


def load_session(path: Path) -> dict:
    try:
        data = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        fail(f"{path}: cannot read valid JSON: {exc}")

    for field in (
        "schema_version",
        "study_id",
        "session_id",
        "contaminated",
        "tasks",
        "findings",
    ):
        if field not in data:
            fail(f"{path}: missing {field}")
    if data["schema_version"] != 1:
        fail(f"{path}: unsupported schema_version {data['schema_version']!r}")
    if not isinstance(data["contaminated"], bool):
        fail(f"{path}: contaminated must be boolean")
    if not isinstance(data["tasks"], list) or not isinstance(data["findings"], list):
        fail(f"{path}: tasks and findings must be arrays")

    for task in data["tasks"]:
        for field in ("id", "outcome", "actions", "errors", "detours", "interventions"):
            if field not in task:
                fail(f"{path}: task missing {field}")
        if task["outcome"] not in OUTCOMES:
            fail(f"{path}: invalid outcome {task['outcome']!r}")
        for field in ("actions", "errors", "detours", "interventions"):
            if not isinstance(task[field], int) or task[field] < 0:
                fail(
                    f"{path}: task {task['id']} {field} must be a non-negative integer"
                )

    for finding in data["findings"]:
        if not finding.get("key"):
            fail(f"{path}: finding missing key")
        if finding.get("severity") not in SEVERITIES:
            fail(f"{path}: invalid finding severity {finding.get('severity')!r}")
        if finding.get("evidence_grade") not in EVIDENCE_GRADES:
            fail(f"{path}: invalid evidence grade {finding.get('evidence_grade')!r}")
    return data


def main(argv: list[str]) -> int:
    if len(argv) != 2:
        print(f"usage: {Path(argv[0]).name} <session-directory>", file=sys.stderr)
        return 2
    root = Path(argv[1])
    paths = sorted(root.glob("*.json"))
    if not paths:
        print(f"error: no .json sessions in {root}", file=sys.stderr)
        return 2

    try:
        sessions = [(path, load_session(path)) for path in paths]
    except ValueError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1

    included = [(path, data) for path, data in sessions if not data["contaminated"]]
    excluded = len(sessions) - len(included)
    task_counts: dict[str, Counter] = defaultdict(Counter)
    task_effort: dict[str, Counter] = defaultdict(Counter)
    findings: dict[str, dict] = {}
    finding_sessions: dict[str, set[str]] = defaultdict(set)

    for _, session in included:
        for task in session["tasks"]:
            task_counts[task["id"]][task["outcome"]] += 1
            for field in ("actions", "errors", "detours", "interventions"):
                task_effort[task["id"]][field] += task[field]
        for finding in session["findings"]:
            findings.setdefault(finding["key"], finding)
            finding_sessions[finding["key"]].add(session["session_id"])

    study_ids = sorted({data["study_id"] for _, data in sessions})
    print(f"# Agentic user-testing summary: {', '.join(study_ids)}")
    print()
    print(
        f"Sessions: {len(sessions)} total, {len(included)} included, {excluded} contaminated/excluded."
    )
    print()
    print("## Task outcomes")
    print()
    print(
        "| Task | Success | Partial | Failure | Blocked | Actions | Errors | Detours | Interventions |"
    )
    print("|---|---:|---:|---:|---:|---:|---:|---:|---:|")
    for task_id in sorted(task_counts):
        outcomes = task_counts[task_id]
        effort = task_effort[task_id]
        print(
            f"| {task_id} | {outcomes['success']} | {outcomes['partial']} | "
            f"{outcomes['failure']} | {outcomes['blocked']} | {effort['actions']} | "
            f"{effort['errors']} | {effort['detours']} | {effort['interventions']} |"
        )

    print()
    print("## Repeated finding keys")
    print()
    print("| Finding | Severity | Grade | Included sessions |")
    print("|---|---|---|---:|")
    severity_order = {"critical": 0, "high": 1, "medium": 2, "low": 3, "instrument": 4}
    for key in sorted(
        findings, key=lambda item: (severity_order[findings[item]["severity"]], item)
    ):
        print(
            f"| {key} | {findings[key]['severity']} | {findings[key]['evidence_grade']} | "
            f"{len(finding_sessions[key])} |"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
