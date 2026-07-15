#!/usr/bin/env python3
# tool: role=lib couples=examples/thunk-force/main.bang,examples/effect-op-arith/main.bang,examples/logger-counting/main.bang,examples/logger-silent/main.bang runs-in=manual
"""Execute the machine-checkable substrate of the common newcomer journey."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys
from collections import Counter
from collections.abc import Callable
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
BANG = ROOT / ".lake/build/bin/bang"
ENGINES = ("env", "oracle", "compiled")
EXPECTED_STEP_IDS = (
    "arithmetic-env",
    "arithmetic-oracle",
    "arithmetic-compiled",
    "thunk-force-env",
    "thunk-force-oracle",
    "thunk-force-compiled",
    "effect-op-arith-env",
    "effect-op-arith-oracle",
    "effect-op-arith-compiled",
    "logger-counting-env",
    "logger-counting-oracle",
    "logger-counting-compiled",
    "logger-silent-env",
    "logger-silent-oracle",
    "logger-silent-compiled",
    "logger-handler-only-swap",
    "logger-check-json",
    "logger-query-dump",
)


def run(args: list[str]) -> subprocess.CompletedProcess[str]:
    return subprocess.run(args, cwd=ROOT, text=True, capture_output=True)


def git(*args: str) -> str:
    result = run(["git", *args])
    if result.returncode != 0:
        raise RuntimeError(result.stderr.strip() or "git command failed")
    return result.stdout.strip()


def expected(path: str) -> str:
    return (ROOT / path).read_text(encoding="utf-8")


def command_step(
    step_id: str,
    args: list[str],
    expected_stdout: str,
    *,
    category: str,
    engine: str | None = None,
    fixture: str | None = None,
) -> dict[str, Any]:
    result = run(args)
    passed = (
        result.returncode == 0
        and result.stdout == expected_stdout
        and result.stderr == ""
    )
    return {
        "id": step_id,
        "category": category,
        "engine": engine,
        "fixture": fixture,
        "argv": args,
        "exit": result.returncode,
        "stdout": result.stdout,
        "stderr": result.stderr,
        "expectedStdout": expected_stdout,
        "status": "pass" if passed else "fail",
    }


def semantic_step(
    step_id: str,
    args: list[str],
    check: Callable[[str], None],
    expected_summary: str,
    *,
    category: str,
    fixture: str,
) -> dict[str, Any]:
    result = run(args)
    error = ""
    passed = result.returncode == 0 and result.stderr == ""
    if passed:
        try:
            check(result.stdout)
        except (
            AssertionError,
            json.JSONDecodeError,
            KeyError,
            TypeError,
            ValueError,
        ) as exc:
            error = str(exc)
            passed = False
    return {
        "id": step_id,
        "category": category,
        "engine": None,
        "fixture": fixture,
        "argv": args,
        "exit": result.returncode,
        "stdout": result.stdout,
        "stderr": result.stderr or error,
        "expected": expected_summary,
        "status": "pass" if passed else "fail",
    }


def build_runner() -> None:
    if os.environ.get("BANG_BIN_FRESH"):
        return
    result = run(["lake", "build", "bang"])
    if result.returncode != 0:
        sys.stderr.write(result.stdout)
        sys.stderr.write(result.stderr)
        raise SystemExit(result.returncode)


def handler_swap_step() -> dict[str, Any]:
    counting = expected("examples/logger-counting/main.bang")
    silent = expected("examples/logger-silent/main.bang")
    transformed = counting.replace("log(msg) => 1", "log(msg) => 0")
    passed = transformed == silent and counting.count("log(msg) => 1") == 1
    return {
        "id": "logger-handler-only-swap",
        "category": "source-invariant",
        "engine": None,
        "fixture": "examples/logger-counting/main.bang + examples/logger-silent/main.bang",
        "argv": [],
        "exit": 0 if passed else 1,
        "stdout": "handler clause only\n" if passed else "",
        "stderr": "" if passed else "logger variants differ outside the handler clause",
        "expectedStdout": "handler clause only\n",
        "status": "pass" if passed else "fail",
    }


def query_dump_check(stdout: str) -> None:
    payload = json.loads(stdout)
    assert payload["ok"] is True, "query dump returned ok:false"
    assert payload["schemaVersion"] == 1, "query schema version drifted"
    log_decl = next((item for item in payload["decls"] if item["name"] == "Log"), None)
    assert log_decl is not None, "Log declaration missing"
    assert log_decl["kind"] == "effect", "Log is not an effect declaration"
    operations = log_decl["shape"]["ops"]
    assert {"name": "log", "type": "Int -> Int"} in operations, (
        "Log.log signature missing"
    )


def step_contract(steps: list[dict[str, Any]]) -> dict[str, Any]:
    expected = set(EXPECTED_STEP_IDS)
    counts = Counter(step["id"] for step in steps)
    missing = sorted(expected - counts.keys())
    extra = sorted(counts.keys() - expected)
    duplicates = sorted(step_id for step_id, count in counts.items() if count > 1)
    failed_required = sorted(
        step["id"]
        for step in steps
        if step["id"] in expected and step["status"] != "pass"
    )
    failure_count = (
        len(missing)
        + len(extra)
        + sum(counts[step_id] - 1 for step_id in duplicates)
        + len(set(failed_required))
    )
    passed = len(expected) - len(missing) - len(set(failed_required))
    return {
        "expectedIds": list(EXPECTED_STEP_IDS),
        "missing": missing,
        "extra": extra,
        "duplicates": duplicates,
        "passed": passed,
        "failed": failure_count,
    }


def report() -> dict[str, Any]:
    build_runner()
    steps: list[dict[str, Any]] = []

    for engine in ENGINES:
        steps.append(
            command_step(
                f"arithmetic-{engine}",
                [str(BANG), "eval", f"--engine={engine}", "1 + 2"],
                "3\n",
                category="eval",
                engine=engine,
            )
        )

    fixtures = (
        ("thunk-force", "examples/thunk-force/main.bang"),
        ("effect-op-arith", "examples/effect-op-arith/main.bang"),
        ("logger-counting", "examples/logger-counting/main.bang"),
        ("logger-silent", "examples/logger-silent/main.bang"),
    )
    for fixture_id, path in fixtures:
        expected_path = str(Path(path).with_name("expected.txt"))
        for engine in ENGINES:
            steps.append(
                command_step(
                    f"{fixture_id}-{engine}",
                    [str(BANG), "run", f"--engine={engine}", path],
                    expected(expected_path),
                    category="run",
                    engine=engine,
                    fixture=path,
                )
            )

    steps.append(handler_swap_step())
    steps.append(
        command_step(
            "logger-check-json",
            [str(BANG), "check", "--json", "examples/logger-counting/main.bang"],
            '{"ok":true,"diagnostics":[]}\n',
            category="check",
            fixture="examples/logger-counting/main.bang",
        )
    )
    steps.append(
        semantic_step(
            "logger-query-dump",
            [str(BANG), "query", "dump", "examples/logger-counting/main.bang"],
            query_dump_check,
            "schemaVersion 1 with Log.log : Int -> Int",
            category="query",
            fixture="examples/logger-counting/main.bang",
        )
    )

    contract = step_contract(steps)
    return {
        "schemaVersion": 1,
        "kind": "onboarding-journey-run",
        "sourceSha": git("rev-parse", "HEAD"),
        "worktreeClean": git("status", "--porcelain=v1") == "",
        "binarySha256": hashlib.sha256(BANG.read_bytes()).hexdigest(),
        "steps": steps,
        "contract": {
            "expectedIds": contract["expectedIds"],
            "missing": contract["missing"],
            "extra": contract["extra"],
            "duplicates": contract["duplicates"],
        },
        "summary": {
            "expected": len(EXPECTED_STEP_IDS),
            "passed": contract["passed"],
            "failed": contract["failed"],
            "skipped": 0,
        },
    }


def render_human(value: dict[str, Any]) -> None:
    print("── onboarding journey ──")
    for step in value["steps"]:
        marker = "✓" if step["status"] == "pass" else "✗"
        print(f"{marker} {step['id']}")
        if step["status"] != "pass":
            print(f"    expected: {step.get('expectedStdout', step.get('expected'))!r}")
            print(f"    stdout:   {step['stdout']!r}")
            print(f"    stderr:   {step['stderr']!r}")
    summary = value["summary"]
    print(
        f"onboarding-journey: {summary['passed']}/{summary['expected']} passed, "
        f"{summary['failed']} failed, {summary['skipped']} skipped"
    )


def self_test() -> None:
    try:
        query_dump_check('{"ok":true,"schemaVersion":1,"decls":[]}')
    except AssertionError as error:
        assert str(error) == "Log declaration missing"
    else:
        raise AssertionError("missing Log declaration was accepted")
    fake_steps = [
        {"id": step_id, "status": "pass"} for step_id in EXPECTED_STEP_IDS[:-1]
    ]
    fake_steps.append({"id": EXPECTED_STEP_IDS[0], "status": "pass"})
    contract = step_contract(fake_steps)
    assert contract["missing"] == [EXPECTED_STEP_IDS[-1]]
    assert contract["duplicates"] == [EXPECTED_STEP_IDS[0]]
    assert contract["failed"] == 2
    print("onboarding-journey self-test: semantic and step-contract poles hold")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        self_test()
        return
    value = report()
    if args.json:
        print(json.dumps(value, sort_keys=True, separators=(",", ":")))
    else:
        render_human(value)
    raise SystemExit(1 if value["summary"]["failed"] else 0)


if __name__ == "__main__":
    main()
