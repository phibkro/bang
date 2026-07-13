#!/usr/bin/env python3
# tool: role=gen couples=examples/logger-counting,docfacts/schema/example.schema.json,docs/reference/examples/logger-counting.md runs-in=fitness
"""docfacts_logger.py — generate and validate the logger-counting documentation fact.

The committed JSON fact is the consumer boundary: Markdown is rendered only after
that JSON has been serialized, reloaded, and schema-validated.
"""

import argparse
import copy
import json
import subprocess
import sys
from pathlib import Path

from jsonschema import Draft202012Validator
from jsonschema.exceptions import ValidationError

ROOT = Path(
    subprocess.run(
        ["git", "rev-parse", "--show-toplevel"],
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()
)
SCHEMA_PATH = ROOT / "docfacts/schema/example.schema.json"
FACT_PATH = ROOT / "docfacts/examples/logger-counting.json"
MARKDOWN_PATH = ROOT / "docs/reference/examples/logger-counting.md"
PROGRAM_PATH = "examples/logger-counting/main.bang"
EXPECTED_PATH = "examples/logger-counting/expected.txt"
PUBLIC_SOURCE_BASE = "https://github.com/phibkro/bang/blob/main"


def read_repo_file(path: str) -> str:
    return (ROOT / path).read_text(encoding="utf-8")


def prose_list(items: list[str]) -> str:
    if len(items) == 1:
        return items[0]
    if len(items) == 2:
        return f"{items[0]} and {items[1]}"
    return f"{', '.join(items[:-1])}, and {items[-1]}"


def build_fact() -> dict:
    supported_engines = ["env", "oracle", "compiled"]
    return {
        "schemaVersion": 1,
        "kind": "example",
        "id": "logger-counting",
        "title": "Logger counting",
        "summary": (
            "A custom Log handler turns three log operations into the value 3 by "
            "returning one from each operation."
        ),
        "supportedEngines": supported_engines,
        "concepts": ["effect-handlers", "custom-effects", "differential-testing"],
        "refusalClass": None,
        "program": {"path": PROGRAM_PATH, "text": read_repo_file(PROGRAM_PATH)},
        "expectedOutput": {
            "path": EXPECTED_PATH,
            "text": read_repo_file(EXPECTED_PATH),
        },
        "evidence": [
            {
                "label": "differential-tested",
                "claim": (
                    f"The {prose_list(supported_engines)} engines each produce the "
                    "committed expected output byte-for-byte; check --json and query "
                    "dump also succeed."
                ),
                "sources": [
                    PROGRAM_PATH,
                    EXPECTED_PATH,
                    "tools/test-docfacts-logger.sh",
                ],
                "commands": ["just test-docfacts-logger"],
            },
            {
                "label": "generated",
                "claim": (
                    "The docfact and this reference page are deterministic renderings of "
                    "the canonical example files."
                ),
                "sources": [
                    PROGRAM_PATH,
                    EXPECTED_PATH,
                    "docfacts/schema/example.schema.json",
                    "tools/docfacts_logger.py",
                ],
                "commands": ["just docs-check"],
            },
        ],
        "relatedExamples": [
            {"id": "logger-silent", "path": "examples/logger-silent/main.bang"}
        ],
    }


def validator() -> Draft202012Validator:
    schema = json.loads(SCHEMA_PATH.read_text(encoding="utf-8"))
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema)


def checked_repo_path(path: str) -> Path:
    candidate = (ROOT / path).resolve()
    try:
        candidate.relative_to(ROOT.resolve())
    except ValueError as error:
        raise ValidationError(f"path escapes the repository: {path}") from error
    if not candidate.is_file():
        raise ValidationError(f"repo source path does not exist: {path}")
    return candidate


def validate_fact(fact: dict) -> None:
    validator().validate(fact)
    checked_repo_path(fact["program"]["path"])
    checked_repo_path(fact["expectedOutput"]["path"])
    for evidence in fact["evidence"]:
        for source in evidence["sources"]:
            checked_repo_path(source)
    for related in fact["relatedExamples"]:
        checked_repo_path(related["path"])


def parse_fact(serialized: str) -> dict:
    fact = json.loads(serialized)
    validate_fact(fact)
    return fact


def load_committed_fact() -> dict:
    return parse_fact(FACT_PATH.read_text(encoding="utf-8"))


def render_json(fact: dict) -> str:
    return json.dumps(fact, ensure_ascii=False, indent=2, sort_keys=True) + "\n"


def public_source_link(path: str, label: str | None = None) -> str:
    return f"[`{label or path}`]({PUBLIC_SOURCE_BASE}/{path})"


def render_markdown(fact: dict) -> str:
    program = fact["program"]
    expected = fact["expectedOutput"]
    engines = ", ".join(f"`{engine}`" for engine in fact["supportedEngines"])
    concepts = ", ".join(f"`{concept}`" for concept in fact["concepts"])
    refusal = (
        f"`{fact['refusalClass']}`" if fact.get("refusalClass") is not None else "none"
    )
    lines = [
        "<!-- GENERATED by tools/docfacts_logger.py — do not hand-edit. -->",
        "",
        f"# {fact['title']}",
        "",
        fact["summary"],
        "",
        f"- Supported engines: {engines}",
        f"- Concepts: {concepts}",
        f"- Refusal class: {refusal}",
        "",
        f"Canonical source: {public_source_link(program['path'])}",
        "",
        "```bang",
        program["text"].rstrip("\n"),
        "```",
        "",
        "Expected stdout:",
        "",
        "```text",
        expected["text"].rstrip("\n"),
        "```",
        "",
        "## Evidence",
        "",
        "| label | claim | sources | validating commands |",
        "|---|---|---|---|",
    ]
    for evidence in fact["evidence"]:
        sources = "<br>".join(public_source_link(path) for path in evidence["sources"])
        commands = "<br>".join(f"`{command}`" for command in evidence["commands"])
        lines.append(
            f"| `{evidence['label']}` | {evidence['claim']} | {sources} | {commands} |"
        )
    lines.extend(["", "## Related canonical example", ""])
    for related in fact["relatedExamples"]:
        lines.append(f"- {public_source_link(related['path'], related['id'])}")
    return "\n".join(lines) + "\n"


def write_outputs() -> int:
    expected_fact = build_fact()
    validate_fact(expected_fact)
    FACT_PATH.parent.mkdir(parents=True, exist_ok=True)
    FACT_PATH.write_text(render_json(expected_fact), encoding="utf-8")
    print(f"docfacts-logger: generated {FACT_PATH.relative_to(ROOT)}")

    committed_fact = load_committed_fact()
    MARKDOWN_PATH.parent.mkdir(parents=True, exist_ok=True)
    MARKDOWN_PATH.write_text(render_markdown(committed_fact), encoding="utf-8")
    print(f"docfacts-logger: generated {MARKDOWN_PATH.relative_to(ROOT)}")
    return 0


def expect_invalid(name: str, fact: dict) -> bool:
    try:
        validate_fact(fact)
    except (ValidationError, KeyError):
        print(f"✓ known-bad {name} rejected")
        return True
    print(f"✗ known-bad {name} was accepted", file=sys.stderr)
    return False


def serialization_consumer_pole(base: dict) -> bool:
    serialized_fact = copy.deepcopy(base)
    serialized_fact["title"] = "Serialized consumer pole"
    serialized = render_json(serialized_fact)
    serialized_fact["title"] = "Unserialized mutation"
    markdown = render_markdown(parse_fact(serialized))
    passed = (
        "# Serialized consumer pole" in markdown
        and "# Unserialized mutation" not in markdown
    )
    if passed:
        print("✓ serialized JSON is the Markdown consumer boundary")
    else:
        print("✗ Markdown bypassed the serialized JSON boundary", file=sys.stderr)
    return passed


def self_test() -> int:
    base = build_fact()
    validate_fact(base)
    cases = []

    missing_source = copy.deepcopy(base)
    missing_source["program"]["path"] = "examples/logger-counting/missing.bang"
    cases.append(("missing-canonical-source", missing_source))

    missing_evidence_source = copy.deepcopy(base)
    del missing_evidence_source["evidence"][0]["sources"]
    cases.append(("missing-evidence-sources", missing_evidence_source))

    false_evidence_source = copy.deepcopy(base)
    false_evidence_source["evidence"][0]["sources"] = ["docs/not-a-real-source.md"]
    cases.append(("false-evidence-source", false_evidence_source))

    invalid_label = copy.deepcopy(base)
    invalid_label["evidence"][0]["label"] = "verified"
    cases.append(("invalid-evidence-vocabulary", invalid_label))

    duplicate_engine = copy.deepcopy(base)
    duplicate_engine["supportedEngines"].append("env")
    cases.append(("duplicate-supported-engine", duplicate_engine))

    invalid_concept = copy.deepcopy(base)
    invalid_concept["concepts"] = ["Effect Handlers"]
    cases.append(("invalid-concept-vocabulary", invalid_concept))

    invalid_refusal = copy.deepcopy(base)
    invalid_refusal["refusalClass"] = "Compiled Refusal"
    cases.append(("invalid-refusal-vocabulary", invalid_refusal))

    passed = sum(expect_invalid(name, fact) for name, fact in cases)
    passed += serialization_consumer_pole(base)
    total = len(cases) + 1
    print(f"docfacts-logger self-test: {passed}/{total} poles passed.")
    return 0 if passed == total else 1


def check_outputs() -> int:
    expected_fact = build_fact()
    validate_fact(expected_fact)
    expected_json = render_json(expected_fact)
    stale = []

    if not FACT_PATH.is_file() or FACT_PATH.read_text(encoding="utf-8") != expected_json:
        stale.append(FACT_PATH.relative_to(ROOT))

    try:
        committed_fact = load_committed_fact()
    except (OSError, json.JSONDecodeError, ValidationError, KeyError) as error:
        print(f"docfacts-logger: committed fact is invalid: {error}", file=sys.stderr)
        committed_fact = None

    if committed_fact is not None:
        expected_markdown = render_markdown(committed_fact)
        if (
            not MARKDOWN_PATH.is_file()
            or MARKDOWN_PATH.read_text(encoding="utf-8") != expected_markdown
        ):
            stale.append(MARKDOWN_PATH.relative_to(ROOT))
    elif MARKDOWN_PATH.relative_to(ROOT) not in stale:
        stale.append(MARKDOWN_PATH.relative_to(ROOT))

    self_test_status = self_test()
    if stale:
        for path in stale:
            print(f"docfacts-logger: stale or missing {path}", file=sys.stderr)
        print("run `just docfacts-logger` to regenerate", file=sys.stderr)
    if stale or self_test_status != 0:
        return 1
    print("docfacts-logger: OK — schema-valid JSON and Markdown are current.")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.check:
        return check_outputs()
    if args.self_test:
        return self_test()
    return write_outputs()


if __name__ == "__main__":
    raise SystemExit(main())
