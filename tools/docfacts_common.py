#!/usr/bin/env python3
# tool: role=lib couples=docfacts/schema/*.schema.json,docfacts/**/*.json runs-in=fitness
"""Shared schema, repository-path, and serialization checks for documentation facts."""

from __future__ import annotations

import copy
import json
import shlex
from collections.abc import Callable, Iterable
from pathlib import Path
from typing import Any

from jsonschema import Draft202012Validator
from jsonschema.exceptions import ValidationError
from referencing import Registry, Resource


def schema_registry(schema_dir: Path) -> Registry:
    registry = Registry()
    for path in sorted(schema_dir.glob("*.schema.json")):
        schema = json.loads(path.read_text(encoding="utf-8"))
        Draft202012Validator.check_schema(schema)
        resource = Resource.from_contents(schema)
        registry = registry.with_resource(schema["$id"], resource)
    return registry


def schema_validator(schema_path: Path) -> Draft202012Validator:
    schema = json.loads(schema_path.read_text(encoding="utf-8"))
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(
        schema,
        registry=schema_registry(schema_path.parent),
    )


def render_json(value: Any) -> str:
    return json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n"


def reload_and_validate(
    serialized: str,
    validator: Draft202012Validator,
    checks: Iterable[Callable[[dict], None]] = (),
) -> dict:
    fact = json.loads(serialized)
    validator.validate(fact)
    for check in checks:
        check(fact)
    return fact


def checked_repo_path(root: Path, path: str) -> Path:
    root = root.resolve()
    candidate = (root / path).resolve()
    try:
        candidate.relative_to(root)
    except ValueError as error:
        raise ValidationError(f"path escapes the repository: {path}") from error
    if not candidate.is_file():
        raise ValidationError(f"repo source path does not exist: {path}")
    return candidate


def check_evidence_sources(root: Path, evidence: Iterable[dict]) -> None:
    for record in evidence:
        for source in record["sources"]:
            checked_repo_path(root, source)


def reject_duplicate_ids(records: Iterable[dict], description: str = "records") -> None:
    seen: set[str] = set()
    for record in records:
        record_id = record.get("id")
        if record_id is None:
            continue
        if record_id in seen:
            raise ValidationError(f"duplicate {description} id: {record_id}")
        seen.add(record_id)


def check_sorted_unique(
    values: list, key: Callable[[Any], Any], description: str
) -> None:
    keys = [key(value) for value in values]
    if keys != sorted(keys) or len(keys) != len(set(keys)):
        raise ValidationError(
            f"{description} must be uniquely and deterministically sorted"
        )


def validate_evidence_commands(root: Path, evidence: Iterable[dict]) -> None:
    for record in evidence:
        for command in record["commands"]:
            tokens = shlex.split(command)
            if not tokens:
                raise ValidationError(f"empty evidence command in {record['id']}")
            if tokens[0] in {"bash", "python3"}:
                if len(tokens) < 2 or not tokens[1].startswith("tools/"):
                    raise ValidationError(f"unsupported evidence command: {command}")
                checked_repo_path(root, tokens[1])
            elif tokens[:3] == ["lake", "env", "lean"] and len(tokens) == 4:
                checked_repo_path(root, tokens[3])
            elif tokens[:2] == ["lake", "build"] and len(tokens) == 3:
                checked_repo_path(root, tokens[2].replace(".", "/") + ".lean")
            else:
                raise ValidationError(f"unsupported evidence command: {command}")


def serialization_consumer_pole(
    base: dict,
    parse_serialized: Callable[[str], dict],
    render_consumer: Callable[[dict], str],
    field: str = "title",
) -> bool:
    serialized_fact = copy.deepcopy(base)
    serialized_fact[field] = "Serialized consumer pole"
    serialized = render_json(serialized_fact)
    serialized_fact[field] = "Unserialized mutation"
    rendered = render_consumer(parse_serialized(serialized))
    return (
        "Serialized consumer pole" in rendered
        and "Unserialized mutation" not in rendered
    )
