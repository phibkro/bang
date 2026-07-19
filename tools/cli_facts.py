#!/usr/bin/env python3
# tool: role=lib couples=Main.lean runs-in=fitness
"""Structural facts for the typed command-scoped CLI parser."""

from __future__ import annotations

import re
from pathlib import Path

INTERNAL_TOP_LEVEL_COMMANDS = frozenset({"internal"})


class CliFactsError(ValueError):
    """The CLI authority no longer has one unambiguous typed parser shape."""


def _one(text: str, pattern: str, description: str) -> re.Match[str]:
    matches = list(re.finditer(pattern, text, re.MULTILINE | re.DOTALL))
    if len(matches) != 1:
        raise CliFactsError(f"cannot derive one {description}: found {len(matches)}")
    return matches[0]


def derive_allowed_option_families(main_source: str) -> dict[str, tuple[str, ...]]:
    """Return each ordinary top-level command's exact `parseCliArgs` allow-list."""
    kind_block = _one(
        main_source,
        r"inductive CliFlagKind where(?P<body>.*?)(?=\n\s*deriving\s+DecidableEq)",
        "CliFlagKind declaration",
    ).group("body")
    kinds = tuple(re.findall(r"\|\s*([A-Za-z_]\w*)", kind_block))
    if not kinds or len(kinds) != len(set(kinds)):
        raise CliFactsError(f"invalid CliFlagKind inventory: {kinds}")

    main_block = _one(
        main_source,
        r"def main \(args : List String\) : IO UInt32 := do\n(?P<body>.*)\Z",
        "main dispatcher",
    ).group("body")
    calls = list(
        re.finditer(
            r'match\s+parseCliArgs\s+"(?P<command>[^"]+)"\s+'
            r"(?P<allowed>\[[^\]]*\])\s+rest\s+with",
            main_block,
            re.MULTILINE | re.DOTALL,
        )
    )
    inventories: dict[str, tuple[str, ...]] = {}
    for call in calls:
        command = call.group("command")
        if command in inventories:
            raise CliFactsError(f"duplicate parseCliArgs call for {command}")
        allowed = tuple(re.findall(r"\.([A-Za-z_]\w*)", call.group("allowed")))
        if len(allowed) != len(set(allowed)):
            raise CliFactsError(
                f"duplicate allowed option family for {command}: {allowed}"
            )
        unknown = set(allowed) - set(kinds)
        if unknown:
            raise CliFactsError(
                f"unknown allowed option families for {command}: {sorted(unknown)}"
            )
        inventories[command] = allowed

    dispatched = set(re.findall(r'else if cmd == "([^"]+)" then', main_block))
    expected = dispatched - {"--help", "--version"} - INTERNAL_TOP_LEVEL_COMMANDS
    if set(inventories) != expected:
        raise CliFactsError(
            "typed parser/dispatcher command mismatch: "
            f"parser={sorted(inventories)} dispatcher={sorted(expected)}"
        )
    return inventories


def derive_allowed_option_families_from_path(
    main_path: Path,
) -> dict[str, tuple[str, ...]]:
    try:
        source = main_path.read_text(encoding="utf-8")
    except FileNotFoundError as error:
        raise CliFactsError(f"missing CLI authority: {main_path}") from error
    return derive_allowed_option_families(source)
