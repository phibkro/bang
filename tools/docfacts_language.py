#!/usr/bin/env python3
# tool: role=gen couples=Bang/Frontend/Surface.lean,Bang/Frontend/DiagCodes.lean,Bang/Frontend/Diagnostics.lean,Prelude.bang,Bang/Frontend/TypeCheck.lean,Main.lean,tools/cli_facts.py,docfacts/schema/language.schema.json,docfacts/schema/common.schema.json,docfacts/language.json runs-in=fitness
"""Generate and validate the serialized language-reference fact bundle."""

import argparse
import copy
import json
import re
import sys
from pathlib import Path

from jsonschema.exceptions import ValidationError

try:
    from cli_facts import CliFactsError, derive_allowed_option_families
    from docfacts_common import schema_validator
except ModuleNotFoundError:
    from tools.cli_facts import CliFactsError, derive_allowed_option_families
    from tools.docfacts_common import schema_validator

ROOT = Path(__file__).resolve().parent.parent
SCHEMA_PATH = ROOT / "docfacts/schema/language.schema.json"
FACT_PATH = ROOT / "docfacts/language.json"
AUTHORITY_PATHS = {
    "surface": "Bang/Frontend/Surface.lean",
    "diagcodes": "Bang/Frontend/DiagCodes.lean",
    "diagnostics": "Bang/Frontend/Diagnostics.lean",
    "prelude": "Prelude.bang",
    "typecheck": "Bang/Frontend/TypeCheck.lean",
    "main": "Main.lean",
}
STANDARD_NAMES = ["concat", "reverse", "eq", "strLength", "intToStr"]
STR = r'"((?:[^"\\]|\\.)*)"'


class FactError(ValueError):
    pass


def _fail(message: str):
    raise FactError(f"docfacts-language: {message}")


def _read_sources(overrides=None):
    overrides = overrides or {}
    return {
        name: overrides.get(path, (ROOT / path).read_text(encoding="utf-8"))
        for name, path in AUTHORITY_PATHS.items()
    }


def _first_sentence(text):
    text = re.sub(r"\s+", " ", text).strip()
    match = re.match(r"(.*?\.)(?:\s|$)", text)
    return (match.group(1) if match else text).strip()


def _lean_strings(text):
    values = []
    for raw in re.findall(STR, text):
        try:
            values.append(json.loads(f'"{raw}"'))
        except json.JSONDecodeError as error:
            _fail(f"unsupported Lean string literal: {error}")
    return values


def _extract_inductive_rows(text, name):
    match = re.search(
        rf"inductive {name} where\n(.*?)(?=\n(?:inductive\s|\s*deriving))", text, re.S
    )
    if not match:
        _fail(f"could not locate `inductive {name} where` body")
    lines = match.group(1).splitlines()
    if name != "Surf":
        rows = []
        for line in lines:
            ctor = re.match(r"\s*\|\s*(\w+)\s*:.*?--\s*(.*)", line)
            if ctor:
                parts = re.split(r"\s{2,}", ctor.group(2).strip(), maxsplit=1)
                rows.append(
                    {
                        "name": ctor.group(1),
                        "form": parts[0],
                        "notes": parts[1].strip() if len(parts) > 1 else "",
                    }
                )
        if not rows:
            _fail(f"`inductive {name}` parsed to no documented rows")
        return rows
    constructors = []
    for index, line in enumerate(lines):
        ctor = re.match(r"\s*\|\s*(\w+)\s*:", line)
        if not ctor:
            continue
        comments = []
        trailing = re.search(r"--\s*(.*)", line)
        if trailing:
            comments.append(trailing.group(1).strip())
        else:
            next_index = index + 1
            while next_index < len(lines):
                following = re.match(r"\s*--\s?(.*)", lines[next_index])
                if not following:
                    break
                comment = following.group(1).strip()
                if comments and (
                    comment.startswith("──") or comment.startswith("arithmetic (")
                ):
                    break
                comments.append(comment)
                next_index += 1
        constructors.append((ctor.group(1), comments))
    if not constructors:
        _fail(f"`inductive {name}` parsed to no constructors")
    undocumented = [ctor for ctor, comments in constructors if not comments]
    if undocumented:
        _fail(f"`inductive {name}` has undocumented constructors: {undocumented}")
    rows = []
    for ctor, comments in constructors:
        quoted_form = re.match(r"(`[^`]+`)(.*)", comments[0])
        if quoted_form:
            form = quoted_form.group(1)[1:-1]
            notes = [quoted_form.group(2).strip()] + comments[1:]
        else:
            parts = re.split(r"\s{2,}|\s+(?:→|—)\s+", comments[0], maxsplit=1)
            form = parts[0]
            notes = ([parts[1]] if len(parts) > 1 else []) + comments[1:]
        rows.append(
            {
                "name": ctor,
                "form": form.strip(),
                "notes": " ".join(note for note in notes if note).strip(),
            }
        )
    documented = {row["name"] for row in rows}
    inventory = {ctor for ctor, _ in constructors}
    if documented != inventory:
        _fail(f"`inductive {name}` documented inventory differs from constructors")
    return rows


def _extract_labels(surface_text, typecheck_text):
    definitions = {}
    for match in re.finditer(
        r"/--(.*?)-/\s*def\s+(\w+Label)\s*:\s*Label\s*:=\s*(\d+)", surface_text, re.S
    ):
        definitions[match.group(2)] = {
            "value": int(match.group(3)),
            "summary": _first_sentence(match.group(1)),
        }
    mapping_match = re.search(
        r"def effNames\b.*?ns\.foldl\s*\(fun acc n =>(.*?)\)\s*∅", typecheck_text, re.S
    )
    if not definitions or not mapping_match:
        _fail("effect-label definition/mapping extraction was empty")
    mappings = re.findall(
        r'n\s*=\s*"([^"]+)"\s*then\s*insert\s+(\w+Label)\s+acc', mapping_match.group(1)
    )
    resolver_match = re.search(
        r"def resolveEffName\b.*?:=\n(.*?)(?=\n\n)", typecheck_text, re.S
    )
    resolver_mappings = re.findall(
        r'n\s*=\s*"([^"]+)"\s*then\s*some\s+(\w+Label)',
        resolver_match.group(1) if resolver_match else "",
    )
    if not mappings or len(mappings) != len(set(mappings)):
        _fail(f"unexpected or duplicate effect-name mappings: {mappings}")
    if mappings != resolver_mappings:
        _fail(
            f"frontend effect-name mappings disagree: effNames={mappings} resolveEffName={resolver_mappings}"
        )
    mapped_labels = {label for _, label in mappings}
    if mapped_labels != set(definitions):
        _fail(
            f"effect-name mapping/label definitions differ: mapping={sorted(mapped_labels)} definitions={sorted(definitions)}"
        )
    return [
        {
            "name": name,
            "value": definitions[label]["value"],
            "summary": definitions[label]["summary"],
        }
        for name, label in mappings
    ]


def _extract_operators(text):
    match = re.search(r"def opInfo.*?\n(.*?)\n\s*\|\s*_\s*=>\s*none", text, re.S)
    if not match:
        _fail("could not locate `def opInfo` table anchor")
    rows = []
    for line in match.group(1).splitlines():
        row = re.match(rf"\s*\|\s*{STR}\s*=>\s*some\s*\(\s*(\d+)\s*,\s*(\d+)\s*,", line)
        if row:
            rows.append(
                {
                    "symbol": json.loads(f'"{row.group(1)}"'),
                    "leftBindingPower": int(row.group(2)),
                    "rightBindingPower": int(row.group(3)),
                }
            )
    if not rows:
        _fail("`opInfo` parsed to no operators")
    return rows


def _extract_keyword_rules(text):
    match = re.search(r"def keywordRule.*?\n(.*?)\n\s*\|\s*_\s*=>\s*none", text, re.S)
    if not match:
        _fail("could not locate `def keywordRule` table anchor")
    slots = {
        "refE": "<expr>",
        "refA": "<atom>",
        "refI": "<ident>",
        "optAs": "[as <ident>]",
    }
    rows = []
    for rule in re.finditer(
        r'\|\s*"([^"]+)"\s*=>\s*some\s*⟨\[(.*?)\]\s*,', match.group(1)
    ):
        parts = []
        for choice in re.finditer(
            r'\.kw\s*"([^"]*)"|\.(refE|refA|refI|optAs)', rule.group(2)
        ):
            parts.append(
                choice.group(1)
                if choice.group(1) is not None
                else slots[choice.group(2)]
            )
        if not parts:
            _fail(f"keyword rule `{rule.group(1)}` parsed to no choices")
        rows.append({"keyword": rule.group(1), "form": " ".join(parts)})
    if not rows:
        _fail("`keywordRule` parsed to no rules")
    return rows


def _extract_reserved_identifiers(text):
    match = re.search(r"def pIdent\b.*?\n(.*?)\n\s*then\b", text, re.S)
    if not match:
        _fail("could not locate `def pIdent` reserved-chain anchor")
    words = re.findall(r't\s*=\s*"([^"]+)"', match.group(1))
    result = []
    for word in words:
        if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", word) and word not in result:
            result.append(word)
    if not result:
        _fail("`pIdent` reserved-chain extraction was empty")
    return result


def _balanced_records(body):
    starts = [match.start() for match in re.finditer(r"\{\s*code\s*:=", body)]
    records = []
    for start in starts:
        depth = 0
        in_string = False
        escaped = False
        for index in range(start, len(body)):
            char = body[index]
            if in_string:
                if escaped:
                    escaped = False
                elif char == "\\":
                    escaped = True
                elif char == '"':
                    in_string = False
            elif char == '"':
                in_string = True
            elif char == "{":
                depth += 1
            elif char == "}":
                depth -= 1
                if depth == 0:
                    records.append(body[start : index + 1])
                    break
        else:
            _fail("unterminated diagnostic registry record")
    return records


def _field_slice(record, field, next_fields):
    start = re.search(rf"\b{re.escape(field)}\s*:=", record)
    if not start:
        _fail(f"diagnostic registry entry missing `{field}`")
    end = len(record)
    for next_field in next_fields:
        found = re.search(rf"\b{re.escape(next_field)}\s*:=", record[start.end() :])
        if found:
            end = min(end, start.end() + found.start())
    return record[start.end() : end]


def _extract_diagnostic_registry(text):
    match = re.search(
        r"def registry\s*:\s*List DiagEntry\s*:=\s*\[(.*?)\n\]", text, re.S
    )
    if not match:
        _fail("could not locate `def registry : List DiagEntry := […]`")
    rows = []
    for record in _balanced_records(match.group(1)):
        code = _lean_strings(_field_slice(record, "code", ["anchors"]))
        anchors = _lean_strings(_field_slice(record, "anchors", ["summary"]))
        summary = _lean_strings(_field_slice(record, "summary", ["teaching"]))
        teaching = _lean_strings(_field_slice(record, "teaching", ["example?"]))
        example_expr = _field_slice(record, "example?", [])
        example_values = _lean_strings(example_expr)
        example = (
            None if re.search(r"\bnone\b", example_expr) else "".join(example_values)
        )
        if len(code) != 1 or not anchors or not summary or not teaching:
            _fail("diagnostic registry entry has an unsupported field shape")
        rows.append(
            {
                "code": code[0],
                "anchors": anchors,
                "summary": "".join(summary),
                "teaching": "".join(teaching),
                "example": example,
            }
        )
    if not rows:
        _fail("diagnostic registry extraction was empty")
    return rows


def _extract_inductive_ctors(text, name):
    match = re.search(rf"inductive {name} where\n(.*?)\n\s*deriving", text, re.S)
    if not match:
        _fail(f"could not locate diagnostic `{name}` inductive")
    rows = re.findall(r"^\s*\|\s*(\w+)\b", match.group(1), re.M)
    if not rows:
        _fail(f"diagnostic `{name}` extraction was empty")
    return rows


def _extract_diagnostic_contract(text):
    structure = re.search(r"structure Diagnostic where\n(.*?)\n\s*deriving", text, re.S)
    to_json = re.search(r"def Diagnostic\.toJson.*?\n(.*?)\n\n", text, re.S)
    if not structure or not to_json:
        _fail("could not locate Diagnostic structure/toJson anchors")
    structure_fields = re.findall(r"^\s*(\w+)\s*:", structure.group(1), re.M)
    if structure_fields != ["severity", "code", "msg", "span"]:
        _fail(f"unexpected Diagnostic fields: {structure_fields}")
    fields = re.findall(r'\\"([^"\\]+)\\"\s*:', to_json.group(1))
    expected = ["severity", "code", "explainCode", "msg", "span"]
    if len(fields) != len(set(fields)):
        _fail(f"duplicate diagnostic JSON fields: {fields}")
    if fields != expected:
        _fail(f"unexpected diagnostic JSON fields: {fields}")
    return {
        "severities": _extract_inductive_ctors(text, "Severity"),
        "stages": _extract_inductive_ctors(text, "DiagCode"),
        "fields": fields,
    }


def _extract_prelude_names(text):
    names = re.findall(r"^pub let(?: rec)?\s+(\w+)", text, re.M)
    if not names:
        _fail("Prelude.bang contains no `pub let` declarations")
    return names


def _extract_prelude_sigs(text):
    match = re.search(r"def preludeSigs\b.*?:=\s*\n\s*\[(.*?)\]\s*\n", text, re.S)
    if not match:
        _fail("could not locate `def preludeSigs` table anchor")
    rows = [
        (name, signature)
        for name, signature in re.findall(
            r'\(\s*"(\w+)"\s*,\s*"([^"]*)"\s*\)', match.group(1)
        )
    ]
    if not rows:
        _fail("`preludeSigs` extraction was empty")
    return rows


def _decode_usage(text):
    match = re.search(r"def usage\s*:\s*String\s*:=\n(.*?)\n\n/-!", text, re.S)
    if not match:
        _fail("could not locate `def usage : String :=` block")
    return "".join(_lean_strings(match.group(1)))


def _command_path(line):
    tokens = line.strip().split()
    if len(tokens) < 2 or tokens[0] != "bang":
        _fail(f"unsupported CLI usage line: {line}")
    first = tokens[1].rstrip(",")
    path = [first]
    if (
        first in {"query", "rewrite"}
        and len(tokens) > 2
        and not tokens[2].startswith("<")
    ):
        path.append(tokens[2])
    elif first == "lint" and len(tokens) > 2 and tokens[2] == "--fix":
        path.append("--fix")
    return path


def _usage_blocks(usage):
    lines = usage.splitlines()
    starts = [
        index for index, line in enumerate(lines) if re.match(r"^(  |    )bang\s", line)
    ]
    blocks = {}
    for position, start in enumerate(starts):
        end = starts[position + 1] if position + 1 < len(starts) else len(lines)
        path = tuple(_command_path(lines[start]))
        blocks[path] = "\n".join(lines[start:end])
    return blocks


def _extract_cli_commands(text, allowed_by_command):
    usage = _decode_usage(text)
    principal_flags = {
        ("run",): [
            "--engine=oracle|compiled|env",
            "--no-typecheck",
            "--fuel",
            "--env=sim|real",
            "--allow",
            "--allow-fs-read",
            "--allow-fs-write",
            "--record",
            "--replay",
            "--max-host-requests",
        ],
        ("eval",): ["--engine=oracle|compiled|env", "--no-typecheck", "--fuel"],
        ("repl",): ["--engine=oracle|compiled|env", "--no-typecheck", "--fuel"],
        ("check",): ["--json"],
        ("emit",): ["-o", "--out="],
        ("build",): ["-o", "--component", "--adapter"],
        ("new",): ["--module"],
        ("rewrite", "fmt"): ["-w"],
        ("rewrite", "rename"): ["-w"],
        ("rewrite", "annotate"): ["-w"],
        ("lint",): ["--json", "--quiet-clean"],
        ("lint", "--fix"): ["--fix", "-w"],
        ("--help",): ["-h"],
        ("--version",): ["-v"],
    }
    blocks = _usage_blocks(usage)
    shared_engine_flags = "\n".join(
        blocks.get((command,), "") for command in ("run", "eval", "repl")
    )
    rows = []
    for line in usage.splitlines():
        if re.match(r"^(  |    )bang\s", line):
            path = _command_path(line)
            flags = principal_flags.get(tuple(path), [])
            block = (
                shared_engine_flags
                if tuple(path) in {("run",), ("eval",), ("repl",)}
                else blocks[tuple(path)]
            )
            for flag in flags:
                if flag not in block:
                    _fail(
                        f"CLI principal flag `{flag}` for `{' '.join(path)}` is absent from its usage block"
                    )
            rows.append(
                {
                    "path": path,
                    "synopsis": line.strip(),
                    "principalFlags": flags,
                    "parserOptionFamilies": list(allowed_by_command.get(path[0], ())),
                }
            )
    if not rows:
        _fail("CLI usage parsed to no documented commands")
    return rows, usage


def _extract_exit_contracts(usage):
    scopes = {
        "EXIT CODES:": "run",
        "EXIT CODES [bang check --json]:": "check --json",
        "EXIT CODES [bang query <op>]:": "query",
    }
    current = None
    rows = []
    for line in usage.splitlines():
        if line in scopes:
            current = scopes[line]
            continue
        if current and line.startswith("EXIT CODES"):
            current = scopes.get(line)
            continue
        if current:
            match = re.match(r"\s+(\d)\s+(.*)", line)
            if match:
                rows.append(
                    {
                        "scope": current,
                        "code": int(match.group(1)),
                        "meaning": match.group(2).strip(),
                    }
                )
            elif not line.strip() or not line.startswith(" "):
                current = None
    if not rows:
        _fail("CLI usage parsed to no exit contracts")
    return rows


def _extract_dispatch(text, command):
    start = text.find(f'else if cmd == "{command}" then')
    if start < 0:
        _fail(f"dispatcher arm missing for `{command}`")
    end = text.find("else if cmd ==", start + 1)
    return text[start : end if end >= 0 else len(text)]


def _validate_cli_agreement(commands, main_text, allowed_by_command):
    paths = {tuple(row["path"]) for row in commands}
    usage_top = {path[0] for path in paths if not path[0].startswith("-")}
    dispatcher_top = set(re.findall(r'else if cmd == "([^"]+)" then', main_text))
    if usage_top != dispatcher_top:
        _fail(
            f"CLI usage/dispatcher mismatch: usage={sorted(usage_top)} dispatcher={sorted(dispatcher_top)}"
        )
    for command in ("query", "rewrite"):
        documented = {
            path[1] for path in paths if len(path) == 2 and path[0] == command
        }
        dispatched = set(
            re.findall(r'\| \["([^"]+)"', _extract_dispatch(main_text, command))
        )
        if documented != dispatched:
            _fail(
                f"CLI {command} usage/dispatcher mismatch: usage={sorted(documented)} dispatcher={sorted(dispatched)}"
            )
    lint_fix = ("lint", "--fix") in paths
    if lint_fix != ("opts.fix" in _extract_dispatch(main_text, "lint")):
        _fail("CLI lint --fix usage/dispatcher mismatch")
    for long, short in (("--help", "-h"), ("--version", "-v")):
        if (long,) not in paths:
            _fail(f"CLI usage missing `{long}`")
        alias_dispatch = re.search(
            rf'cmd == "{re.escape(long)}"\s*\|\|\s*cmd == "{re.escape(short)}"',
            main_text,
        )
        if not alias_dispatch:
            _fail(f"CLI alias dispatch missing `{long}`/`{short}`")

    flag_families = {
        "--engine=oracle|compiled|env": "engine",
        "--no-typecheck": "noTypecheck",
        "--fuel": "fuel",
        "--env=sim|real": "hostEnv",
        "--allow": "allow",
        "--allow-fs-read": "allowFsRead",
        "--allow-fs-write": "allowFsWrite",
        "--record": "record",
        "--replay": "replay",
        "--max-host-requests": "maxHostRequests",
        "--json": "json",
        "-o": "out",
        "--out=": "out",
        "--component": "component",
        "--adapter": "adapter",
        "--module": "moduleFlag",
        "-w": "write",
        "--fix": "fix",
        "--quiet-clean": "quietClean",
    }
    family_anchors = {
        "engine": "opts.selectedEngine",
        "noTypecheck": "!opts.noTypecheck",
        "fuel": "opts.selectedFuel",
        "hostEnv": "opts.hostReal",
        "allow": "opts.allow",
        "allowFsRead": "opts.allowFsRead",
        "allowFsWrite": "opts.allowFsWrite",
        "record": "opts.recordPath",
        "replay": "opts.replayPath",
        "maxHostRequests": "opts.selectedMaxHostRequests",
        "json": "opts.json",
        "out": "opts.outPath",
        "component": "opts.component",
        "adapter": "opts.adapterPath",
        "moduleFlag": "opts.moduleFlag",
        "write": "opts.write",
        "fix": "opts.fix",
        "quietClean": "opts.quietClean",
    }
    aliases = {
        ("--help",): {"-h": 'cmd == "-h"'},
        ("--version",): {"-v": 'cmd == "-v"'},
    }
    documented_families = {command: set() for command in allowed_by_command}
    for row in commands:
        path = tuple(row["path"])
        if path in aliases:
            anchors = aliases[path]
            if set(row["principalFlags"]) != set(anchors):
                _fail(
                    f"CLI principal flag inventory unsupported for `{' '.join(path)}`"
                )
            if row["parserOptionFamilies"]:
                _fail(f"CLI alias `{' '.join(path)}` unexpectedly has parser families")
        else:
            command = path[0]
            if command not in allowed_by_command:
                _fail(f"CLI command `{command}` has no typed parser inventory")
            if tuple(row["parserOptionFamilies"]) != allowed_by_command[command]:
                _fail(f"CLI parser option inventory drift for `{command}`")
            try:
                families = {flag_families[flag] for flag in row["principalFlags"]}
            except KeyError as error:
                _fail(
                    f"CLI principal flag `{error.args[0]}` has no typed option family"
                )
            documented_families[command].update(families)
            anchors = {
                flag: family_anchors[flag_families[flag]]
                for flag in row["principalFlags"]
            }
        block = (
            main_text
            if path[0].startswith("-")
            else _extract_dispatch(main_text, path[0])
        )
        for flag, anchor in anchors.items():
            if anchor not in block:
                _fail(
                    f"CLI principal flag `{flag}` for `{' '.join(path)}` is absent from its dispatcher block"
                )
    for command, allowed in allowed_by_command.items():
        documented = documented_families[command]
        if documented != set(allowed):
            _fail(
                f"CLI typed allow-list/documentation mismatch for `{command}`: "
                f"allowed={list(allowed)} documented={sorted(documented)}"
            )


def _evidence():
    return [
        {
            "id": "surface-generated",
            "label": "generated",
            "claim": "Surface and parser-table facts are extracted from the parser authority and consumed only after JSON reload.",
            "sources": [
                "Bang/Frontend/Surface.lean",
                "tools/docfacts_language.py",
                "docfacts/schema/language.schema.json",
            ],
            "commands": ["python3 tools/docfacts_language.py --check"],
        },
        {
            "id": "diagnostics-implemented",
            "label": "implemented",
            "claim": "The diagnostic JSON contract and stable explain registry are implemented by the frontend authorities.",
            "sources": [
                "Bang/Frontend/Diagnostics.lean",
                "Bang/Frontend/DiagCodes.lean",
            ],
            "commands": ["just test-check-json", "just test-explain"],
        },
        {
            "id": "prelude-generated",
            "label": "generated",
            "claim": "Prelude declaration order and descriptive signatures are joined without duplicating an order field.",
            "sources": [
                "Prelude.bang",
                "Bang/Frontend/TypeCheck.lean",
                "tools/docfacts_language.py",
            ],
            "commands": ["python3 tools/docfacts_language.py --check"],
        },
        {
            "id": "cli-differential-tested",
            "label": "differential-tested",
            "claim": "Documented CLI paths and representative exit contracts agree with the real binary.",
            "sources": [
                "Main.lean",
                "tools/cli_facts.py",
                "tools/docfacts_language.py",
                "tools/test-docfacts-language.sh",
                "tools/test-cli.sh",
                "tools/test-check-json.sh",
                "tools/test-explain.sh",
            ],
            "commands": [
                "just test-docfacts-language",
                "just test-cli",
                "just test-check-json",
                "just test-explain",
            ],
        },
    ]


def build_fact(overrides=None):
    sources = _read_sources(overrides)
    names = _extract_prelude_names(sources["prelude"])
    sig_rows = _extract_prelude_sigs(sources["typecheck"])
    sigs = dict(sig_rows)
    missing_signatures = set(names) - set(sigs)
    if (
        len(sigs) != len(sig_rows)
        or not set(sigs).issubset(names)
        or missing_signatures != {"reverse"}
    ):
        _fail("prelude inventory/signature mismatch")
    try:
        allowed_by_command = derive_allowed_option_families(sources["main"])
    except CliFactsError as error:
        _fail(str(error))
    commands, usage = _extract_cli_commands(sources["main"], allowed_by_command)
    _validate_cli_agreement(commands, sources["main"], allowed_by_command)
    return {
        "schemaVersion": 1,
        "kind": "language",
        "surface": {
            "forms": _extract_inductive_rows(sources["surface"], "Surf"),
            "types": _extract_inductive_rows(sources["surface"], "Ty"),
            "evidence": ["surface-generated"],
        },
        "grammar": {
            "operators": _extract_operators(sources["surface"]),
            "keywordRules": _extract_keyword_rules(sources["surface"]),
            "reservedIdentifiers": _extract_reserved_identifiers(sources["surface"]),
            "effectLabels": _extract_labels(sources["surface"], sources["typecheck"]),
            "evidence": ["surface-generated"],
        },
        "diagnostics": {
            "contract": _extract_diagnostic_contract(sources["diagnostics"]),
            "registry": _extract_diagnostic_registry(sources["diagcodes"]),
            "evidence": ["diagnostics-implemented"],
        },
        "prelude": {
            "standardNames": STANDARD_NAMES,
            "declarations": [
                {"name": name, "signature": sigs.get(name)} for name in names
            ],
            "evidence": ["prelude-generated"],
        },
        "cli": {
            "commands": commands,
            "exitContracts": _extract_exit_contracts(usage),
            "evidence": ["cli-differential-tested"],
        },
        "evidence": _evidence(),
    }


def _checked_repo_path(path):
    candidate = (ROOT / path).resolve()
    try:
        candidate.relative_to(ROOT.resolve())
    except ValueError as error:
        raise ValidationError(f"path escapes repository: {path}") from error
    if not candidate.is_file():
        raise ValidationError(f"evidence source does not exist: {path}")


def _unique(rows, key, family):
    values = [key(row) for row in rows]
    if len(values) != len(set(values)):
        raise ValidationError(f"duplicate {family}: {values}")


def validate_fact(fact):
    schema_validator(SCHEMA_PATH).validate(fact)
    _unique(fact["surface"]["forms"], lambda row: row["name"], "surface form name")
    _unique(fact["surface"]["types"], lambda row: row["name"], "surface type name")
    _unique(fact["grammar"]["operators"], lambda row: row["symbol"], "operator")
    _unique(fact["grammar"]["keywordRules"], lambda row: row["keyword"], "keyword rule")
    _unique(fact["grammar"]["effectLabels"], lambda row: row["name"], "effect label")
    _unique(fact["diagnostics"]["registry"], lambda row: row["code"], "diagnostic code")
    _unique(fact["prelude"]["declarations"], lambda row: row["name"], "prelude name")
    _unique(fact["cli"]["commands"], lambda row: tuple(row["path"]), "CLI path")
    _unique(fact["evidence"], lambda row: row["id"], "evidence id")
    evidence_ids = {row["id"] for row in fact["evidence"]}
    refs = set()
    for family in ("surface", "grammar", "diagnostics", "prelude", "cli"):
        refs.update(fact[family]["evidence"])
    dangling = refs - evidence_ids
    if dangling:
        raise ValidationError(f"dangling evidence references: {sorted(dangling)}")
    for evidence in fact["evidence"]:
        for source in evidence["sources"]:
            _checked_repo_path(source)
    names = [row["name"] for row in fact["prelude"]["declarations"]]
    if not set(fact["prelude"]["standardNames"]).issubset(names):
        raise ValidationError(
            "standard prelude names are not in the declaration inventory"
        )


def render_json(fact):
    return json.dumps(fact, ensure_ascii=False, indent=2, sort_keys=True) + "\n"


def _parse_fact(serialized):
    fact = json.loads(serialized)
    validate_fact(fact)
    return fact


def load_language_fact():
    """Load the committed serialized language fact through schema and semantic validation."""
    return _parse_fact(FACT_PATH.read_text(encoding="utf-8"))


def _expect_invalid(name, fact):
    try:
        validate_fact(fact)
    except (ValidationError, KeyError, TypeError):
        print(f"✓ known-bad {name} rejected")
        return True
    print(f"✗ known-bad {name} was accepted", file=sys.stderr)
    return False


def _expect_build_failure(name, overrides):
    try:
        build_fact(overrides)
    except (FactError, CliFactsError):
        print(f"✓ known-bad {name} rejected")
        return True
    print(f"✗ known-bad {name} was accepted", file=sys.stderr)
    return False


def self_test(base=None, sources=None, base_validated=False):
    if base is None:
        base = build_fact()
    if not base_validated:
        validate_fact(base)
    if sources is None:
        sources = _read_sources()
    cases = []
    missing = copy.deepcopy(base)
    del missing["kind"]
    cases.append(("missing-schema-field", missing))
    extra = copy.deepcopy(base)
    extra["unexpected"] = True
    cases.append(("unexpected-schema-field", extra))
    label = copy.deepcopy(base)
    label["evidence"][0]["label"] = "verified"
    cases.append(("invalid-evidence-label", label))
    no_sources = copy.deepcopy(base)
    no_sources["evidence"][0]["sources"] = []
    cases.append(("missing-evidence-sources", no_sources))
    bad_source = copy.deepcopy(base)
    bad_source["evidence"][0]["sources"] = ["docs/not-real.md"]
    cases.append(("nonexistent-evidence-source", bad_source))
    no_commands = copy.deepcopy(base)
    no_commands["evidence"][0]["commands"] = []
    cases.append(("missing-evidence-commands", no_commands))
    dup_id = copy.deepcopy(base)
    dup_id["evidence"][1]["id"] = dup_id["evidence"][0]["id"]
    cases.append(("duplicate-evidence-id", dup_id))
    dangling = copy.deepcopy(base)
    dangling["surface"]["evidence"] = ["missing-id"]
    cases.append(("dangling-evidence-id", dangling))
    dup_diag = copy.deepcopy(base)
    dup_diag["diagnostics"]["registry"].append(
        copy.deepcopy(dup_diag["diagnostics"]["registry"][0])
    )
    cases.append(("duplicate-diagnostic-code", dup_diag))
    dup_cli = copy.deepcopy(base)
    dup_cli["cli"]["commands"].append(copy.deepcopy(dup_cli["cli"]["commands"][0]))
    cases.append(("duplicate-cli-path", dup_cli))
    passed = sum(_expect_invalid(name, fact) for name, fact in cases)
    build_cases = []
    build_cases.append(
        (
            "missing-source-anchor",
            {
                AUTHORITY_PATHS["surface"]: sources["surface"].replace(
                    "def opInfo", "def changedOpInfo", 1
                )
            },
        )
    )
    empty_ops = re.sub(
        r"(def opInfo.*?\n).*?(\n\s*\|\s*_\s*=>\s*none)",
        r"\1\2",
        sources["surface"],
        count=1,
        flags=re.S,
    )
    build_cases.append(("empty-parser-table", {AUTHORITY_PATHS["surface"]: empty_ops}))
    undocumented = sources["surface"].replace(
        "    -- match s { Left(x) -> e₁ , Right(y) -> e₂ }  → case  (x, y each bind at idx 0)\n",
        "",
        1,
    )
    build_cases.append(
        (
            "multiline-constructor-undocumented",
            {AUTHORITY_PATHS["surface"]: undocumented},
        )
    )
    wrong_effect = sources["typecheck"].replace(
        'if n = "throws" then insert exnLabel acc',
        'if n = "exn" then insert exnLabel acc',
        1,
    )
    build_cases.append(
        ("wrong-surface-effect-mapping", {AUTHORITY_PATHS["typecheck"]: wrong_effect})
    )
    bad_sigs = (
        sources["typecheck"].replace('[ ("concat",', '[ ("ghostPrelude",', 1)
        if '[ ("concat",' in sources["typecheck"]
        else sources["typecheck"].replace('("concat",', '("ghostPrelude",', 1)
    )
    build_cases.append(
        (
            "prelude-inventory-signature-mismatch",
            {AUTHORITY_PATHS["typecheck"]: bad_sigs},
        )
    )
    bad_usage = sources["main"].replace(
        '"  bang fmt  [<file.bang>]', '"  bang format  [<file.bang>]', 1
    )
    build_cases.append(
        ("cli-usage-dispatcher-mismatch", {AUTHORITY_PATHS["main"]: bad_usage})
    )
    bad_flag = sources["main"].replace(
        "else runResolvedProg (!opts.noTypecheck) opts.selectedEngine opts.selectedFuel merged",
        "else runResolvedProg (!opts.noTypecheck) .env opts.selectedFuel merged",
        1,
    )
    build_cases.append(("per-command-flag-drift", {AUTHORITY_PATHS["main"]: bad_flag}))
    run_without_engine = sources["main"].replace(
        "[.engine, .noTypecheck, .fuel, .hostEnv, .allow, .allowFsRead, .allowFsWrite,\n            .record, .replay, .maxHostRequests]",
        "[.noTypecheck, .fuel, .hostEnv, .allow, .allowFsRead, .allowFsWrite,\n            .record, .replay, .maxHostRequests]",
        1,
    )
    build_cases.append(
        (
            "cli-run-allowed-family-removed",
            {AUTHORITY_PATHS["main"]: run_without_engine},
        )
    )
    eval_with_json = sources["main"].replace(
        'parseCliArgs "eval" [.engine, .noTypecheck, .fuel]',
        'parseCliArgs "eval" [.engine, .noTypecheck, .fuel, .json]',
        1,
    )
    build_cases.append(
        (
            "cli-eval-allowed-family-added",
            {AUTHORITY_PATHS["main"]: eval_with_json},
        )
    )
    rewrite_without_write = sources["main"].replace(
        'parseCliArgs "rewrite" [.write]', 'parseCliArgs "rewrite" []', 1
    )
    build_cases.append(
        (
            "cli-rewrite-allowed-family-removed",
            {AUTHORITY_PATHS["main"]: rewrite_without_write},
        )
    )
    bad_alias = sources["main"].replace(
        'cmd == "--help" || cmd == "-h"', 'cmd == "--help"', 1
    )
    build_cases.append(("cli-alias-drift", {AUTHORITY_PATHS["main"]: bad_alias}))
    bad_lint = sources["main"].replace("if opts.fix then", "if false then", 1)
    build_cases.append(("cli-lint-fix-drift", {AUTHORITY_PATHS["main"]: bad_lint}))
    additive_key = sources["diagnostics"].replace(
        '  ",\\"msg\\":" ++ jsonStr d.msg',
        '  ",\\"detail\\":null,\\"msg\\":" ++ jsonStr d.msg',
        1,
    )
    build_cases.append(
        ("additive-diagnostic-json-key", {AUTHORITY_PATHS["diagnostics"]: additive_key})
    )
    duplicate_key = sources["diagnostics"].replace(
        '  ",\\"msg\\":" ++ jsonStr d.msg',
        '  ",\\"code\\":null,\\"msg\\":" ++ jsonStr d.msg',
        1,
    )
    build_cases.append(
        (
            "duplicate-diagnostic-json-key",
            {AUTHORITY_PATHS["diagnostics"]: duplicate_key},
        )
    )
    passed += sum(
        _expect_build_failure(name, overrides) for name, overrides in build_cases
    )
    consumer_source = copy.deepcopy(base)
    serialized = render_json(consumer_source)
    consumer_source["kind"] = "mutated"
    isolated = _parse_fact(serialized)["kind"] == "language"
    print(
        "✓ serialized consumer isolation"
        if isolated
        else "✗ serialized consumer isolation",
        file=sys.stdout if isolated else sys.stderr,
    )
    passed += isolated
    total = len(cases) + len(build_cases) + 1
    print(f"docfacts-language self-test: {passed}/{total} poles passed.")
    return 0 if passed == total else 1


def write_fact():
    fact = build_fact()
    validate_fact(fact)
    FACT_PATH.parent.mkdir(parents=True, exist_ok=True)
    FACT_PATH.write_text(render_json(fact), encoding="utf-8")
    load_language_fact()
    print(f"docfacts-language: generated {FACT_PATH.relative_to(ROOT)}")
    return 0


def check_fact():
    sources = _read_sources()
    overrides = {AUTHORITY_PATHS[name]: text for name, text in sources.items()}
    expected_fact = build_fact(overrides)
    validate_fact(expected_fact)
    expected = render_json(expected_fact)
    stale = not FACT_PATH.is_file() or FACT_PATH.read_text(encoding="utf-8") != expected
    try:
        load_language_fact()
    except (OSError, json.JSONDecodeError, ValidationError, KeyError) as error:
        print(f"docfacts-language: committed fact is invalid: {error}", file=sys.stderr)
        stale = True
    self_test_status = self_test(expected_fact, sources, base_validated=True)
    if stale:
        print(
            "docfacts-language: stale or missing docfacts/language.json",
            file=sys.stderr,
        )
        print("run `just docfacts-language` to regenerate", file=sys.stderr)
    if stale or self_test_status:
        return 1
    print("docfacts-language: OK — schema-valid serialized facts are current.")
    return 0


def main():
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.check:
        return check_fact()
    if args.self_test:
        return self_test()
    return write_fact()


if __name__ == "__main__":
    raise SystemExit(main())
