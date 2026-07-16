#!/usr/bin/env python3
# tool: role=check couples=Main.lean,lean-toolchain,lakefile.toml,docfacts/lean-warning-budget.json,justfile runs-in=verify
"""Keep Lean warnings on a ratchet without making historical warnings fatal.

The normal ``build`` action runs ``lake build Bang bang`` exactly once, covering
the complete project library and native runner while copying output bytes to
their original streams. It then compares the replayed Lean diagnostics with the
committed budget. Lake replays diagnostics on cached builds, so the same path
works for both cold and warm verification.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import signal
import subprocess
import sys
import tempfile
import threading
from collections import Counter
from pathlib import Path
from typing import Any, BinaryIO


ROOT = Path(__file__).resolve().parent.parent
DEFAULT_BASELINE = ROOT / "docfacts" / "lean-warning-budget.json"
SCHEMA_VERSION = 1
CLASSIFIER_VERSION = 2

ANSI_RE = re.compile(rb"\x1b\[[0-?]*[ -/]*[@-~]")
WARNING_RE = re.compile(
    r"^warning: (?P<path>[^:\n]+\.lean):(?P<line>\d+):(?P<column>\d+): (?P<message>.*)$"
)
POSSIBLE_WARNING_PATH_RE = re.compile(r"^warning: (?P<path>[^:\s]+\.lean)(?::|\s)")
HEADERLESS_WARNING_RE = re.compile(r"^warning:\s*(?P<message>.*)$")
LEAN_VERSION_RE = re.compile(
    r"^Lean \(version (?P<version>[^,()\s]+), (?P<host>[^,()]+), "
    r"commit (?P<commit>[0-9A-Fa-f]+), (?P<build>[^,()]+)\)$"
)
CATEGORY_MARKERS = {
    "unusedSimpArgs": "This simp argument is unused:",
    "unusedSectionVars": "automatically included section variable(s) unused",
    "unreachableTactic": "this tactic is never executed",
    "unusedTactic": "tactic does nothing",
    "declarationUsesSorry": "declaration uses `sorry`",
    "unusedVariables": "unused variable `",
    "unusedNames": "unused name:",
    "unnecessarySimpa": "Try `simp at",
    "unnecessarySeqFocus": "Used `tac1 <;> tac2`",
    "deprecated": "has been deprecated",
}
KNOWN_CATEGORIES = frozenset(CATEGORY_MARKERS)


class WarningBudgetError(Exception):
    """A malformed budget or unclassifiable diagnostic."""


def category_for(message: str) -> str | None:
    """Map line-number-free warning text to a stable, reviewable category."""
    for category, marker in CATEGORY_MARKERS.items():
        if marker in message:
            return category
    return None


def project_module(path_text: str) -> str | None:
    """Return a project module name, excluding dependency diagnostics."""
    path = path_text.replace("\\", "/")
    # Lean normally prints paths relative to the package root.  Also accept an
    # absolute checkout path while deliberately excluding .lake/packages.
    if "/.lake/packages/" in f"/{path}":
        return None
    root_prefix = f"{ROOT.as_posix()}/"
    if path.startswith(root_prefix):
        path = path[len(root_prefix) :]
    if "/Bang/" in path:
        path = "Bang/" + path.split("/Bang/", 1)[1]
    elif "/tools/" in path:
        path = "tools/" + path.split("/tools/", 1)[1]
    elif path.startswith("Bang/") or path.startswith("tools/"):
        pass
    elif "/" not in path:
        pass
    else:
        return None
    if not path.endswith(".lean"):
        return None
    return path[:-5].replace("/", ".")


def parse_warnings(raw: bytes) -> tuple[Counter[tuple[str, str]], list[str]]:
    """Normalize display noise and aggregate module/category warning buckets."""
    normalized = (
        ANSI_RE.sub(b"", raw).replace(b"\r", b"\n").decode("utf-8", errors="replace")
    )
    buckets: Counter[tuple[str, str]] = Counter()
    unknown: list[str] = []
    for line in normalized.splitlines():
        match = WARNING_RE.match(line)
        if not match:
            possible = POSSIBLE_WARNING_PATH_RE.match(line)
            if possible and project_module(possible.group("path")) is not None:
                unknown.append(f"malformed project diagnostic header: {line}")
                continue
            # Without a source location, a warning cannot be established as a
            # project diagnostic or safely excluded as dependency output.
            # Properly located dependency diagnostics remain excluded above via
            # project_module(); every ambiguous locationless form fails closed.
            headerless = HEADERLESS_WARNING_RE.match(line)
            if headerless:
                unknown.append(f"locationless warning cannot be attributed: {line}")
            continue
        module = project_module(match.group("path"))
        if module is None:
            continue
        message = match.group("message")
        category = category_for(message)
        if category is None:
            unknown.append(f"{module}: {message}")
            continue
        buckets[(module, category)] += 1
    return buckets, sorted(unknown)


def reject_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise WarningBudgetError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def lean_release_identity(version_output: str) -> dict[str, str]:
    """Drop the host triple while retaining compiler release provenance."""
    normalized = " ".join(version_output.split())
    match = LEAN_VERSION_RE.fullmatch(normalized)
    if match is None:
        raise WarningBudgetError(
            f"unrecognized `lean --version` output: {normalized!r}"
        )
    return {
        "leanVersion": match.group("version"),
        "leanCommit": match.group("commit").lower(),
        "leanBuild": match.group("build").strip(),
    }


def toolchain_identity() -> dict[str, str]:
    toolchain_path = ROOT / "lean-toolchain"
    try:
        toolchain = toolchain_path.read_text(encoding="utf-8").strip()
    except OSError as error:
        raise WarningBudgetError(f"cannot read {toolchain_path}: {error}") from error
    try:
        result = subprocess.run(
            ["lean", "--version"], cwd=ROOT, check=True, capture_output=True, text=True
        )
    except (OSError, subprocess.CalledProcessError) as error:
        raise WarningBudgetError(f"cannot determine Lean version: {error}") from error
    if not toolchain or not result.stdout.strip():
        raise WarningBudgetError("Lean toolchain identity must not be empty")
    return {"leanToolchain": toolchain, **lean_release_identity(result.stdout)}


def baseline_document(
    buckets: Counter[tuple[str, str]], identity: dict[str, str]
) -> dict[str, Any]:
    entries = [
        {"module": module, "category": category, "count": count}
        for (module, category), count in sorted(buckets.items())
        if count > 0
    ]
    return {
        "schemaVersion": SCHEMA_VERSION,
        "classifierVersion": CLASSIFIER_VERSION,
        "toolchain": identity,
        "zeroWarningTarget": True,
        "totalWarnings": sum(item["count"] for item in entries),
        "buckets": entries,
    }


def canonical_bytes(document: dict[str, Any]) -> bytes:
    return (json.dumps(document, indent=2, ensure_ascii=False) + "\n").encode("utf-8")


def load_baseline(path: Path, identity: dict[str, str]) -> Counter[tuple[str, str]]:
    try:
        text = path.read_text(encoding="utf-8")
        document = json.loads(text, object_pairs_hook=reject_duplicate_keys)
    except (OSError, UnicodeError, json.JSONDecodeError, WarningBudgetError) as error:
        raise WarningBudgetError(
            f"malformed warning baseline {path}: {error}"
        ) from error
    if not isinstance(document, dict):
        raise WarningBudgetError("warning baseline root must be an object")
    expected_top = {
        "schemaVersion",
        "classifierVersion",
        "toolchain",
        "zeroWarningTarget",
        "totalWarnings",
        "buckets",
    }
    if set(document) != expected_top:
        raise WarningBudgetError(
            f"warning baseline fields must be exactly {sorted(expected_top)}"
        )
    if document["schemaVersion"] != SCHEMA_VERSION:
        raise WarningBudgetError(
            f"schemaVersion must be {SCHEMA_VERSION}, got {document['schemaVersion']!r}"
        )
    if document["classifierVersion"] != CLASSIFIER_VERSION:
        raise WarningBudgetError(
            "classifierVersion mismatch; regenerate only after reviewing classifier changes"
        )
    if document["toolchain"] != identity:
        raise WarningBudgetError(
            "Lean toolchain mismatch: baseline was generated for "
            f"{document['toolchain']!r}, current toolchain is {identity!r}"
        )
    if document["zeroWarningTarget"] is not True:
        raise WarningBudgetError("zeroWarningTarget must remain true")
    if not isinstance(document["totalWarnings"], int) or isinstance(
        document["totalWarnings"], bool
    ):
        raise WarningBudgetError("totalWarnings must be an integer")
    entries = document["buckets"]
    if not isinstance(entries, list):
        raise WarningBudgetError("buckets must be a list")

    buckets: Counter[tuple[str, str]] = Counter()
    seen: set[tuple[str, str]] = set()
    order: list[tuple[str, str]] = []
    for index, entry in enumerate(entries):
        if not isinstance(entry, dict) or set(entry) != {"module", "category", "count"}:
            raise WarningBudgetError(f"bucket {index} has invalid fields")
        module, category, count = entry["module"], entry["category"], entry["count"]
        if not isinstance(module, str) or not module:
            raise WarningBudgetError(f"bucket {index} has invalid module")
        if not isinstance(category, str) or not category:
            raise WarningBudgetError(f"bucket {index} has invalid category")
        if category not in KNOWN_CATEGORIES:
            raise WarningBudgetError(
                f"bucket {index} has unknown category {category!r}; "
                "review and version the classifier"
            )
        if not isinstance(count, int) or isinstance(count, bool) or count <= 0:
            raise WarningBudgetError(f"bucket {index} count must be a positive integer")
        key = (module, category)
        if key in seen:
            raise WarningBudgetError(f"duplicate warning bucket: {module}/{category}")
        seen.add(key)
        order.append(key)
        buckets[key] = count
    if order != sorted(order):
        raise WarningBudgetError("warning buckets are not in canonical sorted order")
    if sum(buckets.values()) != document["totalWarnings"]:
        raise WarningBudgetError("totalWarnings does not equal the bucket sum")
    if canonical_bytes(document) != text.encode("utf-8"):
        raise WarningBudgetError(
            "warning baseline is not canonical JSON; regenerate it"
        )
    return buckets


def atomic_write(path: Path, content: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary: str | None = None
    try:
        with tempfile.NamedTemporaryFile(
            mode="wb", dir=path.parent, prefix=f".{path.name}.", delete=False
        ) as handle:
            temporary = handle.name
            handle.write(content)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
        temporary = None
    finally:
        if temporary is not None:
            try:
                os.unlink(temporary)
            except FileNotFoundError:
                pass


def pump(source: BinaryIO, sink: BinaryIO, chunks: list[bytes]) -> None:
    while True:
        chunk = source.read(65536)
        if not chunk:
            break
        chunks.append(chunk)
        sink.write(chunk)
        sink.flush()


def run_command(command: list[str]) -> tuple[int, bytes]:
    """Run once, preserving every stdout/stderr byte on its original stream."""
    process = subprocess.Popen(
        command, cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE
    )
    assert process.stdout is not None and process.stderr is not None
    stdout_chunks: list[bytes] = []
    stderr_chunks: list[bytes] = []
    threads = [
        threading.Thread(
            target=pump,
            args=(process.stdout, sys.stdout.buffer, stdout_chunks),
            daemon=True,
        ),
        threading.Thread(
            target=pump,
            args=(process.stderr, sys.stderr.buffer, stderr_chunks),
            daemon=True,
        ),
    ]
    for thread in threads:
        thread.start()
    status = process.wait()
    for thread in threads:
        thread.join()
    return status, b"".join(stdout_chunks) + b"\n" + b"".join(stderr_chunks)


def propagate_status(status: int) -> int:
    if status < 0:
        signum = -status
        # SIGKILL and SIGSTOP cannot have handlers.  Calling signal.signal for
        # either raises before the wrapper can reproduce the child's status.
        uncatchable = {
            candidate
            for name in ("SIGKILL", "SIGSTOP")
            if (candidate := getattr(signal, name, None)) is not None
        }
        if signum not in uncatchable:
            try:
                signal.signal(signum, signal.SIG_DFL)
            except (OSError, RuntimeError, ValueError):
                # If handler restoration is unavailable, the conventional
                # status below is still preferable to a wrapper traceback.
                pass
        try:
            os.kill(os.getpid(), signum)
        except OSError:
            return 128 + signum
        # A non-default inherited handler could return despite the reset
        # attempt. Preserve the conventional shell status in that rare case.
        return 128 + signum
    return status


def compare_budget(
    actual: Counter[tuple[str, str]], baseline: Counter[tuple[str, str]]
) -> list[str]:
    failures: list[str] = []
    baseline_modules = {module for module, _ in baseline}
    baseline_categories = {category for _, category in baseline}
    for (module, category), count in sorted(actual.items()):
        expected = baseline.get((module, category))
        if module not in baseline_modules:
            failures.append(f"new module {module}: {category}={count}")
        elif category not in baseline_categories:
            failures.append(f"new category {category}: {module}={count}")
        elif expected is None:
            failures.append(f"new bucket {module}/{category}: {count}")
        elif count > expected:
            failures.append(
                f"count increase {module}/{category}: {expected} -> {count}"
            )
    return failures


def read_input(path_text: str) -> bytes:
    if path_text == "-":
        return sys.stdin.buffer.read()
    try:
        return Path(path_text).read_bytes()
    except OSError as error:
        raise WarningBudgetError(
            f"cannot read diagnostic input {path_text}: {error}"
        ) from error


def report_unknown(unknown: list[str]) -> None:
    print(
        "FAIL: unclassified project Lean warning shape(s); review and version the classifier:",
        file=sys.stderr,
    )
    for item in unknown:
        print(f"    {item}", file=sys.stderr)


DEFAULT_BUILD_COMMAND = ["lake", "build", "Bang", "bang"]


def command_from(args: argparse.Namespace) -> list[str]:
    return args.command if args.command else DEFAULT_BUILD_COMMAND


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "action",
        choices=("build", "check", "update"),
        help="gate a build/log or regenerate",
    )
    parser.add_argument("--baseline", type=Path, default=DEFAULT_BASELINE)
    parser.add_argument(
        "--input", default="-", help="diagnostic log for the check action"
    )
    parser.add_argument(
        "--command",
        nargs=argparse.REMAINDER,
        help=f"build command (default: {' '.join(DEFAULT_BUILD_COMMAND)})",
    )
    args = parser.parse_args()

    try:
        identity = toolchain_identity()
        if args.action == "check":
            raw = read_input(args.input)
        else:
            status, raw = run_command(command_from(args))
            if status != 0:
                return propagate_status(status)
        actual, unknown = parse_warnings(raw)
        if unknown:
            report_unknown(unknown)
            return 1

        if args.action == "update":
            document = baseline_document(actual, identity)
            atomic_write(args.baseline, canonical_bytes(document))
            print(
                f"lean-warning-budget: wrote {sum(actual.values())} warnings in "
                f"{len(actual)} buckets to {args.baseline}",
                file=sys.stderr,
            )
            return 0

        baseline = load_baseline(args.baseline, identity)
        failures = compare_budget(actual, baseline)
        if failures:
            print("FAIL: Lean warning budget regressed:", file=sys.stderr)
            for failure in failures:
                print(f"    {failure}", file=sys.stderr)
            print(
                "Fix the warnings; do not raise the budget without explicit review.",
                file=sys.stderr,
            )
            return 1
        reduction = sum(baseline.values()) - sum(actual.values())
        suffix = f" ({reduction} below the committed ceiling)" if reduction else ""
        print(
            f"lean-warning-budget: OK — {sum(actual.values())} warnings in "
            f"{len(actual)} buckets{suffix}; target remains zero.",
            file=sys.stderr,
        )
        return 0
    except WarningBudgetError as error:
        print(f"FAIL: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
