#!/usr/bin/env python3
# tool: role=analysis couples=tools/module-impact.py,Bang/Frontend/Query.lean,Main.lean runs-in=manual
"""Compare two BANG dump files without pretending that an artifact can be reused.

The view compares complete checked module-interface exports, uses ``module-impact.py`` for the
validated reverse-dependency closure, and reports type/shape recheck candidates. It never skips a
compiler phase: current interface facts are neither cache-key-safe nor separate-compilation-ready.

Exit status 2 is a successful comparison whose complete invalidation decision is indeterminate.
Today that fires when declaration-law evidence moves outside the module-interface records: dump v1
does not carry a module-owned public-law contract fingerprint.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from collections.abc import Mapping
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MODULE_IMPACT = ROOT / "tools" / "module-impact.py"


class DiffError(ValueError):
    """The two dumps cannot support this comparison."""


def require_string(row: Mapping, key: str, context: str) -> str:
    value = row.get(key)
    if not isinstance(value, str) or not value:
        raise DiffError(f"{context} requires a non-empty string {key!r}")
    return value


def load_dump(path: Path) -> object:
    try:
        with path.open(encoding="utf-8") as stream:
            return json.load(stream)
    except OSError as error:
        raise DiffError(f"cannot read {path}: {error}") from error
    except json.JSONDecodeError as error:
        raise DiffError(f"{path} is not valid JSON: {error}") from error


def impact(document: object, label: str) -> dict:
    process = subprocess.run(
        [sys.executable, str(MODULE_IMPACT)],
        cwd=ROOT,
        input=json.dumps(document, separators=(",", ":")),
        text=True,
        capture_output=True,
        check=False,
    )
    if process.returncode != 0:
        detail = process.stderr.strip().removeprefix("module-impact: ")
        raise DiffError(f"{label}: {detail or 'module topology is invalid'}")
    try:
        result = json.loads(process.stdout)
    except json.JSONDecodeError as error:
        raise DiffError(f"{label}: module-impact returned invalid JSON") from error
    if not isinstance(result, dict):
        raise DiffError(f"{label}: module-impact returned a non-object")
    return result


def topology_key(
    document: object, label: str
) -> tuple[tuple[str, ...], tuple[tuple[str, str], ...]]:
    if not isinstance(document, Mapping):
        raise DiffError(f"{label}: dump must be a JSON object")
    modules = document.get("modules")
    edges = document.get("moduleDeps")
    if not isinstance(modules, list) or not isinstance(edges, list):
        raise DiffError(f"{label}: dump requires modules and moduleDeps arrays")
    names = tuple(
        require_string(row, "name", f"{label}: modules[{index}]")
        for index, row in enumerate(modules)
        if isinstance(row, Mapping)
    )
    if len(names) != len(modules):
        raise DiffError(f"{label}: every modules row must be an object")
    pairs = []
    for index, row in enumerate(edges):
        if not isinstance(row, Mapping):
            raise DiffError(f"{label}: moduleDeps[{index}] must be an object")
        pairs.append(
            (
                require_string(row, "from", f"{label}: moduleDeps[{index}]"),
                require_string(row, "to", f"{label}: moduleDeps[{index}]"),
            )
        )
    return names, tuple(sorted(pairs))


def export_projection(row: Mapping, context: str) -> dict:
    projected = {
        "id": require_string(row, "id", context),
        "name": require_string(row, "name", context),
        "kind": require_string(row, "kind", context),
    }
    for key in ("type", "row", "typeError"):
        value = row.get(key)
        if value is not None and not isinstance(value, str):
            raise DiffError(f"{context} field {key!r} must be a string or null")
        projected[key] = value
    shape = row.get("shape")
    if shape is not None and not isinstance(shape, Mapping):
        raise DiffError(f"{context} field 'shape' must be an object or null")
    projected["shape"] = shape
    return projected


def interfaces(document: object, names: tuple[str, ...], label: str) -> dict[str, dict]:
    if not isinstance(document, Mapping):
        raise DiffError(f"{label}: dump must be a JSON object")
    rows = document.get("moduleInterfaces")
    if rows is None:
        raise DiffError(
            f"{label}: moduleInterfaces is null; the checked subject is invalid"
        )
    if not isinstance(rows, list):
        raise DiffError(f"{label}: moduleInterfaces must be an array or null")
    result = {}
    for index, row in enumerate(rows):
        context = f"{label}: moduleInterfaces[{index}]"
        if not isinstance(row, Mapping):
            raise DiffError(f"{context} must be an object")
        module = require_string(row, "module", context)
        if module in result:
            raise DiffError(f"{label}: duplicate module interface {module!r}")
        exports = row.get("exports")
        if not isinstance(exports, list):
            raise DiffError(f"{context} requires an exports array")
        projected_exports = []
        for export_index, export in enumerate(exports):
            if not isinstance(export, Mapping):
                raise DiffError(f"{context}.exports[{export_index}] must be an object")
            projected_exports.append(
                export_projection(export, f"{context}.exports[{export_index}]")
            )
        for key in ("cacheKeySafe", "separateCompilationReady"):
            if type(row.get(key)) is not bool:
                raise DiffError(f"{context} requires a boolean {key!r}")
        result[module] = {
            "scope": require_string(row, "scope", context),
            "algorithm": require_string(row, "algorithm", context),
            "digest": require_string(row, "digest", context),
            "cacheKeySafe": row["cacheKeySafe"],
            "separateCompilationReady": row["separateCompilationReady"],
            "exports": projected_exports,
        }
    if set(result) != set(names):
        raise DiffError(
            f"{label}: moduleInterfaces must cover the modules table exactly"
        )
    return result


def law_projection(document: object, label: str) -> tuple[str, ...]:
    if not isinstance(document, Mapping):
        raise DiffError(f"{label}: dump must be a JSON object")
    rows = document.get("laws")
    if not isinstance(rows, list):
        raise DiffError(f"{label}: dump requires a laws array")
    projected = []
    for index, row in enumerate(rows):
        context = f"{label}: laws[{index}]"
        if not isinstance(row, Mapping):
            raise DiffError(f"{context} must be an object")
        realization = row.get("realization")
        if realization is not None and not isinstance(realization, str):
            raise DiffError(f"{context} field 'realization' must be a string or null")
        params = row.get("params")
        if not isinstance(params, list) or not all(
            isinstance(value, str) for value in params
        ):
            raise DiffError(f"{context} field 'params' must be an array of strings")
        fact = {
            "trait": require_string(row, "trait", context),
            "contract": require_string(row, "contract", context),
            "realization": realization,
            "law": require_string(row, "law", context),
            "params": params,
            "body": require_string(row, "body", context),
        }
        projected.append(json.dumps(fact, sort_keys=True, separators=(",", ":")))
    return tuple(sorted(projected))


def affected_map(result: Mapping, label: str) -> dict[str, list[str]]:
    rows = result.get("impacts")
    if not isinstance(rows, list):
        raise DiffError(f"{label}: module-impact result requires an impacts array")
    affected = {}
    for index, row in enumerate(rows):
        if not isinstance(row, Mapping):
            raise DiffError(
                f"{label}: module-impact impacts[{index}] must be an object"
            )
        changed = require_string(
            row, "changed", f"{label}: module-impact impacts[{index}]"
        )
        values = row.get("affected")
        if not isinstance(values, list) or not all(
            isinstance(value, str) for value in values
        ):
            raise DiffError(
                f"{label}: module-impact impacts[{index}] requires an affected string array"
            )
        affected[changed] = values
    return affected


def direct_dependencies(
    names: tuple[str, ...], edges: tuple[tuple[str, str], ...]
) -> dict[str, frozenset[str]]:
    return {
        name: frozenset(target for source, target in edges if source == name)
        for name in names
    }


def compare(before: object, after: object) -> tuple[dict, int]:
    before_impact = impact(before, "before")
    after_impact = impact(after, "after")
    before_names, before_edges = topology_key(before, "before")
    after_names, after_edges = topology_key(after, "after")
    before_interfaces = interfaces(before, before_names, "before")
    after_interfaces = interfaces(after, after_names, "after")
    before_affected = affected_map(before_impact, "before")
    after_affected = affected_map(after_impact, "after")
    before_deps = direct_dependencies(before_names, before_edges)
    after_deps = direct_dependencies(after_names, after_edges)
    names = after_names + tuple(
        name for name in before_names if name not in after_names
    )

    added = [name for name in after_names if name not in before_interfaces]
    removed = [name for name in before_names if name not in after_interfaces]
    moved = []
    interface_status = {}
    for name in before_names:
        if name not in after_interfaces:
            interface_status[name] = "removed"
            continue
        old = before_interfaces[name]
        new = after_interfaces[name]
        if old["scope"] != new["scope"] or old["algorithm"] != new["algorithm"]:
            raise DiffError(f"module {name!r} changed interface scope or algorithm")
        exports_equal = old["exports"] == new["exports"]
        digest_equal = old["digest"] == new["digest"]
        if exports_equal != digest_equal:
            raise DiffError(
                f"module {name!r} digest and complete export comparison disagree"
            )
        status = "preserved" if exports_equal else "moved"
        interface_status[name] = status
        if not exports_equal:
            moved.append(name)
    for name in added:
        interface_status[name] = "added"

    topology_changed = [
        name
        for name in names
        if before_deps.get(name, frozenset()) != after_deps.get(name, frozenset())
    ]
    seed_set = set(moved) | set(added) | set(removed) | set(topology_changed)
    seeds = [name for name in names if name in seed_set]
    closure_by_seed = {}
    for seed in seeds:
        closure_by_seed[seed] = set(before_affected.get(seed, [])) | set(
            after_affected.get(seed, [])
        )
    candidates = {
        name
        for name in after_names
        if any(name in closure for closure in closure_by_seed.values())
    }
    ordered_candidates = [name for name in after_names if name in candidates]
    module_rows = [
        {
            "module": name,
            "interface": interface_status[name],
            "recheckCandidate": name in candidates,
            "invalidatedBy": [seed for seed in seeds if name in closure_by_seed[seed]],
        }
        for name in names
    ]

    laws_moved = law_projection(before, "before") != law_projection(after, "after")
    if laws_moved:
        decision = {
            "status": "indeterminate",
            "actualChecksSkipped": False,
            "artifactReuseAuthorized": False,
            "reason": "law evidence moved outside module interface records",
        }
        gap = {
            "code": "module-owned-public-law-contract",
            "need": "a stable per-module public-law contract fact before complete dependent-check invalidation is decidable",
        }
        status = 2
    else:
        decision = {
            "status": "measured",
            "actualChecksSkipped": False,
            "artifactReuseAuthorized": False,
            "reason": "type/shape candidates are re-derivable in principle; no independent checked artifact exists",
        }
        gap = None
        status = 0

    result = {
        "ok": True,
        "schemaVersion": 1,
        "comparisonBasis": "complete-module-interface-exports+validated-module-topology",
        "modules": module_rows,
        "typeShapeInvalidation": {
            "moved": moved,
            "added": added,
            "removed": removed,
            "topologyChanged": topology_changed,
            "recheckCandidates": ordered_candidates,
        },
        "lawFactsMoved": laws_moved,
        "decision": decision,
        "gap": gap,
    }
    return result, status


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("before", type=Path, help="earlier bang query dump JSON file")
    parser.add_argument("after", type=Path, help="later bang query dump JSON file")
    args = parser.parse_args()
    try:
        result, status = compare(load_dump(args.before), load_dump(args.after))
        print(json.dumps(result, separators=(",", ":")))
        return status
    except DiffError as error:
        print(f"interface-diff: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    try:
        subprocess.run(
            ["bash", "tools/tool-log.sh", "interface-diff.py"],
            cwd=ROOT,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            check=False,
        )
    except OSError:
        pass
    raise SystemExit(main())
