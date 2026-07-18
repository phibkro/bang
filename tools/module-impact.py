#!/usr/bin/env python3
# tool: role=analysis couples=Bang/Frontend/Query.lean,Main.lean runs-in=manual
"""Measure structural rebuild fanout from `bang query dump` module facts.

Usage:
    bang query dump path/to/main.bang | python3 tools/module-impact.py

The input is BANG's versioned, path-free fact export. The output reports the reverse-transitive
affected set for changing each logical module, plus a deliberately structural comparison:

* ``wholeProgramPairs`` assumes every possible single-module change rebuilds every module;
* ``dependencyPairs`` sums the exact affected-set sizes from the exported DAG;
* ``avoidedPairs`` is their difference.

These are equally weighted module/change pairs, not timings, cache hits, or a speedup claim. The
consumer ignores unknown JSON fields as required by dump schema v1 and fails loudly on malformed,
dangling, duplicate, or cyclic topology rather than inventing an invalidation answer. Impact rows
and affected lists follow the deterministic order of the input ``modules`` table; their meaning is
set-valued.
"""

from __future__ import annotations

import json
import subprocess
import sys
from collections.abc import Mapping


class ImpactError(ValueError):
    """The dump cannot support a sound structural-impact answer."""


def require_string(row: Mapping, key: str, context: str) -> str:
    value = row.get(key)
    if not isinstance(value, str) or not value:
        raise ImpactError(f"{context} requires a non-empty string {key!r}")
    return value


def topology(document: object) -> tuple[list[str], list[tuple[str, str]]]:
    if not isinstance(document, Mapping):
        raise ImpactError("dump must be a JSON object")
    if document.get("ok") is not True:
        raise ImpactError("dump did not report ok:true")
    version = document.get("schemaVersion")
    if type(version) is not int or version != 1:
        raise ImpactError("module-impact supports dump schemaVersion 1")

    module_rows = document.get("modules")
    edge_rows = document.get("moduleDeps")
    if not isinstance(module_rows, list) or not isinstance(edge_rows, list):
        raise ImpactError("dump requires modules and moduleDeps arrays")

    names = []
    seen_names = set()
    for index, row in enumerate(module_rows):
        if not isinstance(row, Mapping):
            raise ImpactError(f"modules[{index}] must be an object")
        name = require_string(row, "name", f"modules[{index}]")
        if name in seen_names:
            raise ImpactError(f"duplicate module {name!r}")
        names.append(name)
        seen_names.add(name)
    if not names or names[0] != "@entry":
        raise ImpactError("modules must begin with the reserved @entry node")

    known = set(names)
    edges = []
    seen_edges = set()
    for index, row in enumerate(edge_rows):
        if not isinstance(row, Mapping):
            raise ImpactError(f"moduleDeps[{index}] must be an object")
        edge = (
            require_string(row, "from", f"moduleDeps[{index}]"),
            require_string(row, "to", f"moduleDeps[{index}]"),
        )
        if edge[0] not in known or edge[1] not in known:
            raise ImpactError(f"moduleDeps[{index}] has an unknown endpoint")
        if edge in seen_edges:
            raise ImpactError(f"duplicate dependency {edge[0]!r} -> {edge[1]!r}")
        edges.append(edge)
        seen_edges.add(edge)

    # Kahn's algorithm verifies the resolver-DAG premise independently of row order.
    indegree = {name: 0 for name in names}
    outgoing = {name: [] for name in names}
    for source, target in edges:
        outgoing[source].append(target)
        indegree[target] += 1
    ready = [name for name in names if indegree[name] == 0]
    visited = 0
    while ready:
        source = ready.pop()
        visited += 1
        for target in outgoing[source]:
            indegree[target] -= 1
            if indegree[target] == 0:
                ready.append(target)
    if visited != len(names):
        raise ImpactError("moduleDeps contains a cycle")
    return names, edges


def measure(document: object) -> dict:
    names, edges = topology(document)
    reverse = {name: [] for name in names}
    for source, target in edges:
        reverse[target].append(source)

    impacts = []
    dependency_pairs = 0
    for changed in names:
        affected_set = {changed}
        pending = [changed]
        while pending:
            target = pending.pop()
            for dependent in reverse[target]:
                if dependent not in affected_set:
                    affected_set.add(dependent)
                    pending.append(dependent)
        affected = [name for name in names if name in affected_set]
        dependency_pairs += len(affected)
        impacts.append(
            {
                "changed": changed,
                "affected": affected,
                "affectedCount": len(affected),
            }
        )

    whole_program_pairs = len(names) * len(names)
    return {
        "ok": True,
        "schemaVersion": 1,
        "moduleCount": len(names),
        "impacts": impacts,
        "structuralWork": {
            "wholeProgramPairs": whole_program_pairs,
            "dependencyPairs": dependency_pairs,
            "avoidedPairs": whole_program_pairs - dependency_pairs,
        },
    }


def main() -> int:
    try:
        document = json.load(sys.stdin)
        print(json.dumps(measure(document), separators=(",", ":")))
        return 0
    except (ImpactError, json.JSONDecodeError) as error:
        print(f"module-impact: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    try:
        subprocess.run(
            ["bash", "tools/tool-log.sh", "module-impact.py"],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            check=False,
        )
    except OSError:
        pass
    raise SystemExit(main())
