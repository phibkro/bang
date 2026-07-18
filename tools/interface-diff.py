#!/usr/bin/env python3
# tool: role=analysis couples=tools/module-impact.py,Bang/Frontend/Query.lean,Main.lean runs-in=manual
"""Compare two BANG dump files without pretending that an artifact can be reused.

The view compares complete checked module-interface exports—including declared public-law
contracts—uses ``module-impact.py`` for the validated reverse-dependency closure, and reports
interface recheck candidates. It never skips a compiler phase: current interface facts are neither
cache-key-safe nor separate-compilation-ready.

Exit status 2 is a successful comparison whose complete invalidation decision is indeterminate.
That remains a fail-loud residue when global realization-law evidence moves without any owning
public declared-law contract movement in the module-interface records.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from collections import Counter
from collections.abc import Mapping
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MODULE_IMPACT = ROOT / "tools" / "module-impact.py"
EXPECTED_INTERFACE_ALGORITHM = "bang-module-interface-json-v2-uint64"


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
    laws = row.get("laws")
    if not isinstance(laws, list):
        raise DiffError(f"{context} requires a declared-law 'laws' array")
    projected_laws = []
    for index, law in enumerate(laws):
        law_context = f"{context}.laws[{index}]"
        if not isinstance(law, Mapping):
            raise DiffError(f"{law_context} must be an object")
        params = law.get("params")
        if not isinstance(params, list) or not all(
            isinstance(value, str) for value in params
        ):
            raise DiffError(f"{law_context} field 'params' must be an array of strings")
        law_id = require_string(law, "id", law_context)
        contract_id = require_string(law, "contractId", law_context)
        name = require_string(law, "name", law_context)
        if law_id != f"{contract_id}:{name}":
            raise DiffError(f"{law_context} id does not agree with contractId/name")
        projected_laws.append(
            {
                "id": law_id,
                "contractId": contract_id,
                "name": name,
                "params": params,
                "body": require_string(law, "body", law_context),
            }
        )
    projected["laws"] = projected_laws
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
        algorithm = require_string(row, "algorithm", context)
        if algorithm != EXPECTED_INTERFACE_ALGORITHM:
            raise DiffError(
                f"{context} requires interface algorithm {EXPECTED_INTERFACE_ALGORITHM!r}; "
                f"got {algorithm!r}"
            )
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
            "algorithm": algorithm,
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


def law_projection(document: object, label: str) -> tuple[tuple[str, str], ...]:
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
            "id": require_string(row, "id", context),
            "trait": require_string(row, "trait", context),
            "contract": require_string(row, "contract", context),
            "contractId": require_string(row, "contractId", context),
            "realization": realization,
            "realizationId": row.get("realizationId"),
            "law": require_string(row, "law", context),
            "params": params,
            "body": require_string(row, "body", context),
        }
        if fact["realizationId"] is not None and not isinstance(
            fact["realizationId"], str
        ):
            raise DiffError(f"{context} field 'realizationId' must be a string or null")
        relation = fact["contractId"]
        if fact["realizationId"] is not None:
            relation += f"@{fact['realizationId']}"
        if fact["id"] != f"{relation}:{fact['law']}":
            raise DiffError(
                f"{context} id does not agree with contractId/realizationId/law"
            )
        projected.append(
            (
                json.dumps(fact, sort_keys=True, separators=(",", ":")),
                fact["contractId"],
            )
        )
    return tuple(sorted(projected))


def public_law_contract_projection(interface: Mapping) -> tuple[str, ...]:
    projected = []
    for export in interface["exports"]:
        for law in export["laws"]:
            fact = {"owner": export["id"], **law}
            projected.append(json.dumps(fact, sort_keys=True, separators=(",", ":")))
    return tuple(projected)


def public_law_contracts_by_id(interfaces: Mapping) -> dict[str, tuple[str, ...]]:
    grouped: dict[str, list[str]] = {}
    for interface in interfaces.values():
        for export in interface["exports"]:
            for law in export["laws"]:
                contract_id = law["contractId"]
                grouped.setdefault(contract_id, []).append(
                    json.dumps(law, sort_keys=True, separators=(",", ":"))
                )
    return {contract_id: tuple(rows) for contract_id, rows in grouped.items()}


def changed_law_contract_ids(
    before_rows: tuple[tuple[str, str], ...],
    after_rows: tuple[tuple[str, str], ...],
) -> set[str]:
    before_counts = Counter(before_rows)
    after_counts = Counter(after_rows)
    return {
        contract_id
        for row, contract_id in set(before_counts) | set(after_counts)
        if before_counts[(row, contract_id)] != after_counts[(row, contract_id)]
    }


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

    public_law_contracts_moved = [
        name
        for name in names
        if public_law_contract_projection(before_interfaces.get(name, {"exports": []}))
        != public_law_contract_projection(after_interfaces.get(name, {"exports": []}))
    ]
    before_public_contracts = public_law_contracts_by_id(before_interfaces)
    after_public_contracts = public_law_contracts_by_id(after_interfaces)
    public_law_contract_ids_moved = {
        contract_id
        for contract_id in set(before_public_contracts) | set(after_public_contracts)
        if before_public_contracts.get(contract_id)
        != after_public_contracts.get(contract_id)
    }

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

    before_laws = law_projection(before, "before")
    after_laws = law_projection(after, "after")
    changed_instance_contract_ids = changed_law_contract_ids(before_laws, after_laws)
    unexplained_contract_ids = sorted(
        changed_instance_contract_ids - public_law_contract_ids_moved
    )
    laws_moved = before_laws != after_laws
    if unexplained_contract_ids:
        decision = {
            "status": "indeterminate",
            "actualChecksSkipped": False,
            "artifactReuseAuthorized": False,
            "reason": "realization-law evidence moved without an owning public declared-law contract delta",
        }
        gap = {
            "code": "unexplained-realization-law-movement",
            "need": "an owner-stable explanation before this realization-law delta can participate in complete invalidation",
        }
        status = 2
    else:
        decision = {
            "status": "measured",
            "actualChecksSkipped": False,
            "artifactReuseAuthorized": False,
            "reason": "public interface candidates are re-derivable in principle; no independent checked artifact exists",
        }
        gap = None
        status = 0

    result = {
        "ok": True,
        "schemaVersion": 2,
        "comparisonBasis": "complete-module-interface-exports-including-declared-laws+validated-module-topology",
        "modules": module_rows,
        "interfaceInvalidation": {
            "moved": moved,
            "added": added,
            "removed": removed,
            "topologyChanged": topology_changed,
            "recheckCandidates": ordered_candidates,
        },
        "publicLawContractsMoved": public_law_contracts_moved,
        "lawFactsMoved": laws_moved,
        "unexplainedLawContractIds": unexplained_contract_ids,
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
