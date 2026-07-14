#!/usr/bin/env python3
# tool: role=gen couples=Bang/**/*.lean,Bang/Audit.lean,Bang/Spec.lean,lean-toolchain,lakefile.toml,lake-manifest.json,docfacts/schema/proof.schema.json,docfacts/proof.json runs-in=fitness
"""Generate, statically check, and live-check BANG proof documentation facts."""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

from jsonschema.exceptions import ValidationError

import audit_facts
from architecture_facts import ArchitectureFactsError, proof_arrow_semantics
from docfacts_common import (
    check_evidence_sources,
    check_sorted_unique,
    checked_repo_path,
    reject_duplicate_ids,
    reload_and_validate,
    render_json,
    schema_validator,
    serialization_consumer_pole,
    validate_evidence_commands,
)
from import_facts import ImportFactsError
from symbols import SymbolFactsError, collect_public_symbols, collect_symbols

ROOT = Path(__file__).resolve().parent.parent
SCHEMA_PATH = ROOT / "docfacts/schema/proof.schema.json"
FACT_PATH = ROOT / "docfacts/proof.json"
ARCHITECTURE_PATH = ROOT / "docfacts/architecture.json"
SELF_TEST_POLES = 16


class ProofFactsError(ValueError):
    """Proof sources, reports, or cross-fact references are ambiguous or inconsistent."""


def slug(name: str) -> str:
    value = re.sub(r"[^a-z0-9]+", "-", name.lower()).strip("-")
    if not value:
        raise ProofFactsError(f"cannot form fact id from theorem name: {name}")
    return value


def tracked_proof_paths() -> list[str]:
    result = subprocess.run(
        [
            "git",
            "-C",
            str(ROOT),
            "ls-files",
            "Bang/*.lean",
            "Bang/**/*.lean",
            "lean-toolchain",
            "lakefile.toml",
            "lake-manifest.json",
        ],
        check=True,
        capture_output=True,
        text=True,
    )
    paths = sorted(set(result.stdout.splitlines()))
    required = {"lean-toolchain", "lakefile.toml", "lake-manifest.json"}
    if not required <= set(paths) or not any(
        path.startswith("Bang/") and path.endswith(".lean") for path in paths
    ):
        raise ProofFactsError("proof fingerprint inventory is incomplete")
    for path in paths:
        checked_repo_path(ROOT, path)
    return paths


def proof_fingerprint() -> dict:
    paths = tracked_proof_paths()
    digest = hashlib.sha256()
    for path in paths:
        raw_path = path.encode("utf-8")
        content = (ROOT / path).read_bytes()
        digest.update(len(raw_path).to_bytes(8, "big"))
        digest.update(raw_path)
        digest.update(len(content).to_bytes(8, "big"))
        digest.update(content)
    return {
        "algorithm": "sha256-sorted-path-content",
        "digest": digest.hexdigest(),
        "paths": paths,
    }


def source_symbols() -> list[dict]:
    return collect_symbols(ROOT)


def resolve_definition(written_ref: str, symbols: list[dict]) -> dict | None:
    base = written_ref.split(".")[-1]
    candidates = [
        symbol
        for symbol in symbols
        if symbol["name"] == base and symbol["kind"] in {"theorem", "lemma", "axiom"}
    ]
    if len(candidates) > 1:
        locations = ", ".join(f"{item['file']}:{item['line']}" for item in candidates)
        raise ProofFactsError(
            f"ambiguous theorem definition for {written_ref}: {locations}"
        )
    if not candidates:
        return None
    return {"path": candidates[0]["file"], "line": candidates[0]["line"]}


def spec_headlines() -> list[dict]:
    records = [
        {
            "name": f"Bang.{symbol['name']}",
            "kind": "theorem",
            "source": {"path": symbol["path"], "line": symbol["line"]},
        }
        for symbol in collect_public_symbols(ROOT)
        if symbol["path"] == "Bang/Spec.lean" and symbol["kind"] == "theorem"
    ]
    return sorted(records, key=lambda item: item["source"]["line"])


def build_enrollments(report_entries: list[tuple[str, list[str]]]) -> list[dict]:
    audit_entries = audit_facts.enrollments(ROOT)
    resolved = audit_facts.resolve_reports(audit_entries, report_entries)
    all_symbols = source_symbols()
    spec_names = {item["name"] for item in spec_headlines()}
    records = []
    for enrollment, report_name, axioms in resolved:
        trusted = set(axioms) <= audit_facts.TRUSTED
        is_spec = any(
            audit_facts.reference_matches(report_name, name) for name in spec_names
        )
        record = {
            "id": slug(report_name),
            "writtenRef": enrollment.written_ref,
            "reportName": report_name,
            "auditLine": enrollment.line,
            "definitionSource": resolve_definition(enrollment.written_ref, all_symbols),
            "specHeadline": is_spec,
            "axioms": sorted(set(axioms)),
            "classification": "trusted" if trusted else "flagged",
        }
        if trusted:
            record["evidenceLabel"] = "proven"
        records.append(record)
    return records


def proof_arrows() -> list[dict]:
    evidence_ids = {
        "contextual-equivalence": "lr-audit-status",
        "source-target-forward-simulation": "simulation-proven",
    }
    return [
        semantics | {"evidenceId": evidence_ids[semantics["id"]]}
        for semantics in proof_arrow_semantics()
    ]


def proof_evidence() -> list[dict]:
    return [
        {
            "id": "audit-generated",
            "label": "generated",
            "claim": "Enrollment, source-location, Spec-headline, fingerprint, and axiom classifications are deterministic projections of tracked proof sources and fresh kernel output.",
            "sources": ["Bang/Audit.lean", "Bang/Spec.lean", "tools/docfacts_proof.py"],
            "commands": ["python3 tools/docfacts_proof.py --live-check"],
        },
        {
            "id": "lr-audit-status",
            "label": "implemented",
            "claim": "The binary biorthogonal LR contextual-equivalence headlines are source-defined and Audit-enrolled. Their per-theorem axiom sets, not this method label, decide whether they are trusted or flagged.",
            "sources": [
                "Bang/Spec.lean",
                "Bang/Meta/LR.lean",
                "Bang/Meta/BinaryLR.lean",
                "Bang/Audit.lean",
            ],
            "commands": ["lake env lean Bang/Audit.lean"],
        },
        {
            "id": "simulation-proven",
            "label": "proven",
            "claim": "Bang.compile_forward_sim is trusted-Audit-backed support for the one-way source-execution to formal-target-execution simulation, under the theorem's VcapFree and successful-source premises.",
            "sources": ["Bang/Spec.lean", "Bang/Backend/Wasm.lean", "Bang/Audit.lean"],
            "commands": ["lake env lean Bang/Audit.lean"],
        },
    ]


def build_fact(report_entries: list[tuple[str, list[str]]]) -> dict:
    return {
        "schemaVersion": 1,
        "kind": "proof",
        "id": "proof",
        "title": "BANG proof inventory",
        "summary": "Kernel-reported axiom sets, Spec headline enrollment, proof-method arrows, and a dirty-tree-sensitive proof-source fingerprint.",
        "trustedAxioms": sorted(audit_facts.TRUSTED),
        "sourceFingerprint": proof_fingerprint(),
        "specHeadlines": spec_headlines(),
        "enrollments": build_enrollments(report_entries),
        "proofArrows": proof_arrows(),
        "evidence": sorted(proof_evidence(), key=lambda item: item["id"]),
    }


def synthetic_report_entries() -> list[tuple[str, list[str]]]:
    entries = []
    for enrollment in audit_facts.enrollments(ROOT):
        canonical = (
            enrollment.written_ref
            if enrollment.written_ref.startswith("Bang.")
            else f"Bang.{enrollment.written_ref}"
        )
        axioms = ["propext", "sorryAx"] if enrollment.written_ref == "lr_sound" else []
        entries.append((canonical, axioms))
    return entries


def validate_serialized_fact(fact: dict) -> None:
    schema_validator(SCHEMA_PATH).validate(fact)
    if fact["trustedAxioms"] != sorted(audit_facts.TRUSTED):
        raise ValidationError("trusted axiom set drifted")
    if fact["proofArrows"] != proof_arrows():
        raise ValidationError("proof arrow semantics drifted")
    check_sorted_unique(
        fact["specHeadlines"], lambda item: item["source"]["line"], "Spec headlines"
    )
    audit_lines = [item["auditLine"] for item in fact["enrollments"]]
    if audit_lines != sorted(audit_lines) or len(audit_lines) != len(set(audit_lines)):
        raise ValidationError("Audit enrollments must preserve unique source order")
    check_sorted_unique(fact["proofArrows"], lambda item: item["id"], "proof arrows")
    check_sorted_unique(fact["evidence"], lambda item: item["id"], "evidence")
    reject_duplicate_ids(
        fact["enrollments"] + fact["proofArrows"] + fact["evidence"], "proof"
    )

    spec_names = {item["name"] for item in fact["specHeadlines"]}
    enrolled_spec = set()
    report_names = []
    enrollment_by_report = {}
    for item in fact["enrollments"]:
        if not audit_facts.reference_matches(item["writtenRef"], item["reportName"]):
            raise ValidationError(
                f"canonical report name does not resolve written ref: {item['writtenRef']}"
            )
        report_names.append(item["reportName"])
        trusted = set(item["axioms"]) <= audit_facts.TRUSTED
        expected_class = "trusted" if trusted else "flagged"
        if item["classification"] != expected_class:
            raise ValidationError(
                f"axiom classification disagrees with actual set: {item['writtenRef']}"
            )
        if trusted and item.get("evidenceLabel") != "proven":
            raise ValidationError(
                f"trusted theorem lacks proven evidence: {item['writtenRef']}"
            )
        if not trusted and "evidenceLabel" in item:
            raise ValidationError(
                f"flagged theorem labelled proven: {item['writtenRef']}"
            )
        if item["axioms"] != sorted(set(item["axioms"])):
            raise ValidationError(
                f"axiom set is not sorted/unique: {item['writtenRef']}"
            )
        actual_spec = any(
            audit_facts.reference_matches(item["reportName"], name)
            for name in spec_names
        )
        if item["specHeadline"] != actual_spec:
            raise ValidationError(f"Spec headline flag drifted: {item['writtenRef']}")
        if actual_spec:
            enrolled_spec.update(
                name
                for name in spec_names
                if audit_facts.reference_matches(item["reportName"], name)
            )
        enrollment_by_report[item["reportName"]] = item
    if len(report_names) != len(set(report_names)):
        raise ValidationError("canonical Audit report names are not unique")
    if enrolled_spec != spec_names:
        missing = sorted(spec_names - enrolled_spec)
        raise ValidationError(
            f"Spec headline set is not exactly Audit-enrolled: {missing}"
        )

    evidence_by_id = {item["id"]: item for item in fact["evidence"]}
    for arrow in fact["proofArrows"]:
        if arrow["evidenceId"] not in evidence_by_id:
            raise ValidationError(f"missing proof-arrow evidence: {arrow['id']}")
        supporting = []
        for theorem_ref in arrow["theoremRefs"]:
            matches = [
                item
                for item in fact["enrollments"]
                if audit_facts.reference_matches(theorem_ref, item["reportName"])
            ]
            if len(matches) != 1:
                raise ValidationError(
                    f"proof arrow theorem does not resolve uniquely: {theorem_ref}"
                )
            supporting.append(matches[0])
        if evidence_by_id[arrow["evidenceId"]]["label"] == "proven" and any(
            item["classification"] != "trusted" for item in supporting
        ):
            raise ValidationError(f"proven arrow has flagged support: {arrow['id']}")
    semantic_keys = (
        "id",
        "from",
        "to",
        "endpointType",
        "direction",
        "method",
        "theoremRefs",
    )
    actual_semantics = [
        {key: arrow[key] for key in semantic_keys} for arrow in fact["proofArrows"]
    ]
    if actual_semantics != proof_arrow_semantics():
        raise ValidationError("LR and simulation proof semantics drifted")


def validate_fact(fact: dict) -> None:
    validate_serialized_fact(fact)
    if fact["sourceFingerprint"] != proof_fingerprint():
        raise ValidationError("proof source fingerprint is stale")
    if fact["specHeadlines"] != spec_headlines():
        raise ValidationError("Spec headline inventory is stale")
    source_enrollments = audit_facts.enrollments(ROOT)
    if [(item["writtenRef"], item["auditLine"]) for item in fact["enrollments"]] != [
        (item.written_ref, item.line) for item in source_enrollments
    ]:
        raise ValidationError("Audit enrollment inventory is stale")
    if len(fact["specHeadlines"]) != 18 or len(fact["enrollments"]) != 27:
        raise ValidationError("current Spec/Audit cardinality pole moved")
    if fact["evidence"] != sorted(proof_evidence(), key=lambda item: item["id"]):
        raise ValidationError("proof evidence drifted")
    all_symbols = source_symbols()
    for item in fact["enrollments"]:
        expected_source = resolve_definition(item["writtenRef"], all_symbols)
        if item["definitionSource"] != expected_source:
            raise ValidationError(f"definition source drifted: {item['writtenRef']}")
    check_evidence_sources(ROOT, fact["evidence"])
    validate_evidence_commands(ROOT, fact["evidence"])


def parse_fact(serialized: str) -> dict:
    return reload_and_validate(
        serialized, schema_validator(SCHEMA_PATH), [validate_serialized_fact]
    )


def render_consumer(fact: dict) -> str:
    return f"# {fact['title']}\n\n{fact['summary']}\n"


def validate_cross_fact(architecture: dict, proof: dict) -> None:
    evidence_by_id = {item["id"]: item for item in architecture["evidence"]}
    for arrow in architecture["arrows"] + architecture["proofArrows"]:
        support = []
        for theorem_ref in arrow["theoremRefs"]:
            matches = [
                item
                for item in proof["enrollments"]
                if audit_facts.reference_matches(theorem_ref, item["reportName"])
            ]
            if len(matches) != 1:
                raise ValidationError(
                    f"architecture theorem ref does not resolve uniquely in proof fact: {theorem_ref}"
                )
            support.append(matches[0])
        evidence_record = evidence_by_id[arrow["evidenceId"]]
        if evidence_record["label"] == "proven" and not support:
            raise ValidationError(
                f"architecture proven arrow has no theorem support: {arrow['id']}"
            )
        if evidence_record["label"] == "proven" and any(
            item["classification"] != "trusted" for item in support
        ):
            raise ValidationError(
                f"architecture proven arrow has flagged support: {arrow['id']}"
            )

    semantic_keys = (
        "id",
        "from",
        "to",
        "endpointType",
        "direction",
        "method",
        "theoremRefs",
    )

    def semantic_projection(arrow: dict) -> dict:
        return {key: arrow[key] for key in semantic_keys}

    if [semantic_projection(item) for item in architecture["proofArrows"]] != [
        semantic_projection(item) for item in proof["proofArrows"]
    ]:
        raise ValidationError("architecture/proof arrow semantics disagree")


def expect_invalid(name: str, fact: dict) -> bool:
    try:
        validate_fact(fact)
    except (ValidationError, ProofFactsError, audit_facts.AuditFactsError, KeyError):
        print(f"✓ known-bad {name} rejected")
        return True
    print(f"✗ known-bad {name} was accepted", file=sys.stderr)
    return False


def self_test() -> int:
    base = build_fact(synthetic_report_entries())
    validate_fact(base)
    cases = []

    def mutate(name, change):
        fact = copy.deepcopy(base)
        change(fact)
        cases.append((name, fact))

    mutate(
        "stale-theorem",
        lambda fact: fact["enrollments"][0].update(reportName="Bang.stale_theorem"),
    )
    mutate(
        "qualified-suffix-spoof",
        lambda fact: fact["enrollments"][0].update(reportName="Other.Bang.lr_sound"),
    )
    mutate("missing-theorem", lambda fact: fact["enrollments"].pop())
    invented = copy.deepcopy(base["enrollments"][-1])
    invented.update(
        id="invented-theorem",
        writtenRef="invented",
        reportName="Bang.invented",
        auditLine=999,
        definitionSource=None,
        specHeadline=False,
    )
    mutate("invented-theorem", lambda fact: fact["enrollments"].append(invented))
    mutate("missing-spec-headline", lambda fact: fact["specHeadlines"].pop())
    flagged_index = next(
        index
        for index, item in enumerate(base["enrollments"])
        if item["classification"] == "flagged"
    )
    mutate(
        "removed-sorryax",
        lambda fact: fact["enrollments"][flagged_index].update(axioms=["propext"]),
    )
    mutate(
        "flagged-labelled-proven",
        lambda fact: fact["enrollments"][flagged_index].update(evidenceLabel="proven"),
    )
    mutate(
        "collapsed-lr-simulation",
        lambda fact: fact["proofArrows"][0].update(
            endpointType="source-to-target-executions",
            direction="forward",
            method="annotated forward simulation",
            theoremRefs=["Bang.compile_forward_sim"],
        ),
    )
    mutate("missing-evidence-source", lambda fact: fact["evidence"][0].pop("sources"))
    mutate(
        "false-evidence-source",
        lambda fact: fact["evidence"][0].update(sources=["docs/missing.md"]),
    )
    mutate(
        "missing-evidence-command", lambda fact: fact["evidence"][0].update(commands=[])
    )
    mutate(
        "duplicate-id",
        lambda fact: fact["evidence"][1].update(id=fact["proofArrows"][0]["id"]),
    )

    passed = sum(expect_invalid(name, fact) for name, fact in cases)

    try:
        resolve_definition(
            "Bang.ambiguous",
            [
                {
                    "name": "ambiguous",
                    "kind": "theorem",
                    "file": "Bang/A.lean",
                    "line": 1,
                },
                {
                    "name": "ambiguous",
                    "kind": "theorem",
                    "file": "Bang/B.lean",
                    "line": 1,
                },
            ],
        )
    except ProofFactsError:
        print("✓ known-bad ambiguous theorem resolution rejected")
        passed += 1
    else:
        print("✗ ambiguous theorem resolution accepted", file=sys.stderr)

    for name, reports in (
        ("empty-kernel-output", []),
        ("missing-kernel-report", synthetic_report_entries()[:-1]),
    ):
        try:
            audit_facts.resolve_reports(audit_facts.enrollments(ROOT), reports)
        except audit_facts.AuditFactsError:
            print(f"✓ known-bad {name} rejected")
            passed += 1
        else:
            print(f"✗ known-bad {name} accepted", file=sys.stderr)

    serialized = serialization_consumer_pole(base, parse_fact, render_consumer)
    print(
        "✓ serialized JSON is the proof consumer boundary"
        if serialized
        else "✗ proof consumer bypassed serialized JSON",
        file=sys.stdout if serialized else sys.stderr,
    )
    passed += serialized
    total = len(cases) + 4
    if total != SELF_TEST_POLES:
        print(f"docfacts-proof: internal pole count mismatch: {total}", file=sys.stderr)
        return 1
    print(f"docfacts-proof self-test: {passed}/{total} poles passed.")
    return 0 if passed == total else 1


def live_fact() -> dict:
    output = audit_facts.authoritative_axiom_output(ROOT)
    reports = audit_facts.parse_axiom_entries(output)
    return build_fact(reports)


def write_output() -> int:
    fact = live_fact()
    validate_fact(fact)
    FACT_PATH.write_text(render_json(fact), encoding="utf-8")
    print(
        f"docfacts-proof: generated {FACT_PATH.relative_to(ROOT)} from fresh Audit output"
    )
    return 0


def print_axiom_census(fact: dict) -> None:
    print("── audited theorem axioms ──")
    for item in fact["enrollments"]:
        axioms = ", ".join(item["axioms"]) or "none"
        marker = "✓" if item["classification"] == "trusted" else "⚠"
        print(f"{marker} {item['reportName']}: [{axioms}]")


def check_output(live: bool) -> int:
    if not FACT_PATH.is_file():
        raise ProofFactsError(f"missing committed fact: {FACT_PATH.relative_to(ROOT)}")
    committed = parse_fact(FACT_PATH.read_text(encoding="utf-8"))
    validate_fact(committed)
    if live:
        expected = live_fact()
        validate_fact(expected)
        if FACT_PATH.read_text(encoding="utf-8") != render_json(expected):
            raise ProofFactsError(
                "committed proof fact differs from fresh authoritative Audit output"
            )
        print_axiom_census(expected)
        print(
            f"docfacts-proof: LIVE OK — {len(expected['specHeadlines'])} Spec headlines, {len(expected['enrollments'])} unique Audit reports"
        )
    else:
        print(
            f"docfacts-proof: OK — static inventories/fingerprint current; {len(committed['specHeadlines'])} Spec headlines, {len(committed['enrollments'])} Audit enrollments"
        )
    return 0


def cross_check() -> int:
    if not ARCHITECTURE_PATH.is_file() or not FACT_PATH.is_file():
        raise ProofFactsError("architecture/proof facts must exist before cross-check")
    from docfacts_architecture import parse_fact as parse_architecture_fact

    architecture = parse_architecture_fact(
        ARCHITECTURE_PATH.read_text(encoding="utf-8")
    )
    proof = parse_fact(FACT_PATH.read_text(encoding="utf-8"))
    validate_cross_fact(architecture, proof)
    print(
        "docfacts-proof: CROSS OK — architecture theorem refs and proof evidence agree"
    )
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument(
        "--check",
        action="store_true",
        help="static source/fingerprint check; never runs Lake",
    )
    mode.add_argument(
        "--live-check",
        action="store_true",
        help="rebuild and re-elaborate Audit, then compare",
    )
    mode.add_argument("--self-test", action="store_true")
    mode.add_argument("--cross-check", action="store_true")
    args = parser.parse_args()
    try:
        if args.self_test:
            return self_test()
        if args.check:
            return check_output(live=False)
        if args.live_check:
            return check_output(live=True)
        if args.cross_check:
            return cross_check()
        return write_output()
    except (
        OSError,
        subprocess.CalledProcessError,
        json.JSONDecodeError,
        ValidationError,
        ProofFactsError,
        ArchitectureFactsError,
        ImportFactsError,
        audit_facts.AuditFactsError,
        SymbolFactsError,
        AssertionError,
    ) as error:
        print(f"docfacts-proof: FAIL — {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
