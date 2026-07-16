#!/usr/bin/env python3
# tool: role=gen couples=CHANGELOG.md,provenance.py runs-in=fitness
"""Generate CHANGELOG.md from canonical history plus one virtual squash landing.

Entries through the fixed v2 schema boundary retain their durable canonical-main
commit anchors byte-for-byte. Later entries carry ``change:<sha256>``: a digest of
the canonical parent, normalized conventional subject, and complete before/after
delta manifests (normalizing only CHANGELOG.md's recursive generated block). A
PR's source + generated-follow-up range and GitHub's configured squash commit
therefore render byte-identically when their final trees and titles agree.

The optional ``--base`` declares the stable parent of a virtual landing ending at
``--end``.  That range may contain exactly one product-notable commit.  In CI the
base, end, stable ref, and PR title are explicit event facts.  Locally a full clone
derives the base from origin/main.  ``--end-index`` lets the pre-commit hook bind
the staged final tree before the generated follow-up commit exists.
"""

from __future__ import annotations

import argparse
import os
import re
import sys

from genblock import splice as _splice
from provenance import (
    ProvenanceError,
    change_id,
    commit,
    default_stable_ref,
    git_text,
    index_tree,
    normalize_subject,
)

BEGIN = "<!-- BEGIN GENERATED changelog (just changelog) — do not hand-edit -->"
END = "<!-- END GENERATED changelog -->"
BASELINE = "833e3a95f1c668b9346d35dcfcf06ee4c72c3160"
LEGACY_BOUNDARY = "ef7a0fba03204d73492478685088c5dc25e23a76"
SECTIONS = [("feat", "Features"), ("fix", "Fixes"), ("perf", "Performance")]
ENTRY_RE = re.compile(
    r"^(?P<type>[a-z]+)(\((?P<scope>[^)]+)\))?(?P<bang>!)?: (?P<subject>.+)$"
)


def parse_entry(subject: str, *, squash_title: bool = False):
    value = normalize_subject(subject) if squash_title else subject
    match = ENTRY_RE.match(value)
    if not match or match.group("type") not in dict(SECTIONS):
        return None
    return (
        match.group("type"),
        match.group("scope"),
        match.group("subject"),
        bool(match.group("bang")),
    )


def history(root: str, start: str, end: str) -> list[tuple[str, str]]:
    try:
        raw = git_text(root, "log", f"{start}..{end}", "--reverse", "--format=%H%x1f%s")
    except ProvenanceError as exc:
        raise ProvenanceError(f"cannot derive changelog history: {exc}") from exc
    rows = []
    for line in raw.splitlines():
        if line:
            rows.append(tuple(line.split("\x1f", 1)))
    return rows


def canonical_entries(root: str, start: str, end: str, boundary: str) -> list[tuple]:
    boundary_sha = commit(root, boundary)
    if git_text(root, "merge-base", boundary_sha, end) != boundary_sha:
        raise ProvenanceError(
            f"schema boundary {boundary_sha} is not an ancestor of endpoint {end}"
        )
    legacy = set(git_text(root, "rev-list", boundary_sha).splitlines())
    result = []
    for sha, subject in history(root, start, end):
        is_legacy = sha in legacy
        parsed = parse_entry(subject, squash_title=not is_legacy)
        if not parsed:
            continue
        if is_legacy:
            identity = sha[:8]
        else:
            parent = git_text(root, "rev-parse", f"{sha}^")
            identity = f"change:{change_id(root, parent, sha, subject)}"
        result.append((*parsed, identity))
    return result


def virtual_entry(
    root: str, base: str, end: str, after: str, expected_title: str | None
):
    rows = [
        (sha, subject)
        for sha, subject in history(root, base, end)
        if parse_entry(subject, squash_title=True)
    ]
    if not rows:
        return None
    if len(rows) != 1:
        raise ProvenanceError(
            f"virtual landing {base[:12]}..{end[:12]} has {len(rows)} product-notable "
            "commits; squash policy requires exactly one"
        )
    _, subject = rows[0]
    if expected_title is not None and normalize_subject(
        expected_title
    ) != normalize_subject(subject):
        raise ProvenanceError(
            "squash title does not match the product commit: "
            f"{expected_title!r} != {subject!r}"
        )
    return (
        *parse_entry(subject, squash_title=True),
        f"change:{change_id(root, base, after, subject)}",
    )


def resolve_base(root: str, end: str, explicit: str | None) -> tuple[str, str]:
    stable = os.environ.get("CHANGELOG_STABLE_REF", default_stable_ref(root))
    stable_sha = commit(root, stable)
    if explicit:
        base = commit(root, explicit)
        if base != stable_sha:
            raise ProvenanceError(
                f"declared base {base} is stale; stable ref {stable} is {stable_sha}"
            )
        return base, stable
    end_sha = commit(root, end)
    if end_sha == stable_sha:
        return end_sha, stable
    base = git_text(root, "merge-base", end_sha, stable_sha)
    if base != stable_sha:
        raise ProvenanceError(
            f"{end} is not based on stable ref {stable} ({stable_sha})"
        )
    return base, stable


def entries(
    root: str,
    *,
    start: str = BASELINE,
    boundary: str = LEGACY_BOUNDARY,
    base: str | None = None,
    end: str = "HEAD",
    after: str | None = None,
    title: str | None = None,
) -> dict[str, list[tuple]]:
    start_sha = commit(root, start)
    end_sha = commit(root, end)
    base_sha, _ = resolve_base(root, end_sha, base)
    if git_text(root, "merge-base", start_sha, base_sha) != start_sha:
        raise ProvenanceError(f"baseline {start_sha} is not an ancestor of {base_sha}")
    buckets: dict[str, list[tuple]] = {kind: [] for kind, _ in SECTIONS}
    for kind, scope, subject, bang, identity in canonical_entries(
        root, start_sha, base_sha, boundary
    ):
        buckets[kind].append((scope, subject, identity, bang))
    if end_sha != base_sha:
        if git_text(root, "merge-base", base_sha, end_sha) != base_sha:
            raise ProvenanceError(
                f"base {base_sha} is not an ancestor of end {end_sha}"
            )
        item = virtual_entry(root, base_sha, end_sha, after or end_sha, title)
        if item:
            kind, scope, subject, bang, identity = item
            buckets[kind].append((scope, subject, identity, bang))
    return buckets


def render(root: str, **kwargs) -> str:
    buckets = entries(root, **kwargs)
    out = [BEGIN, "", "## Unreleased", ""]
    populated = False
    for kind, heading in SECTIONS:
        if not buckets[kind]:
            continue
        populated = True
        out.append(f"### {heading}")
        for scope, subject, identity, bang in buckets[kind]:
            mark = "**⚠ BREAKING** " if bang else ""
            prefix = f"**{scope}** — " if scope else ""
            out.append(f"- {mark}{prefix}{subject} (`{identity}`)")
        out.append("")
    if not populated:
        out += ["_Nothing notable since the MVP baseline yet._", ""]
    out.append(END)
    return "\n".join(out)


def splice(md: str, block: str) -> str:
    return _splice(md, BEGIN, END, block)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", default=".")
    parser.add_argument("--file", default=None)
    parser.add_argument("--start", default=BASELINE)
    parser.add_argument("--boundary", default=LEGACY_BOUNDARY)
    parser.add_argument("--base", default=os.environ.get("CHANGELOG_BASE"))
    parser.add_argument("--end", default=os.environ.get("CHANGELOG_END", "HEAD"))
    parser.add_argument("--title", default=os.environ.get("CHANGELOG_TITLE"))
    parser.add_argument("--after-tree", default=os.environ.get("CHANGELOG_AFTER_TREE"))
    parser.add_argument("--end-index", action="store_true")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    root = os.path.abspath(args.root)
    path = os.path.abspath(args.file or os.path.join(root, "CHANGELOG.md"))
    try:
        if args.end_index and args.after_tree:
            raise ProvenanceError("choose only one of --end-index and --after-tree")
        after = index_tree(root) if args.end_index else args.after_tree
        block = render(
            root,
            start=args.start,
            boundary=args.boundary,
            base=args.base,
            end=args.end,
            after=after,
            title=args.title,
        )
    except ProvenanceError as exc:
        print(f"── changelog ──\nFAIL: {exc}")
        return 1
    if not os.path.exists(path):
        print(f"── changelog ──\nFAIL: {path} missing")
        return 1
    md = open(path, encoding="utf-8").read()
    if BEGIN not in md or END not in md:
        print(f"── changelog ──\nFAIL: {path} has no GEN markers")
        return 1
    expected = splice(md, block)
    if args.check:
        if expected == md:
            print(
                "── changelog ──\nPASS: CHANGELOG.md ≡ canonical history + virtual squash landing."
            )
            return 0
        print(
            "── changelog ──\nFAIL: CHANGELOG.md provenance is stale — run `just changelog`."
        )
        return 1
    open(path, "w", encoding="utf-8").write(expected)
    print(
        f"changelog: regenerated {os.path.relpath(path, root)} with stable change ids."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
