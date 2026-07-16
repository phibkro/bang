#!/usr/bin/env python3
# tool: role=lib couples=gen-changelog.py,gen-proof-state.py,test-squash-provenance.py runs-in=fitness
"""Landing-independent Git provenance primitives.

Commit ids identify history topology, so a squash necessarily replaces them.  The
identities here describe the facts that survive that rewrite:

* a change id binds the canonical parent, normalized product subject, and complete
  before/after records for every changed path (normalizing only CHANGELOG.md's
  recursive generated block);
* proof state binds both the exact Git tree object for ``Bang/`` and a SHA-256
  manifest of every repository input that can change the rendered census.

Both are deterministic from a complete local repository and require no network.
"""

from __future__ import annotations

import hashlib
import os
import re
import subprocess

DOMAIN = b"bang/change-id/v1\0"
PROOF_DOMAIN = b"bang/proof-input/v1\0"
CHANGELOG_PATH = "CHANGELOG.md"
PR_SUFFIX_RE = re.compile(r" \(#[1-9][0-9]*\)$")
CHANGELOG_BEGIN = (
    "<!-- BEGIN GENERATED changelog (just changelog) — do not hand-edit -->".encode()
)
CHANGELOG_END = b"<!-- END GENERATED changelog -->"
CHANGELOG_SENTINEL = b"<!-- GENERATED changelog normalized for change identity -->"
_CONTENT_CACHE: dict[tuple[str, bytes], bytes] = {}
PROOF_INPUT_FILES = frozenset(
    {
        "tools/gen-proof-state.py",
        "tools/audit_facts.py",
        "tools/burndown.sh",
        "tools/leanlex.py",
        "tools/genblock.py",
        "tools/provenance.py",
        "docfacts/proof-claims.json",
        "lean-toolchain",
        "lakefile.toml",
        "lake-manifest.json",
        "flake.nix",
        "flake.lock",
    }
)


class ProvenanceError(RuntimeError):
    """A provenance claim cannot be derived exactly."""


def git(root: str, *args: str, input_bytes: bytes | None = None) -> bytes:
    result = subprocess.run(
        ["git", "-C", root, *args], input=input_bytes, capture_output=True
    )
    if result.returncode != 0:
        detail = result.stderr.decode(errors="replace").strip()
        raise ProvenanceError(
            detail or f"git {' '.join(args)} exited {result.returncode}"
        )
    return result.stdout


def git_text(root: str, *args: str) -> str:
    return git(root, *args).decode().strip()


def commit(root: str, ref: str) -> str:
    return git_text(root, "rev-parse", "--verify", f"{ref}^{{commit}}")


def tree(root: str, ref: str) -> str:
    return git_text(root, "rev-parse", "--verify", f"{ref}^{{tree}}")


def normalize_subject(subject: str) -> str:
    """Normalize only GitHub's configured squash-title PR suffix."""
    return PR_SUFFIX_RE.sub("", subject)


def _contents(root: str, object_ids: list[bytes]) -> dict[bytes, bytes]:
    """Read raw blob contents in one batch."""
    missing = [
        oid for oid in dict.fromkeys(object_ids) if (root, oid) not in _CONTENT_CACHE
    ]
    if missing:
        output = git(
            root, "cat-file", "--batch", input_bytes=b"\n".join(missing) + b"\n"
        )
        cursor = 0
        for requested in missing:
            header_end = output.index(b"\n", cursor)
            header = output[cursor:header_end].split()
            if len(header) != 3 or header[1] != b"blob":
                raise ProvenanceError(
                    f"manifest object {requested.decode()} is not an available blob"
                )
            size = int(header[2])
            start = header_end + 1
            content = output[start : start + size]
            if len(content) != size or output[start + size : start + size + 1] != b"\n":
                raise ProvenanceError(
                    f"malformed cat-file response for {requested.decode()}"
                )
            _CONTENT_CACHE[(root, requested)] = content
            cursor = start + size + 1
        if cursor != len(output):
            raise ProvenanceError("unexpected trailing bytes from git cat-file --batch")
    return {oid: _CONTENT_CACHE[(root, oid)] for oid in object_ids}


def encode_manifest_records(
    records: list[tuple[bytes, bytes, bytes, bytes]], contents: dict[bytes, bytes]
) -> bytes:
    """Encode parsed ls-tree records through a unit-testable collision boundary."""
    encoded = []
    for mode, kind, object_id, path in records:
        if kind == b"blob":
            content = contents[object_id]
            if path == CHANGELOG_PATH.encode():
                content = normalize_changelog(content)
            identity = b"sha256:" + hashlib.sha256(content).hexdigest().encode()
        elif kind == b"commit":
            # A gitlink intentionally binds the exact submodule commit. Its content is
            # outside this repository and cannot be read as a local blob.
            identity = b"gitlink:" + object_id
        else:
            raise ProvenanceError(f"unsupported manifest object type {kind.decode()!r}")
        encoded.append(
            b"\0".join((str(len(path)).encode(), path, mode, kind, identity)) + b"\0"
        )
    return b"".join(encoded)


def normalize_changelog(content: bytes) -> bytes:
    """Replace only the recursive generated block; bind all surrounding prose."""
    begin_count = content.count(CHANGELOG_BEGIN)
    end_count = content.count(CHANGELOG_END)
    if begin_count == 0 and end_count == 0:
        return content
    if begin_count != 1 or end_count != 1:
        raise ProvenanceError(
            "CHANGELOG.md must have exactly one complete generated block "
            f"(found {begin_count} starts, {end_count} ends)"
        )
    start = content.find(CHANGELOG_BEGIN)
    end = content.find(CHANGELOG_END, start)
    if end < start:
        raise ProvenanceError("CHANGELOG.md generated-block markers are reversed")
    end += len(CHANGELOG_END)
    return content[:start] + CHANGELOG_SENTINEL + content[end:]


def manifest(
    root: str,
    treeish: str,
    *,
    proof_inputs_only: bool = False,
    include_paths: set[bytes] | None = None,
) -> bytes:
    """Canonical NUL-safe path/mode/type/raw-content manifest."""
    raw = git(root, "ls-tree", "-r", "-z", "--full-tree", treeish)
    records: list[tuple[bytes, bytes, bytes, bytes]] = []
    for record in raw.split(b"\0"):
        if not record:
            continue
        metadata, path = record.split(b"\t", 1)
        mode, kind, object_id = metadata.split(b" ", 2)
        if include_paths is not None and path not in include_paths:
            continue
        decoded_path = path.decode("utf-8", errors="surrogateescape")
        if proof_inputs_only and not (
            decoded_path.startswith("Bang/") or decoded_path in PROOF_INPUT_FILES
        ):
            continue
        records.append((mode, kind, object_id, path))
    contents = _contents(
        root, [object_id for _, kind, object_id, _ in records if kind == b"blob"]
    )
    return encode_manifest_records(records, contents)


def change_id(root: str, base: str, after: str, subject: str) -> str:
    """SHA-256 identity for the virtual squash ``base..after``."""
    base_commit = commit(root, base)
    base_tree = tree(root, base_commit)
    after_tree = tree(root, after)
    changed_paths = {
        path
        for path in git(
            root,
            "diff-tree",
            "--no-commit-id",
            "--name-only",
            "--no-renames",
            "-r",
            "-z",
            base_tree,
            after_tree,
        ).split(b"\0")
        if path
    }
    # Include the recursive projection on both sides even when its generated block
    # is the only difference. Otherwise the pre-commit index (old block) and final
    # commit (new block) would have different path-union domains despite normalizing
    # to the same content. Surrounding hand-written prose remains fully bound.
    changed_paths.add(CHANGELOG_PATH.encode())
    normalized = normalize_subject(subject)
    digest = hashlib.sha256()
    digest.update(DOMAIN)
    for label, value in (
        (b"parent", base_commit.encode()),
        (b"subject", normalized.encode()),
        (b"before", manifest(root, base_tree, include_paths=changed_paths)),
        (b"after", manifest(root, after_tree, include_paths=changed_paths)),
    ):
        digest.update(label + b"\0")
        digest.update(str(len(value)).encode() + b"\0" + value + b"\0")
    return digest.hexdigest()


def bang_tree(root: str, ref: str = "HEAD") -> str:
    oid = git_text(root, "rev-parse", "--verify", f"{ref}:Bang")
    kind = git_text(root, "cat-file", "-t", oid)
    if kind != "tree":
        raise ProvenanceError(f"{ref}:Bang is {kind}, not a tree")
    return oid


def proof_input_id(root: str, ref: str = "HEAD") -> str:
    """Bind every repository input that can alter the proof-state projection."""
    digest = hashlib.sha256(PROOF_DOMAIN)
    digest.update(manifest(root, tree(root, ref), proof_inputs_only=True))
    return digest.hexdigest()


def index_tree(root: str) -> str:
    """Materialize the caller's current Git index as a tree without changing it."""
    return git_text(root, "write-tree")


def default_stable_ref(root: str) -> str:
    configured = os.environ.get("PROVENANCE_STABLE_REF")
    if configured:
        return configured
    for candidate in ("refs/remotes/origin/main", "main"):
        try:
            commit(root, candidate)
            return candidate
        except ProvenanceError:
            pass
    return "HEAD"
