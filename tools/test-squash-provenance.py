#!/usr/bin/env python3
# tool: role=test couples=provenance.py,gen-changelog.py,gen-proof-state.py,check-sha-reachable.sh,.github/workflows/verify.yml runs-in=fitness
"""Integration/falsifier suite for squash-stable generated provenance."""

from __future__ import annotations

import importlib.util
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

TOOLS = Path(__file__).resolve().parent
REPO = TOOLS.parent
sys.path.insert(0, str(TOOLS))

from provenance import (  # noqa: E402
    ProvenanceError,
    change_id,
    encode_manifest_records,
    index_tree,
    normalize_changelog,
    proof_input_id,
)

passed = 0


def check(name: str, condition: bool) -> None:
    global passed
    if not condition:
        raise AssertionError(name)
    passed += 1
    print(f"  ✓ {name}")


def run(
    *args: str,
    cwd: Path,
    env: dict[str, str] | None = None,
    expect: int = 0,
) -> subprocess.CompletedProcess[str]:
    merged = os.environ.copy()
    for key in tuple(merged):
        if key.startswith("CHANGELOG_") or key.startswith("PROVENANCE_"):
            del merged[key]
    if env:
        merged.update(env)
    result = subprocess.run(args, cwd=cwd, env=merged, text=True, capture_output=True)
    if result.returncode != expect:
        raise AssertionError(
            f"{' '.join(args)} exited {result.returncode}, expected {expect}\n"
            f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}"
        )
    return result


def git(root: Path, *args: str, env: dict[str, str] | None = None) -> str:
    return run("git", *args, cwd=root, env=env).stdout.strip()


def expect_fail(name: str, *args: str, cwd: Path, env=None) -> None:
    result = run(*args, cwd=cwd, env=env, expect=1)
    check(name, "FAIL:" in result.stdout or result.stderr)


def gen_args(root: Path, baseline: str, boundary: str) -> list[str]:
    return [
        sys.executable,
        str(TOOLS / "gen-changelog.py"),
        "--root",
        str(root),
        "--start",
        baseline,
        "--boundary",
        boundary,
    ]


def proof_env(fake_bin: Path) -> dict[str, str]:
    return {"PATH": f"{fake_bin}:{os.environ['PATH']}"}


def write_fixture(root: Path) -> tuple[str, str, Path]:
    git(root, "init", "-b", "main")
    git(root, "config", "user.name", "Provenance Test")
    git(root, "config", "user.email", "provenance@example.invalid")
    (root / "Bang").mkdir()
    (root / "Bang/Audit.lean").write_text("#print axioms foo\n")
    (root / "CHANGELOG.md").write_text(
        "# Fixture changelog\n\n"
        "<!-- BEGIN GENERATED changelog (just changelog) — do not hand-edit -->\n\n"
        "## Unreleased\n\n"
        "_Nothing notable since the MVP baseline yet._\n\n"
        "<!-- END GENERATED changelog -->\n"
    )
    (root / "CONTEXT.md").write_text(
        "# Context\n\n"
        "<!-- BEGIN GENERATED proof-state (just proof-state) — do not hand-edit -->\n"
        "placeholder\n"
        "<!-- END GENERATED proof-state -->\n"
    )
    (root / "ROADMAP.md").write_text("# Roadmap\n")
    (root / "tools").mkdir()
    (root / "tools/burndown.sh").write_text(
        "#!/usr/bin/env bash\nprintf 'TOTAL 0 0 0\\n'\n"
    )
    (root / "tools/burndown.sh").chmod(0o755)
    for name in (
        "gen-proof-state.py",
        "audit_facts.py",
        "leanlex.py",
        "genblock.py",
        "provenance.py",
    ):
        (root / "tools" / name).write_text(f"# fixture {name}\n")
    for name in (
        "lean-toolchain",
        "lakefile.toml",
        "lake-manifest.json",
        "flake.nix",
        "flake.lock",
    ):
        (root / name).write_text(f"fixture {name}\n")
    git(root, "add", "-A")
    git(root, "commit", "-m", "chore: fixture baseline")
    baseline = git(root, "rev-parse", "HEAD")

    fake_bin = root / "fake-bin"
    fake_bin.mkdir()
    (fake_bin / "lake").write_text(
        "#!/usr/bin/env bash\n"
        "if [[ $1 == build ]]; then exit 0; fi\n"
        "if [[ $1 == env ]]; then "
        "printf \"'Bang.foo' does not depend on any axioms\\n\"; exit 0; fi\n"
        "exit 1\n"
    )
    (fake_bin / "lake").chmod(0o755)
    run(
        sys.executable,
        str(TOOLS / "gen-proof-state.py"),
        "--lean-root",
        str(root),
        "--context",
        str(root / "CONTEXT.md"),
        "--build",
        "--end",
        baseline,
        cwd=root,
        env=proof_env(fake_bin),
    )
    git(root, "add", "CONTEXT.md")
    git(root, "commit", "-m", "chore(generated): seed proof projection")
    return baseline, git(root, "rev-parse", "HEAD"), fake_bin


def main() -> int:
    print("── squash provenance integration ──")
    with tempfile.TemporaryDirectory(prefix="bang-provenance-") as tmp:
        root = Path(tmp) / "repo"
        root.mkdir()
        baseline, base, fake_bin = write_fixture(root)
        args = gen_args(root, baseline, base)

        git(root, "checkout", "-b", "pr")
        (root / "Bang/Audit.lean").write_text("#print axioms foo\n-- product change\n")
        (root / "binary.dat").write_bytes(b"\x00\xff\x10product\n")
        (root / "mode.sh").write_text("#!/bin/sh\nexit 0\n")
        (root / "mode.sh").chmod(0o755)
        os.symlink("mode.sh", root / "tool-link")
        (root / "rename-old.txt").write_text("renamed content\n")
        (root / "delete.me").write_text("delete in landing\n")
        git(root, "add", "-A")
        git(root, "commit", "-m", "chore: seed filesystem shapes")
        # Keep the conventional product delta as the sole notable commit in the range.
        git(root, "mv", "rename-old.txt", "rename-new.txt")
        (root / "delete.me").unlink()
        (root / "binary.dat").write_bytes(b"\x00\xff\x10changed\n")
        (root / "mode.sh").chmod(0o644)
        (root / "tool-link").unlink()
        os.symlink("rename-new.txt", root / "tool-link")
        (root / "tools/audit_facts.py").write_text("# changed proof classifier\n")
        git(root, "add", "-A")
        git(root, "commit", "-m", "fix(core): durable landing")
        source = git(root, "rev-parse", "HEAD")

        run(
            sys.executable,
            str(TOOLS / "gen-proof-state.py"),
            "--lean-root",
            str(root),
            "--context",
            str(root / "CONTEXT.md"),
            "--build",
            "--end",
            source,
            cwd=root,
            env=proof_env(fake_bin),
        )
        (root / "derived.txt").write_text("generated follow-up\n")
        git(root, "add", "-A")
        proposed = git(root, "write-tree")
        proposed_id = change_id(str(root), base, proposed, "fix(core): durable landing")
        run(
            *args,
            "--base",
            base,
            "--end",
            source,
            "--after-tree",
            proposed,
            "--title",
            "fix(core): durable landing",
            cwd=root,
            env={"CHANGELOG_STABLE_REF": base},
        )
        git(root, "add", "CHANGELOG.md")
        git(root, "commit", "-m", "chore(generated): refresh projections")
        pr_head = git(root, "rev-parse", "HEAD")
        pr_tree = git(root, "rev-parse", "HEAD^{tree}")
        pr_changelog = (root / "CHANGELOG.md").read_bytes()
        virtual_id = change_id(str(root), base, pr_head, "fix(core): durable landing")
        if proposed_id != virtual_id:
            print(git(root, "diff", "--stat", proposed, pr_head))
            print(git(root, "diff", "--name-status", proposed, pr_head))
        check(
            "generated follow-up changes only normalized changelog provenance",
            proposed_id == virtual_id,
        )
        rendered_id = re.search(rb"`change:([0-9a-f]{64})`", pr_changelog)
        check(
            "committed projection carries aggregate index identity",
            rendered_id is not None and rendered_id.group(1).decode() == virtual_id,
        )

        run(
            *args,
            "--base",
            base,
            "--end",
            pr_head,
            "--title",
            "fix(core): durable landing",
            "--check",
            cwd=root,
            env={"CHANGELOG_STABLE_REF": base},
        )
        check("PR source + generated follow-up projection passes", True)
        run(
            "bash",
            str(TOOLS / "check-sha-reachable.sh"),
            str(root),
            cwd=root,
            env={"PROVENANCE_STABLE_REF": base, "PROVENANCE_END": pr_head},
        )
        check("PR commit claims use base while proof uses final head", True)

        git(root, "checkout", "-b", "synthetic", base)
        git(root, "merge", "--no-ff", "pr", "-m", "synthetic PR merge")
        run(
            *args,
            "--base",
            base,
            "--end",
            pr_head,
            "--title",
            "fix(core): durable landing",
            "--check",
            cwd=root,
            env={"CHANGELOG_STABLE_REF": base},
        )
        check("synthetic merge context selects immutable PR head", True)

        git(root, "checkout", "-b", "landed", base)
        git(root, "merge", "--squash", "pr")
        git(root, "commit", "-m", "fix(core): durable landing (#190)")
        landed = git(root, "rev-parse", "HEAD")
        check(
            "squash preserves reviewed final tree",
            git(root, "rev-parse", "HEAD^{tree}") == pr_tree,
        )
        check(
            "virtual and canonical change identities are byte-identical",
            virtual_id
            == change_id(str(root), base, landed, "fix(core): durable landing (#190)"),
        )
        check(
            "canonical squash preserves CHANGELOG bytes",
            (root / "CHANGELOG.md").read_bytes() == pr_changelog,
        )
        run(
            *args,
            "--end",
            landed,
            "--check",
            cwd=root,
            env={"CHANGELOG_STABLE_REF": landed},
        )
        check("first canonical post-squash check passes", True)
        run(
            sys.executable,
            str(TOOLS / "gen-proof-state.py"),
            "--lean-root",
            str(root),
            "--context",
            str(root / "CONTEXT.md"),
            "--check",
            "--build",
            "--end",
            landed,
            cwd=root,
            env=proof_env(fake_bin),
        )
        check("authoritative post-squash proof projection passes", True)

        # Projection and policy falsifiers.
        original_changelog = (root / "CHANGELOG.md").read_text()
        (root / "CHANGELOG.md").write_text(
            original_changelog.replace("change:", "change:0", 1)
        )
        expect_fail(
            "tampered change identity fails",
            *args,
            "--end",
            landed,
            "--check",
            cwd=root,
            env={"CHANGELOG_STABLE_REF": landed},
        )
        (root / "CHANGELOG.md").write_text(original_changelog)
        expect_fail(
            "mismatched squash title fails",
            *args,
            "--base",
            base,
            "--end",
            pr_head,
            "--title",
            "fix(core): edited title",
            "--check",
            cwd=root,
            env={"CHANGELOG_STABLE_REF": base},
        )

        git(root, "checkout", "-b", "two-notable", base)
        (root / "one").write_text("1")
        git(root, "add", "one")
        git(root, "commit", "-m", "feat(test): one")
        (root / "two").write_text("2")
        git(root, "add", "two")
        git(root, "commit", "-m", "fix(test): two")
        two_head = git(root, "rev-parse", "HEAD")
        expect_fail(
            "two notable source commits fail squash policy",
            *args,
            "--base",
            base,
            "--end",
            two_head,
            "--check",
            cwd=root,
            env={"CHANGELOG_STABLE_REF": base},
        )
        expect_fail(
            "stale PR base fails",
            *args,
            "--base",
            base,
            "--end",
            pr_head,
            "--check",
            cwd=root,
            env={"CHANGELOG_STABLE_REF": landed},
        )

        git(root, "checkout", "-b", "merged", base)
        git(root, "merge", "--no-ff", "pr", "-m", "merge policy violation")
        merged = git(root, "rev-parse", "HEAD")
        expect_fail(
            "non-squash landing does not satisfy canonical projection",
            *args,
            "--end",
            merged,
            "--check",
            cwd=root,
            env={"CHANGELOG_STABLE_REF": merged},
        )

        git(root, "checkout", "landed")
        original_context = (root / "CONTEXT.md").read_text()
        mutated_context = original_context.replace("1 clean", "9 clean")
        (root / "CONTEXT.md").write_text(mutated_context)
        expect_fail(
            "proof count tamper fails authoritative --build check",
            sys.executable,
            str(TOOLS / "gen-proof-state.py"),
            "--lean-root",
            str(root),
            "--context",
            str(root / "CONTEXT.md"),
            "--check",
            "--build",
            "--end",
            landed,
            cwd=root,
            env=proof_env(fake_bin),
        )
        (root / "CONTEXT.md").write_text(original_context)

        blob = git(root, "rev-parse", f"{landed}:CHANGELOG.md")
        wrong = re.sub(r"tree:[0-9a-f]+", f"tree:{blob}", original_context, count=1)
        (root / "CONTEXT.md").write_text(wrong)
        expect_fail(
            "wrong object type in tree claim fails",
            "bash",
            str(TOOLS / "check-sha-reachable.sh"),
            str(root),
            cwd=root,
            env={"PROVENANCE_STABLE_REF": landed, "PROVENANCE_END": landed},
        )
        (root / "CONTEXT.md").write_text(original_context)

        orphan = run(
            "git",
            "commit-tree",
            f"{landed}^{{tree}}",
            "-m",
            "orphan",
            cwd=root,
        ).stdout.strip()
        (root / "ROADMAP.md").write_text(f"orphan waypoint `{orphan[:12]}`\n")
        expect_fail(
            "present orphan commit object is not canonical ancestry",
            "bash",
            str(TOOLS / "check-sha-reachable.sh"),
            str(root),
            cwd=root,
            env={"PROVENANCE_STABLE_REF": landed, "PROVENANCE_END": landed},
        )
        git(root, "branch", "deadbee", landed)
        (root / "ROADMAP.md").write_text("ref-spoof waypoint `deadbee`\n")
        expect_fail(
            "hex-named ref cannot spoof an object prefix",
            "bash",
            str(TOOLS / "check-sha-reachable.sh"),
            str(root),
            cwd=root,
            env={"PROVENANCE_STABLE_REF": landed, "PROVENANCE_END": landed},
        )
        (root / "ROADMAP.md").write_text("# Roadmap\n")

        git(root, "checkout", "-b", "bang-drift", landed)
        with (root / "Bang/Audit.lean").open("a") as handle:
            handle.write("-- unprojected drift\n")
        git(root, "add", "Bang/Audit.lean")
        git(root, "commit", "-m", "chore: drift Bang without projection")
        drift = git(root, "rev-parse", "HEAD")
        expect_fail(
            "Bang drift invalidates exact proof tree",
            "bash",
            str(TOOLS / "check-sha-reachable.sh"),
            str(root),
            cwd=root,
            env={"PROVENANCE_STABLE_REF": landed, "PROVENANCE_END": drift},
        )
        check(
            "proof derivation input drift changes typed digest",
            proof_input_id(str(root), landed) != proof_input_id(str(root), drift),
        )

        # Filesystem semantics all perturb the aggregate identity.
        git(root, "checkout", "pr")
        variants = []
        (root / "binary.dat").write_bytes(b"different binary")
        git(root, "add", "binary.dat")
        variants.append(("binary bytes", git(root, "write-tree")))
        git(root, "reset", "--hard", "pr")
        (root / "mode.sh").chmod(0o755)
        git(root, "add", "mode.sh")
        variants.append(("executable mode", git(root, "write-tree")))
        git(root, "reset", "--hard", "pr")
        (root / "tool-link").unlink()
        os.symlink("mode.sh", root / "tool-link")
        git(root, "add", "tool-link")
        variants.append(("symlink target", git(root, "write-tree")))
        git(root, "reset", "--hard", "pr")
        git(root, "mv", "rename-new.txt", "rename-again.txt")
        variants.append(("rename paths", git(root, "write-tree")))
        git(root, "reset", "--hard", "pr")
        (root / "derived.txt").unlink()
        git(root, "add", "derived.txt")
        variants.append(("deletion", git(root, "write-tree")))
        for name, variant_tree in variants:
            check(
                f"{name} is bound by change identity",
                change_id(str(root), base, variant_tree, "fix(core): durable landing")
                != virtual_id,
            )
        git(root, "reset", "--hard", "pr")

        # Active temporary/pathspec index excludes unrelated unstaged bytes.
        alternate_index = root / "alternate.index"
        env = {"GIT_INDEX_FILE": str(alternate_index)}
        git(root, "read-tree", "pr", env=env)
        (root / "mode.sh").write_text("staged A\n")
        (root / "binary.dat").write_bytes(b"unstaged B")
        git(root, "add", "mode.sh", env=env)
        old_index = os.environ.get("GIT_INDEX_FILE")
        os.environ["GIT_INDEX_FILE"] = str(alternate_index)
        try:
            alternate_tree = index_tree(str(root))
        finally:
            if old_index is None:
                del os.environ["GIT_INDEX_FILE"]
            else:
                os.environ["GIT_INDEX_FILE"] = old_index
        check(
            "pathspec index captures staged A",
            git(root, "show", f"{alternate_tree}:mode.sh") == "staged A",
        )
        check(
            "pathspec index excludes unstaged B",
            git(root, "rev-parse", f"{alternate_tree}:binary.dat")
            == git(root, "rev-parse", "pr:binary.dat"),
        )
        git(root, "reset", "--hard", "pr")

        # Stable raw-content and marker boundaries.
        record = [(b"100644", b"blob", b"same-object", b"file")]
        left = encode_manifest_records(record, {b"same-object": b"left"})
        right = encode_manifest_records(record, {b"same-object": b"right"})
        check(
            "raw content defeats equal-metadata/object-id substitution", left != right
        )
        before_block = (root / "CHANGELOG.md").read_bytes()
        changed_block = before_block.replace(b"## Unreleased", b"## Tampered")
        check(
            "only generated changelog block is normalized",
            normalize_changelog(before_block) == normalize_changelog(changed_block),
        )
        check(
            "changelog prose remains identity-bound",
            normalize_changelog(b"prose A\n" + before_block)
            != normalize_changelog(b"prose B\n" + before_block),
        )
        try:
            normalize_changelog(before_block + before_block)
        except ProvenanceError:
            check("duplicate generated markers fail loudly", True)
        else:
            check("duplicate generated markers fail loudly", False)

        # Zero-notable docs range adds no changelog entry.
        git(root, "checkout", "-b", "docs-only", landed)
        (root / "docs.txt").write_text("docs\n")
        git(root, "add", "docs.txt")
        git(root, "commit", "-m", "docs(test): prose only")
        docs_head = git(root, "rev-parse", "HEAD")
        run(
            *args,
            "--base",
            landed,
            "--end",
            docs_head,
            "--title",
            "docs(test): prose only",
            "--check",
            cwd=root,
            env={"CHANGELOG_STABLE_REF": landed},
        )
        check("zero-notable docs range is valid and adds no entry", True)

        shallow = Path(tmp) / "shallow"
        run(
            "git",
            "clone",
            "--depth=1",
            "--branch",
            "landed",
            f"file://{root}",
            str(shallow),
            cwd=Path(tmp),
        )
        expect_fail(
            "shallow history fails canonical ancestry",
            "bash",
            str(TOOLS / "check-sha-reachable.sh"),
            str(shallow),
            cwd=shallow,
        )

        workflow = (REPO / ".github/workflows/verify.yml").read_text()
        check("PR title edits rerun Verify", "edited" in workflow)
        contributing = (REPO / "CONTRIBUTING.md").read_text()
        for setting in (
            "allow_squash_merge=true",
            "allow_merge_commit=false",
            "allow_rebase_merge=false",
            "COMMIT_OR_PR_TITLE",
            "COMMIT_MESSAGES",
        ):
            check(f"landing invariant documents {setting}", setting in contributing)

        spec = importlib.util.spec_from_file_location(
            "gen_dashboard", TOOLS / "gen-dashboard.py"
        )
        dashboard = importlib.util.module_from_spec(spec)
        assert spec.loader is not None
        spec.loader.exec_module(dashboard)
        mixed = (
            "### Features\n"
            "- **old** — legacy (`1234abcd`)\n"
            f"- **new** — stable (`change:{'a' * 64}`)\n"
        )
        check(
            "dashboard accepts mixed legacy/v2 identities",
            len(dashboard.parse_pulse(mixed)) == 2,
        )

    print(f"PASS: {passed}/{passed} squash-provenance checks.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
