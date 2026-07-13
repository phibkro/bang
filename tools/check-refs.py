#!/usr/bin/env python3
# tool: role=check couples=*.md,refs-allow.txt runs-in=fitness
"""check-refs.py — the stale cross-reference fitness function.

Climbs doc→file references from CONVENTION (hand-maintained) to TEST: a tracked
markdown file that names a repo path (`Bang/Foo.lean`, `docs/bar.md`) or links to
one (`[x](../baz.md)`) must point at a tracked repository file — or the reference
is stale and the build fails. Untracked working-tree files cannot satisfy a
reference. Ambiguous index states (intent-to-add or unstaged deletion) fail loud
rather than making local verification disagree with the next clean checkout.

Robustness (the reason a real markdown parser was considered — captured here at
zero dependency cost):
  - fenced code blocks (``` / ~~~) are SKIPPED, so lambda/STM/Lean notation that
    happens to look like `](…)` or a path is not a false positive;
  - `<placeholder>` tokens, globs (`*`), and shell snippets are not paths;
  - `:NNN` line suffixes and `#anchors` are stripped before classification;
  - references resolve relative to the FILE's directory as well as the repo root,
    so `../ROADMAP.md` from docs/decisions/ is correctly found;
  - absolute `/tmp/...` command artifacts are skipped, but other absolute-looking
    file references remain visible and fail unless explicitly allowed.

Intentional-historical references (a file that was archived/merged/deleted on
purpose, whose only home is now the git graph) are documented ONCE in
`tools/refs-allow.txt` — a new dangling ref fails; a known one is an explicit,
greppable exception. This is the single-source-of-truth move applied to "dead refs".

LIMITATION (stated, not hidden): a `file:NNN` line reference is validated only to
the FILE, never the line — line numbers drift constantly. Cite a SYMBOL, not a line,
if you want the reference to survive edits.
"""
import argparse
import os
import re
import subprocess
import sys
import tempfile

# Reference must end in one of these to be path-like (else it is prose/code/a module name).
EXTS = (".md", ".lean", ".sh", ".py", ".nix", ".bib", ".json", ".mjs",
        ".toml", ".lock", ".yaml", ".yml", ".txt", ".c", ".wat")

# Vendored skill copies configured for OTHER repos — their refs are not about this repo.
EXCLUDE_PREFIXES = (".claude/skills/codebase-maintenance/",)

LINK_RE = re.compile(r"\]\(([^)]+)\)")     # markdown link target
CODE_RE = re.compile(r"`([^`]+)`")          # inline-code span
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))


class ProjectionError(RuntimeError):
    pass


def git_output(root, *args):
    return subprocess.run(
        ["git", *args], cwd=root, capture_output=True, check=True
    ).stdout


def decode_paths(output):
    return {
        os.path.normpath(path)
        for path in output.decode(errors="surrogateescape").split("\0")
        if path
    }


def tracked_paths(root):
    deleted = decode_paths(git_output(root, "ls-files", "--deleted", "-z"))
    if deleted:
        ordered = sorted(deleted)
        shown = ", ".join(ordered[:3])
        more = f" (+{len(ordered) - 3} more)" if len(ordered) > 3 else ""
        raise ProjectionError(
            f"tracked path(s) deleted only in the worktree: {shown}{more}; stage or restore them"
        )

    staged_visible = decode_paths(
        git_output(root, "diff", "--cached", "--name-only", "-z", "--ita-visible-in-index")
    )
    staged_real = decode_paths(
        git_output(root, "diff", "--cached", "--name-only", "-z", "--ita-invisible-in-index")
    )
    intent_to_add = staged_visible - staged_real
    if intent_to_add:
        path = sorted(intent_to_add)[0]
        raise ProjectionError(
            f"intent-to-add path: {path}; stage its contents or remove the -N entry"
        )

    paths = set()
    for record in git_output(root, "ls-files", "--stage", "-z").split(b"\0"):
        if not record:
            continue
        metadata, raw_path = record.split(b"\t", 1)
        _mode, _raw_oid, raw_stage = metadata.split(b" ", 2)
        stage = raw_stage.decode("ascii")
        path = os.path.normpath(raw_path.decode(errors="surrogateescape"))
        if stage != "0":
            raise ProjectionError(f"unmerged index entry: {path}; resolve the conflict first")
        if path.endswith(EXTS):
            paths.add(path)
    return paths


def tracked_md(paths):
    return sorted(
        path
        for path in paths
        if path.endswith(".md") and not path.startswith(EXCLUDE_PREFIXES)
    )


def load_allow(root):
    pats, path = [], os.path.join(root, "tools/refs-allow.txt")
    if os.path.exists(path):
        for line in open(path):
            line = line.split("#", 1)[0].strip()
            if line:
                pats.append(line)
    return pats


def candidates(line):
    for match in LINK_RE.finditer(line):
        yield match.group(1)
    for match in CODE_RE.finditer(line):
        yield match.group(1)


def normalize(tok):
    tok = tok.split("#", 1)[0]                      # strip anchor
    tok = re.sub(r":\d+(-\d+)?$", "", tok)          # strip :NNN / :NNN-MMM line suffix
    return tok


def is_pathish(tok):
    if any(char in tok for char in "<>*${}| \t"):
        return False
    if tok.startswith(("http://", "https://", "mailto:", "#", "/tmp/")):
        return False
    # Require a LOCATING reference (a slash): `Bang/Eval.lean`, `../ROADMAP.md`. A bare
    # basename (`Audit.lean`) is a prose filename mention, not a path claim — and every
    # genuinely-stale reference in this repo specifies a directory, so the slash rule keeps
    # all real signal while dropping the bare-basename false positives.
    if "/" not in tok:
        return False
    return tok.endswith(EXTS)


def resolve(path, filedir, tracked):
    root_relative = os.path.normpath(path)
    file_relative = os.path.normpath(os.path.join(filedir, path))
    return root_relative in tracked or file_relative in tracked


def stale_references(root, tracked, allow):
    stale = []
    for filename in tracked_md(tracked):
        filedir = os.path.dirname(filename)
        in_fence = False
        with open(os.path.join(root, filename), errors="replace") as source:
            for line_number, line in enumerate(source, 1):
                stripped = line.lstrip()
                if stripped.startswith("```") or stripped.startswith("~~~"):
                    in_fence = not in_fence
                    continue
                if in_fence:
                    continue
                for tok in candidates(line):
                    path = normalize(tok)
                    if not is_pathish(path) or resolve(path, filedir, tracked):
                        continue
                    if any(pattern in tok for pattern in allow):
                        continue
                    stale.append((filename, line_number, tok))
    return stale


def run_git(root, *args):
    subprocess.run(["git", *args], cwd=root, check=True, capture_output=True)


def write(root, path, content):
    destination = os.path.join(root, path)
    os.makedirs(os.path.dirname(destination), exist_ok=True)
    with open(destination, "w") as handle:
        handle.write(content)


def self_test():
    with tempfile.TemporaryDirectory() as root:
        run_git(root, "init", "-q")
        write(
            root,
            "docs/note.md",
            "[tracked](docs/target.md#section)\n"
            "`tools/missing.py:42`\n"
            "`research/untracked.md`\n"
            "`/tmp/lint-out.txt`\n",
        )
        write(root, "docs/target.md", "# Target\n")
        run_git(root, "add", "docs/note.md", "docs/target.md")
        write(root, "research/untracked.md", "# Local only\n")

        tracked = tracked_paths(root)
        assert "research/untracked.md" not in tracked
        stale = {tok for _filename, _line, tok in stale_references(root, tracked, [])}
        assert stale == {"tools/missing.py:42", "research/untracked.md"}

        os.remove(os.path.join(root, "docs/target.md"))
        try:
            tracked_paths(root)
            raise AssertionError("unstaged deletion was accepted")
        except ProjectionError:
            pass
        write(root, "docs/target.md", "# Target\n")

        write(root, "docs/intent.md", "# Intent\n")
        run_git(root, "add", "-N", "docs/intent.md")
        try:
            tracked_paths(root)
            raise AssertionError("intent-to-add was accepted")
        except ProjectionError:
            pass


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "root",
        nargs="?",
        default=os.environ.get("REFS_ROOT", "."),
        help="repository root (default: REFS_ROOT or current directory)",
    )
    parser.add_argument("--self-test", action="store_true", help="run falsification poles only")
    args = parser.parse_args()
    root = os.path.abspath(args.root)

    try:
        self_test()
        if args.self_test:
            print(
                "check-refs self-test: PASS — Git projection, source scan, anchor, "
                "untracked, /tmp, deletion, and intent-to-add poles hold."
            )
            return 0

        subprocess.run(
            ["bash", os.path.join(SCRIPT_DIR, "tool-log.sh"), os.path.basename(__file__)],
            cwd=root,
            check=False,
        )
        tracked = tracked_paths(root)
        stale = stale_references(root, tracked, load_allow(root))
    except (AssertionError, ProjectionError, subprocess.CalledProcessError) as exc:
        print(f"check-refs: FAIL — {exc}")
        return 1

    print("── check-refs (doc path/link references) ──")
    if not stale:
        print("PASS: every path/link reference resolves (intentional-historical refs in tools/refs-allow.txt).")
        return 0
    for filename, line_number, tok in stale:
        print(f"STALE  {filename}:{line_number}  ->  {tok}")
    print(f"FAIL: {len(stale)} stale reference(s). Fix the path, or — if it is intentional "
          f"history — add it to tools/refs-allow.txt with a reason.")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
