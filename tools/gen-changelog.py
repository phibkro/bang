#!/usr/bin/env python3
"""gen-changelog.py — generate CHANGELOG.md from conventional commits (the GENERATE rung).

The changelog is a DERIVATION of git history, NOT a hand-maintained second copy — that would
violate single-source-of-truth + "history lives in git, not docs" (CLAUDE.md). So there is no
"write an entry" discipline and no per-merge gate: the conventional commit subject IS the entry,
written once where git already keeps it, and `--check` keeps the rendered file ≡ the commits
(same pattern as gen-adr-index / gen-import-graph / gen-proof-state).

An entry = a `feat` / `fix` / `perf` commit since the MVP BASELINE (the direction-shift to
"surface the verified kernel"). Commits before the baseline are the v1-verification grind
(`feat(kernel)`, `feat(model)`, …) — recorded in git + ROADMAP, NOT the product changelog.
Squash-merging each increment to `main` yields one clean conventional commit per shipped unit,
which is the right entry granularity for free (no per-commit noise, no per-merge gate).

Zero dependencies (stdlib), like the other tools/ generators.

Usage:
    gen-changelog.py                # rewrite the block in ./CHANGELOG.md
    gen-changelog.py --check        # gate: file ≡ a fresh render (drift = exit 1)
"""
from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys

BEGIN = "<!-- BEGIN GENERATED changelog (just changelog) — do not hand-edit -->"
END = "<!-- END GENERATED changelog -->"

# The MVP product era began at the direction-shift (the GitHub-issues migration). Commits before
# this are the v1-verification grind (out of product-changelog scope). Anchored to the commit, not
# a tag, because the repo has no release tags yet; switch to `git describe --tags` once it does.
BASELINE = "833e3a9"

# (type, heading) — only PRODUCT-NOTABLE types. docs/chore/wip/test/tooling/refactor/simplify are
# dev-noise and excluded by construction (the entry-test below only keeps these three).
SECTIONS = [("feat", "Features"), ("fix", "Fixes"), ("perf", "Performance")]

# `<sha>\x1f<type>(scope)!?: subject`  — `\x1f` (unit separator) can't appear in a subject.
ENTRY_RE = re.compile(
    r"^(?P<sha>[0-9a-f]+)\x1f(?P<type>[a-z]+)(\((?P<scope>[^)]+)\))?(?P<bang>!)?: (?P<subject>.+)$")


def commits(root: str) -> list[str]:
    """Conventional-commit subjects since the MVP baseline, oldest-first."""
    res = subprocess.run(
        ["git", "-C", root, "log", f"{BASELINE}..HEAD", "--reverse", "--format=%h\x1f%s"],
        capture_output=True, text=True)
    return res.stdout.splitlines() if res.returncode == 0 else []


def entries(root: str) -> dict[str, list[tuple]]:
    buckets: dict[str, list[tuple]] = {t: [] for t, _ in SECTIONS}
    for line in commits(root):
        m = ENTRY_RE.match(line)
        if not m or m.group("type") not in buckets:
            continue
        buckets[m.group("type")].append(
            (m.group("scope"), m.group("subject"), m.group("sha"), bool(m.group("bang"))))
    return buckets


def render(root: str) -> str:
    b = entries(root)
    out = [BEGIN, "", "## Unreleased", ""]
    populated = False
    for t, heading in SECTIONS:
        if not b[t]:
            continue
        populated = True
        out.append(f"### {heading}")
        for scope, subject, sha, bang in b[t]:
            mark = "**⚠ BREAKING** " if bang else ""
            pre = f"**{scope}** — " if scope else ""
            out.append(f"- {mark}{pre}{subject} (`{sha}`)")
        out.append("")
    if not populated:
        out += ["_Nothing notable since the MVP baseline yet._", ""]
    out.append(END)
    return "\n".join(out)


from genblock import splice as _splice  # the shared GEN-block primitive (#113)
def splice(md: str, block: str) -> str:
    return _splice(md, BEGIN, END, block)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--root", default=".", help="repo root (default: cwd)")
    ap.add_argument("--file", default=None, help="changelog path (default: <root>/CHANGELOG.md)")
    ap.add_argument("--check", action="store_true", help="gate: file ≡ fresh render (drift → exit 1)")
    args = ap.parse_args()

    root = os.path.abspath(args.root)
    path = os.path.abspath(args.file or os.path.join(root, "CHANGELOG.md"))
    block = render(root)

    if not os.path.exists(path):
        if args.check:
            print(f"── changelog ──\nFAIL: {path} missing — run `just changelog`.")
            return 1
        print(f"changelog: {path} missing — create it with the GEN markers first.", file=sys.stderr)
        return 1

    md = open(path, encoding="utf-8").read()
    if BEGIN not in md or END not in md:
        print(f"── changelog ──\nFAIL: {path} has no GEN markers — add them.")
        return 1

    if args.check:
        if splice(md, block) != md:
            print("── changelog ──\nFAIL: CHANGELOG.md is stale — run `just changelog`.")
            return 1
        print("── changelog ──\nPASS: CHANGELOG.md ≡ the conventional commits.")
        return 0

    open(path, "w", encoding="utf-8").write(splice(md, block))
    print(f"changelog: regenerated the block in {os.path.relpath(path, root)}.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
