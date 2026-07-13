#!/usr/bin/env python3
# tool: role=gen couples=CHANGELOG.md runs-in=fitness
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
    gen-changelog.py --check --end <sha>  # check an explicit history endpoint
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
BASELINE = "833e3a95f1c668b9346d35dcfcf06ee4c72c3160"

# (type, heading) — only PRODUCT-NOTABLE types. docs/chore/wip/test/tooling/refactor/simplify are
# dev-noise and excluded by construction (the entry-test below only keeps these three).
SECTIONS = [("feat", "Features"), ("fix", "Fixes"), ("perf", "Performance")]

# `<sha>\x1f<type>(scope)!?: subject`  — `\x1f` (unit separator) can't appear in a subject.
ENTRY_RE = re.compile(
    r"^(?P<sha>[0-9a-f]+)\x1f(?P<type>[a-z]+)(\((?P<scope>[^)]+)\))?(?P<bang>!)?: (?P<subject>.+)$")
FULL_SHA_RE = re.compile(r"^[0-9a-f]{40}$")


def commits(root: str, end: str = "HEAD", start: str = BASELINE) -> list[str]:
    """Conventional-commit subjects in start..end, oldest-first."""
    res = subprocess.run(
        ["git", "-C", root, "log", f"{start}..{end}", "--reverse", "--format=%H\x1f%s"],
        capture_output=True, text=True)
    if res.returncode != 0:
        detail = res.stderr.strip() or f"git log exited {res.returncode}"
        raise RuntimeError(f"cannot derive changelog history for {end}: {detail}")
    return res.stdout.splitlines()


def git_text(root: str, *args: str) -> str:
    res = subprocess.run(["git", "-C", root, *args], capture_output=True, text=True)
    if res.returncode != 0:
        detail = res.stderr.strip() or f"git {' '.join(args)} exited {res.returncode}"
        raise RuntimeError(detail)
    return res.stdout.strip()


def lag_refs(root: str, end: str) -> list[str]:
    """The sole parent that may satisfy the one-commit self-hash lag.

    Never guess across a merge. Callers checking a synthetic merge must declare the
    source commit through `--end` / `CHANGELOG_END`.
    """
    fields = git_text(root, "rev-list", "--parents", "-n", "1", end).split()
    parents = fields[1:]
    if len(parents) > 1:
        raise RuntimeError(
            f"{end} is a merge commit; set --end or CHANGELOG_END to the source commit"
        )
    return parents


def entries(root: str, end: str = "HEAD", start: str = BASELINE) -> dict[str, list[tuple]]:
    buckets: dict[str, list[tuple]] = {t: [] for t, _ in SECTIONS}
    for line in commits(root, end, start):
        m = ENTRY_RE.match(line)
        if not m or m.group("type") not in buckets:
            continue
        sha = m.group("sha")
        if not FULL_SHA_RE.fullmatch(sha):
            raise RuntimeError(f"git log returned a non-full commit id: {sha!r}")
        buckets[m.group("type")].append(
            (m.group("scope"), m.group("subject"), sha[:8], bool(m.group("bang"))))
    return buckets


def render(root: str, end: str = "HEAD") -> str:
    b = entries(root, end)
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
    try: __import__("subprocess").run(["bash", __import__("os").path.join(__import__("os").path.dirname(__file__), "tool-log.sh"), __import__("os").path.basename(__file__)], check=False)  # tool-log (plan 012)
    except Exception: pass
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--root", default=".", help="repo root (default: cwd)")
    ap.add_argument("--file", default=None, help="changelog path (default: <root>/CHANGELOG.md)")
    ap.add_argument(
        "--end",
        default=os.environ.get("CHANGELOG_END", "HEAD"),
        help="history endpoint (default: CHANGELOG_END or HEAD)",
    )
    ap.add_argument("--check", action="store_true", help="gate: file ≡ fresh render (drift → exit 1)")
    args = ap.parse_args()

    root = os.path.abspath(args.root)
    path = os.path.abspath(args.file or os.path.join(root, "CHANGELOG.md"))
    try:
        block = render(root, args.end)
    except RuntimeError as exc:
        print(f"── changelog ──\nFAIL: {exc}")
        return 1

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
        if splice(md, block) == md:
            print("── changelog ──\nPASS: CHANGELOG.md ≡ the conventional commits.")
            return 0
        # A commit cannot contain a changelog entry for its own not-yet-existing hash.
        # The caller declares the history endpoint; only that commit's sole parent may
        # satisfy the one-commit fixpoint lag.
        try:
            candidates = lag_refs(root, args.end)
            for ref in candidates:
                if splice(md, render(root, ref)) != md:
                    continue
                short = git_text(root, "rev-parse", "--short=8", ref)
                print(f"── changelog ──\nPASS: CHANGELOG.md ≡ the commits as of {short} "
                      "(the self-hash fixpoint lag — resyncs on the next `just changelog`).")
                return 0
        except RuntimeError as exc:
            print(f"── changelog ──\nFAIL: cannot check changelog fixpoint: {exc}")
            return 1
        print("── changelog ──\nFAIL: CHANGELOG.md is stale (≥2 commits behind) — run `just changelog`.")
        return 1

    open(path, "w", encoding="utf-8").write(splice(md, block))
    print(f"changelog: regenerated the block in {os.path.relpath(path, root)}.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
