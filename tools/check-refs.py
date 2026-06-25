#!/usr/bin/env python3
"""check-refs.py — the stale cross-reference fitness function.

Climbs doc→file references from CONVENTION (hand-maintained) to TEST: a markdown
file that names a repo path (`Bang/Foo.lean`, `docs/bar.md`) or links to one
(`[x](../baz.md)`) must point at something that exists — or the reference is stale
and the build fails.

Robustness (the reason a real markdown parser was considered — captured here at
zero dependency cost):
  - fenced code blocks (``` / ~~~) are SKIPPED, so lambda/STM/Lean notation that
    happens to look like `](…)` or a path is not a false positive;
  - `<placeholder>` tokens, globs (`*`), and shell snippets are not paths;
  - `:NNN` line suffixes and `#anchors` are stripped before the existence check;
  - references resolve relative to the FILE's directory as well as the repo root,
    so `../ROADMAP.md` from docs/decisions/ is correctly found.

Intentional-historical references (a file that was archived/merged/deleted on
purpose, whose only home is now the git graph) are documented ONCE in
`tools/refs-allow.txt` — a new dangling ref fails; a known one is an explicit,
greppable exception. This is the single-source-of-truth move applied to "dead refs".

LIMITATION (stated, not hidden): a `file:NNN` line reference is validated only to
the FILE, never the line — line numbers drift constantly. Cite a SYMBOL, not a line,
if you want the reference to survive edits.
"""
import os
import re
import subprocess
import sys

ROOT = os.path.abspath(sys.argv[1] if len(sys.argv) > 1 else ".")
os.chdir(ROOT)

# Reference must end in one of these to be path-like (else it is prose/code/a module name).
EXTS = (".md", ".lean", ".sh", ".py", ".nix", ".bib", ".json", ".mjs",
        ".toml", ".lock", ".yaml", ".yml", ".txt", ".c", ".wat")

# Vendored skill copies configured for OTHER repos — their refs are not about this repo.
EXCLUDE_PREFIXES = (".claude/skills/codebase-maintenance/",)

LINK_RE = re.compile(r"\]\(([^)]+)\)")     # markdown link target
CODE_RE = re.compile(r"`([^`]+)`")          # inline-code span


def tracked_md():
    out = subprocess.run(["git", "ls-files", "*.md"], capture_output=True, text=True).stdout
    return [f for f in out.splitlines() if not f.startswith(EXCLUDE_PREFIXES)]


def load_allow():
    pats, path = [], "tools/refs-allow.txt"
    if os.path.exists(path):
        for line in open(path):
            line = line.split("#", 1)[0].strip()
            if line:
                pats.append(line)
    return pats


def candidates(line):
    for m in LINK_RE.finditer(line):
        yield m.group(1)
    for m in CODE_RE.finditer(line):
        yield m.group(1)


def is_pathish(tok):
    if any(c in tok for c in "<>*${}| \t"):
        return False
    if tok.startswith(("http://", "https://", "mailto:", "#")):
        return False
    # Require a LOCATING reference (a slash): `Bang/Eval.lean`, `../ROADMAP.md`. A bare
    # basename (`Audit.lean`) is a prose filename mention, not a path claim — and every
    # genuinely-stale reference in this repo specifies a directory, so the slash rule keeps
    # all real signal while dropping the bare-basename false positives.
    if "/" not in tok:
        return False
    return tok.endswith(EXTS)


def normalize(tok):
    tok = tok.split("#", 1)[0]                      # strip anchor
    tok = re.sub(r":\d+(-\d+)?$", "", tok)          # strip :NNN / :NNN-MMM line suffix
    return tok


def resolve(path, filedir):
    return os.path.exists(path) or os.path.exists(os.path.normpath(os.path.join(filedir, path)))


def main():
    allow = load_allow()
    stale = []
    for f in tracked_md():
        filedir = os.path.dirname(f)
        in_fence = False
        for i, line in enumerate(open(f, errors="replace"), 1):
            s = line.lstrip()
            if s.startswith("```") or s.startswith("~~~"):
                in_fence = not in_fence
                continue
            if in_fence:
                continue
            for tok in candidates(line):
                if not is_pathish(tok):
                    continue
                path = normalize(tok)
                if not path or resolve(path, filedir):
                    continue
                if any(a in tok for a in allow):
                    continue
                stale.append((f, i, tok))
    print("── check-refs (doc path/link references) ──")
    if not stale:
        print("PASS: every path/link reference resolves (intentional-historical refs in tools/refs-allow.txt).")
        return 0
    for f, i, tok in stale:
        print(f"STALE  {f}:{i}  ->  {tok}")
    print(f"FAIL: {len(stale)} stale reference(s). Fix the path, or — if it is intentional "
          f"history — add it to tools/refs-allow.txt with a reason.")
    return 1


sys.exit(main())
