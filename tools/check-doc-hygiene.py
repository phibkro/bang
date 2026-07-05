#!/usr/bin/env python3
"""check-doc-hygiene.py — the doc-reachability / staleness fitness function.

The DUAL of `check-refs.py`. That tool checks OUTBOUND links (a doc's references
resolve). This one checks INBOUND reachability (something references the doc) —
the drift it catches is a doc that quietly falls off the map: cited by nobody,
never re-read, silently rotting. `docs/decisions/` has a GENERATED ledger
(frontmatter → gen-adr-index → bijection), so ADRs can't fall off. `docs/notes/`
is HAND-indexed in CLAUDE.md, so it drifts exactly there — this test climbs that
survey to a check.

Model: reachability from the ENTRY docs (the always-loaded / onboarding roots)
over the citation graph (doc X cites doc Y iff basename(Y) appears in X's text).
A `docs/notes/*.md` unreachable from any root is an ORPHAN — flagged unless it is
a documented archival exception in `tools/docs-allow.txt` (the refs-allow.txt
pattern: an intentional terminal doc is a greppable, reasoned entry, not a silent
orphan).

Also REPORTS (never hard-fails on): per-doc age (days since last commit),
inbound-citation count, and a soft staleness heuristic — a doc carrying
status-table vocabulary (IN-FLIGHT / TODO / IN PROGRESS / RE-KEY) that has not
been touched in >STALE_DAYS is likely describing a reality that has moved on.

Usage:
  check-doc-hygiene.py            # full report (age · refs · reachability)
  check-doc-hygiene.py --check    # exit 1 on an un-allowlisted orphan (for fitness)
"""
import os
import re
import subprocess
import sys

ROOT = subprocess.run(["git", "rev-parse", "--show-toplevel"],
                      capture_output=True, text=True).stdout.strip()
ALLOW = os.path.join(ROOT, "tools", "docs-allow.txt")
STALE_DAYS = 21
STATUS_VOCAB = re.compile(r"\b(IN-FLIGHT|IN PROGRESS|TODO|RE-KEY|WIP|in flight)\b")

# The entry docs — reachability roots. Anything a fresh agent loads first.
ROOTS = ["CLAUDE.md", "AGENTS.md", "ONBOARDING.md", "CONTEXT.md", "ROADMAP.md",
         "README.md", "docs/decisions/README.md", "references/README.md"]


def tracked_md():
    out = subprocess.run(["git", "ls-files", "*.md"], capture_output=True, text=True,
                         cwd=ROOT).stdout.splitlines()
    # skip vendored foreign-project skill instances (not ours to govern)
    return [f for f in out if not f.startswith(".claude/skills/")
            and not f.endswith("/SKILL.md")]


def commit_epoch(path, ref=""):
    args = ["git", "log", "-1", "--format=%ct"]
    if ref:
        args.append(ref)
    args += ["--", path]
    r = subprocess.run(args, capture_output=True, text=True, cwd=ROOT).stdout.strip()
    return int(r) if r else 0


def load_allow():
    if not os.path.exists(ALLOW):
        return set()
    out = set()
    for line in open(ALLOW):
        line = line.split("#", 1)[0].strip()
        if line:
            out.add(line)
    return out


def main():
    check = "--check" in sys.argv
    files = tracked_md()
    texts = {f: open(os.path.join(ROOT, f), encoding="utf-8").read() for f in files}
    basenames = {os.path.basename(f): f for f in files}

    # citation edges: X -> Y iff basename(Y) appears in X (self-excluded)
    cites = {f: set() for f in files}
    for f, txt in texts.items():
        for bn, target in basenames.items():
            if target != f and bn in txt:
                cites[f].add(target)

    # BFS reachability from the roots
    seen = set()
    stack = [r for r in ROOTS if r in texts]
    while stack:
        cur = stack.pop()
        if cur in seen:
            continue
        seen.add(cur)
        stack.extend(cites.get(cur, ()))

    allow = load_allow()
    now = commit_epoch(".")  # HEAD time via the repo's latest commit
    now = int(subprocess.run(["git", "log", "-1", "--format=%ct"],
                             capture_output=True, text=True, cwd=ROOT).stdout.strip())

    notes = sorted(f for f in files if f.startswith("docs/notes/"))
    inbound = {f: sum(1 for g in files if f in cites[g]) for f in notes}

    orphans, stale = [], []
    print("── doc-hygiene (docs/notes reachability + staleness) ──")
    print(f"{'age':>5} {'lines':>6} {'in':>3}  reach  doc")
    for f in notes:
        age = (now - commit_epoch(f)) // 86400
        lines = texts[f].count("\n") + 1
        reachable = f in seen
        bn = os.path.basename(f)
        allowed = bn in allow or f in allow
        tag = "OK   " if reachable else ("archiv" if allowed else "ORPHAN")
        if not reachable and not allowed:
            orphans.append(f)
        if reachable and age > STALE_DAYS and STATUS_VOCAB.search(texts[f]):
            stale.append((f, age))
        print(f"{age:>4}d {lines:>6} {inbound[f]:>3}  {tag}  {bn}")

    if stale:
        print("\n⚠ soft-stale (status vocabulary + untouched >%dd — verify against reality):" % STALE_DAYS)
        for f, age in stale:
            print(f"    {age}d  {os.path.basename(f)}")

    if orphans:
        print("\nORPHANS (unreachable from any entry doc, not allowlisted):")
        for f in orphans:
            print(f"    {f}")
        print("Fix: link it from the CLAUDE.md reference index or a citing doc, "
              "delete it (history lives in git), or add it to tools/docs-allow.txt "
              "with a reason if it is an intentional archival terminal.")
        if check:
            return 1
    else:
        print("\nreachability: OK — every docs/notes/*.md is reachable or allowlisted.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
