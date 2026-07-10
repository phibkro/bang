#!/usr/bin/env python3
# tool: role=check couples=CONTEXT.md,gen-proof-state.py runs-in=fitness
"""check-context-claims.py — CONTEXT prose vs the generated proof-state (drift gate).

CONTEXT.md's proof-state BLOCK is generated (gen-proof-state.py); the NARRATIVE above
and below it is hand prose — convention-tier, so it can claim a health the gate refutes
(the observed failure mode: calling a sorryAx-flagged headline "clean"). This leg makes
that *specific* drift testable:

    FAIL when a prose line outside the generated block names a FLAGGED headline
    (backticked, short or fully-qualified) on the same line as a clean-claim
    keyword (clean / axiom-clean / sorry-free / sorryAx-free).

Deliberately ONE-DIRECTIONAL and line-granular: the converse (a clean headline
described as sorried) and all looser semantic drift ("pending X") stay with the
G2 `/doc-smells` judgment survey — a tighter net here would false-positive on
legitimate prose (e.g. "`sim` stays clean, no new sorryAx"). Flagged set comes
from the committed block itself (not a build), so this rides `just fitness`
(no-build) and stays consistent with gen-proof-state's own freshness gate.

Zero dependencies (stdlib), like the other tools/ scripts.
"""
from __future__ import annotations

import re
import subprocess
import sys

BEGIN = "<!-- BEGIN GENERATED proof-state (just proof-state) — do not hand-edit -->"
END = "<!-- END GENERATED proof-state -->"

FLAGGED_RE = re.compile(r"^\s*-\s+\*\*flagged:\*\*\s+`([^`]+)`")
TICKED_RE = re.compile(r"`([^`\s]+)`")
CLEAN_CLAIM_RE = re.compile(r"\b(axiom-clean|sorry-?free|sorryAx-?free|clean)\b", re.IGNORECASE)


def main() -> int:
    try: __import__("subprocess").run(["bash", __import__("os").path.join(__import__("os").path.dirname(__file__), "tool-log.sh"), __import__("os").path.basename(__file__)], check=False)  # tool-log (plan 012)
    except Exception: pass
    root = subprocess.run(
        ["git", "rev-parse", "--show-toplevel"], capture_output=True, text=True, check=True
    ).stdout.strip()
    text = open(f"{root}/CONTEXT.md", encoding="utf-8").read()

    print("── check-context-claims (prose vs generated proof-state) ──")
    if BEGIN not in text or END not in text:
        print("SKIP: no generated proof-state block in CONTEXT.md.")
        return 0

    before, rest = text.split(BEGIN, 1)
    block, after = rest.split(END, 1)

    flagged: set[str] = set()
    n_flagged = 0
    for line in block.splitlines():
        m = FLAGGED_RE.match(line)
        if m:
            name = m.group(1)
            n_flagged += 1
            flagged.add(name)
            flagged.add(name.rsplit(".", 1)[-1])  # short name too

    if not flagged:
        print("PASS: no flagged headlines in the block — nothing to cross-check.")
        return 0

    violations = []
    for lineno, line in enumerate((before + "\n" + after).splitlines(), start=1):
        if not CLEAN_CLAIM_RE.search(line):
            continue
        named = [t for t in TICKED_RE.findall(line) if t in flagged]
        if named:
            violations.append((lineno, named, line.strip()))

    if not violations:
        print(f"PASS: no prose line claims a flagged headline ({n_flagged} flagged) clean.")
        return 0

    for lineno, named, line in violations:
        print(f"DRIFT  CONTEXT.md ~line {lineno}: {', '.join(f'`{n}`' for n in named)} "
              f"is FLAGGED (sorryAx) but the prose claims clean:")
        print(f"       {line[:160]}")
    print("FAIL: prose contradicts the generated proof-state — fix the prose (or, if the")
    print("      gate moved, regenerate the block: `just proof-state`).")
    return 1


if __name__ == "__main__":
    sys.exit(main())
