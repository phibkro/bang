#!/usr/bin/env python3
# tool: role=check couples=ONBOARDING.md,CLAUDE.md runs-in=fitness
"""check-onboarding-refs.py — ONBOARDING's note references ⊆ CLAUDE's index (drift gate).

CLAUDE.md's reference index is the SSoT for "which `docs/notes/*.md` is a CURRENT
working reference" (its `active` set — llms.txt is generated from it, and
check-doc-hygiene enforces active⟹in-CLAUDE). ONBOARDING.md hand-copies a curated
onboarding SUBSET of those pointers. That copy is convention-tier: when a note is
de-indexed from CLAUDE (e.g. flipped to `archival` once its ADR lands), ONBOARDING
can silently keep listing it as a live reference — check-refs still passes (the
FILE exists), so the staleness is invisible.

This leg makes that SPECIFIC drift testable:

    FAIL when ONBOARDING.md cites a `docs/notes/<x>.md` that CLAUDE.md's index
    does NOT (an onboarding pointer to a note CLAUDE no longer treats as current).

Deliberately one-directional (ONBOARDING ⊆ CLAUDE): ONBOARDING is a SUBSET by
design, so the converse (a CLAUDE note absent from ONBOARDING) is expected, not a
smell. Existence of the target is check-refs's job; this checks CURRENCY.
Zero dependencies (stdlib), like the other tools/ scripts. Rides `just fitness`
(no build).
"""
from __future__ import annotations

import re
import subprocess
import sys

NOTE_RE = re.compile(r"docs/notes/[A-Za-z0-9._/-]+\.md")


def main() -> int:
    root = subprocess.run(
        ["git", "rev-parse", "--show-toplevel"], capture_output=True, text=True, check=True
    ).stdout.strip()
    onboarding = open(f"{root}/ONBOARDING.md", encoding="utf-8").read()
    claude = open(f"{root}/CLAUDE.md", encoding="utf-8").read()

    print("── check-onboarding-refs (ONBOARDING note pointers ⊆ CLAUDE index) ──")

    cited = sorted(set(NOTE_RE.findall(onboarding)))
    # The OPEN_QUESTIONS ledger is a generated index, not a note; CLAUDE cites it
    # via the same path, so it is covered — no special-case needed.
    stale = [p for p in cited if p not in claude]

    if not stale:
        print(f"PASS: all {len(cited)} `docs/notes/*.md` pointer(s) in ONBOARDING.md "
              f"are current in CLAUDE.md's reference index.")
        return 0

    for p in stale:
        print(f"DRIFT  ONBOARDING.md cites `{p}` but CLAUDE.md's index does not "
              f"(de-indexed / archival?):")
    print("FAIL: an onboarding pointer names a note CLAUDE.md no longer treats as a")
    print("      current reference. Fix: drop the ONBOARDING row (git holds the history),")
    print("      or re-add the note to CLAUDE.md's index if it IS still current.")
    return 1


if __name__ == "__main__":
    sys.exit(main())
