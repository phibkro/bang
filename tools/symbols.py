#!/usr/bin/env python3
"""symbols.py — a generated symbol index for the Lean source (the navigation gap-fill).

General code-intelligence tools (tilth/stacklit) don't support Lean 4, so this is the
repo's own "where is X defined / what's in this module" index, derived from the source
(regex over top-level declarations). ON-DEMAND by design: a Lean symbol index keyed on
file:line churns every edit, so committing+gating it would be high-friction — instead it
regenerates fresh in <1s, so it can never drift.

Usage:
  python3 tools/symbols.py                 # every declaration, sorted by name
  python3 tools/symbols.py HasCTy          # only names containing "HasCTy" (case-insensitive)
  python3 tools/symbols.py --by-file       # grouped per module (a structural outline)
  python3 tools/symbols.py --json          # machine-readable

LIMITATION (stated): regex over source, not the Lean elaborator — it indexes top-level
declarations by keyword; anonymous `instance :` decls and local `where`/`let rec` defs are
not listed. For find-references (callers of X) use grep; this answers definitions only.
"""
import json
import os
import re
import subprocess
import sys

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
os.chdir(ROOT)

KINDS = "def|theorem|lemma|inductive|structure|class|instance|abbrev|axiom|opaque"
MODS = r"(?:private|protected|noncomputable|partial|unsafe|scoped|local)"
# A top-level declaration: optional @[attrs], optional modifiers, a kind keyword, then the
# name. Anchored at start-of-line (top-level decls sit at column 0, including mutual bodies),
# so indented local defs inside proofs are excluded.
DECL = re.compile(
    rf"^(?:@\[[^\]]*\]\s*)*(?:{MODS}\s+)*({KINDS})\s+([^\s({{:\[]+)(.*)$"
)


def lean_files():
    out = subprocess.run(["git", "ls-files", "Bang/*.lean", "Bang/**/*.lean"],
                         capture_output=True, text=True).stdout
    return sorted(set(out.split()))


def collect():
    syms = []
    for f in lean_files():
        for i, line in enumerate(open(f, errors="replace"), 1):
            m = DECL.match(line.rstrip("\n"))
            if not m:
                continue
            kind, name, rest = m.group(1), m.group(2), m.group(3).strip()
            # trim a signature preview to the binder/colon head, no trailing := body
            sig = rest.split(":=", 1)[0].strip()
            sig = (sig[:90] + "…") if len(sig) > 90 else sig
            syms.append({"name": name, "kind": kind, "file": f, "line": i, "sig": sig})
    return syms


def main():
    args = sys.argv[1:]
    as_json = "--json" in args
    by_file = "--by-file" in args
    pats = [a for a in args if not a.startswith("--")]
    syms = collect()
    if pats:
        needle = pats[0].lower()
        syms = [s for s in syms if needle in s["name"].lower()]

    if as_json:
        print(json.dumps(syms, indent=2))
        return 0

    if by_file:
        cur = None
        for s in sorted(syms, key=lambda s: (s["file"], s["line"])):
            if s["file"] != cur:
                cur = s["file"]
                print(f"\n── {cur} ──")
            print(f"  {s['line']:>5}  {s['kind']:<9} {s['name']}")
    else:
        for s in sorted(syms, key=lambda s: s["name"].lower()):
            loc = f"{s['file']}:{s['line']}"
            print(f"{s['name']:<42} {s['kind']:<9} {loc}")

    print(f"\n{len(syms)} declaration(s)"
          + (f" matching '{pats[0]}'" if pats else "")
          + f" across {len({s['file'] for s in syms})} module(s).", file=sys.stderr)
    return 0


sys.exit(main())
