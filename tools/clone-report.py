#!/usr/bin/env python3
# tool: role=analysis couples=Bang/**/*.lean,tools/leanlex.py runs-in=manual
"""clone-report.py — rank duplicated code windows in Lean sources.

Token-window clone detector, Lean-aware where it matters:
  * strips line comments (`-- …`) and block comments (`/- … -/`, nested),
    so doc drift never counts as a clone;
  * normalizes leading whitespace + collapses internal runs of spaces;
  * slides a WINDOW-line hash over each file, groups identical windows,
    then MERGES overlapping/adjacent hits into maximal clone regions so a
    40-line clone reports once, not 36 times.

Output: clone families ranked by duplicated mass (occurrences × lines),
each with a representative excerpt and every file:line anchor.

This finds EXTRACTION CANDIDATES, not extractions: in Lean, textually
identical tactic blocks can sit on different tactic states, and the right
abstraction differs per family (a lemma, a @[simp]/@[grind] set, an
`all_goals` restructure, or a tactic macro). Triage is a human/agent step.

Usage:
  python3 tools/clone-report.py [PATHS…] [--window N] [--min-count N] [--top N]
  (defaults: Bang/  --window 5  --min-count 4  --top 15)
"""

from __future__ import annotations
import argparse
import hashlib
import sys
from collections import defaultdict
from pathlib import Path

from leanlex import strip_comments


def normalized_lines(path: Path) -> list[tuple[int, str]]:
    """(original_lineno, normalized_line) for non-empty lines."""
    text = strip_comments(path.read_text(encoding="utf-8"))
    result = []
    for lineno, raw in enumerate(text.splitlines(), start=1):
        line = " ".join(raw.split())
        if line:
            result.append((lineno, line))
    return result


def find_clones(files: list[Path], window: int, min_count: int):
    # window-hash → list of (file, idx-into-normalized, orig-lineno)
    hits: dict[str, list[tuple[Path, int, int]]] = defaultdict(list)
    contents: dict[Path, list[tuple[int, str]]] = {}
    for f in files:
        lines = normalized_lines(f)
        contents[f] = lines
        for i in range(len(lines) - window + 1):
            key = hashlib.sha1(
                "\n".join(l for _, l in lines[i : i + window]).encode()
            ).hexdigest()
            hits[key].append((f, i, lines[i][0]))

    dup = {k: v for k, v in hits.items() if len(v) >= min_count}

    # Merge overlapping windows into maximal regions: two windows in the same
    # family chain if EVERY occurrence advances by one line together.
    # Approximation that works well in practice: group by the SET of
    # (file, idx - offset) start signatures.
    families: dict[tuple, dict] = {}
    for key, occs in dup.items():
        sig = tuple(sorted((str(f), i) for f, i, _ in occs))
        # try to attach to an existing family whose signature is sig shifted by -k
        attached = False
        for k in range(1, window + 1):
            shifted = tuple(sorted((f, i - k) for f, i in sig))
            if shifted in families:
                fam = families[shifted]
                fam["length"] = max(fam["length"], window + k)
                attached = True
                break
        if not attached:
            families[sig] = {
                "occs": [(f, i, ln) for f, i, ln in occs],
                "length": window,
            }

    out = []
    for sig, fam in families.items():
        f0, i0, _ = fam["occs"][0]
        excerpt = [l for _, l in contents[f0][i0 : i0 + fam["length"]]]
        anchors = sorted(f"{f}:{ln}" for f, _, ln in fam["occs"])
        mass = len(fam["occs"]) * fam["length"]
        out.append(
            {
                "count": len(fam["occs"]),
                "length": fam["length"],
                "mass": mass,
                "anchors": anchors,
                "excerpt": excerpt,
            }
        )
    out.sort(key=lambda r: -r["mass"])
    return out


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("paths", nargs="*", default=["Bang/"])
    ap.add_argument("--window", type=int, default=5)
    ap.add_argument("--min-count", type=int, default=4)
    ap.add_argument("--top", type=int, default=15)
    args = ap.parse_args()

    files: list[Path] = []
    for p in args.paths or ["Bang/"]:
        path = Path(p)
        if path.is_dir():
            files.extend(sorted(path.rglob("*.lean")))
        elif path.suffix == ".lean":
            files.append(path)
    if not files:
        print("no .lean files found", file=sys.stderr)
        return 2

    fams = find_clones(files, args.window, args.min_count)
    total_mass = sum(f["mass"] for f in fams)
    print(f"clone families ≥{args.min_count}×{args.window} lines: "
          f"{len(fams)}   duplicated mass ≈ {total_mass} normalized lines\n")
    for rank, fam in enumerate(fams[: args.top], start=1):
        print(f"#{rank}  {fam['count']}× {fam['length']} lines  (mass {fam['mass']})")
        for line in fam["excerpt"][:6]:
            print(f"      {line[:110]}")
        if fam["length"] > 6:
            print(f"      … (+{fam['length'] - 6} lines)")
        shown = fam["anchors"][:8]
        print(f"      at: {', '.join(shown)}"
              + (f" … +{len(fam['anchors']) - 8} more" if len(fam["anchors"]) > 8 else ""))
        print()
    return 0


if __name__ == "__main__":
    sys.exit(main())
