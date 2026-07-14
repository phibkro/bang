#!/usr/bin/env python3
# tool: role=gen couples=adr_facts.py,docs/decisions/*.md,docs/decisions/README.md,docs/notes/OPEN_QUESTIONS.md runs-in=fitness
"""gen-adr-index.py — generate the ADR decided-ledger from per-ADR frontmatter.

The ledger (the index table + the resolved-questions table in
docs/decisions/README.md) is a pure function of the frontmatter blocks in each
docs/decisions/NNNN-*.md. Hand-maintaining it lets it drift from the ADRs (the
SoT); generating it makes drift unrepresentable (the generate>test>convention
ladder, CLAUDE.md "Single source of truth").

Frontmatter schema — a bullet block right after the `# … NNNN … Title` H1:

    - **Status**: Accepted | Proposed | Superseded | Deprecated
    - **Summary**: <one line — the index needs this>
    - **Supersedes**: 0003, 0004      (omit if none)
    - **Amends**: 0026                (omit if none)
    - **Resolves**: Q19, Q15          (design-question numbers; omit if none)
    - **Depends-on**: 0016, 0027      (omit if none)

Inverse links (Superseded-by / Amended-by) are NOT declared — they are DERIVED
here from other ADRs' Supersedes/Amends. Field-key matching is lenient: the
`**`/`*` emphasis, surrounding spaces, a trailing `:` inside or outside the
emphasis, and `-`/` ` in the key (`Depends-on` ~ `Depends on`) are all
normalised away, so the long-standing prose bullets (`- **Status:** …`,
`- **Depends on:** …`) parse without a mechanical rewrite of every ADR.

Usage:
    gen-adr-index.py            # rewrite the generated region in README.md
    gen-adr-index.py --check    # exit 1 on any of: a stale region, a Q⟺ADR
                                # `Resolves:` mismatch, or a Status drift between
                                # an ADR's sentinel frontmatter and its prose bullet
"""

from __future__ import annotations

import argparse
import difflib
import sys
from pathlib import Path

from adr_facts import (
    collect as collect_adr_facts,
    crossref_check as check_crossrefs,
    nums,
    qnums,
    status_consistency_check,
    status_of,
)

DECISIONS = Path(__file__).resolve().parent.parent / "docs" / "decisions"
README = DECISIONS / "README.md"

BEGIN = "<!-- BEGIN GENERATED ADR INDEX — do not edit; run `just adr-index` -->"
END = "<!-- END GENERATED ADR INDEX -->"


def collect() -> list[dict]:
    return collect_adr_facts(DECISIONS)


def link(num: str, by_num: dict) -> str:
    a = by_num.get(num)
    return f"[{num}]({a['file']})" if a else num


def join_links(numbers, by_num) -> str:
    return ", ".join(link(n, by_num) for n in numbers) if numbers else "—"


def render(adrs: list[dict]) -> str:
    by_num = {a["num"]: a for a in adrs}
    out = [BEGIN, ""]
    out.append(
        "| # | Status | Title | Summary | Supersedes / Superseded-by | "
        "Amends / Amended-by | Resolves | Depends-on |"
    )
    out.append("|---|---|---|---|---|---|---|---|")
    for a in adrs:
        f = a["fields"]
        sup = join_links(nums(f.get("supersedes", "")), by_num)
        sup_by = join_links(a["superseded_by"], by_num)
        am = join_links(nums(f.get("amends", "")), by_num)
        am_by = join_links(a["amended_by"], by_num)
        resolves = ", ".join(f"Q{q}" for q in qnums(f.get("resolves", ""))) or "—"
        deps = join_links(
            nums(f.get("depends-on", "") or f.get("dependson", "")), by_num
        )
        title = (a["title"] or "—").replace("|", "\\|")
        summary = (a["field_heads"].get("summary", "—")).replace("|", "\\|")
        out.append(
            f"| [{a['num']}]({a['file']}) | {status_of(f)} | {title} | {summary} "
            f"| {sup} / {sup_by} | {am} / {am_by} | {resolves} | {deps} |"
        )

    # Resolved-questions table: Q → resolving ADR(s).
    q_to_adrs: dict[int, list[str]] = {}
    for a in adrs:
        for q in qnums(a["fields"].get("resolves", "")):
            q_to_adrs.setdefault(int(q), []).append(a["num"])
    out.append("")
    out.append("### Resolved questions (derived from ADR `Resolves:` fields)")
    out.append("")
    out.append("| Question | Resolved by |")
    out.append("|---|---|")
    for q in sorted(q_to_adrs):
        resolving = ", ".join(link(n, by_num) for n in sorted(q_to_adrs[q]))
        out.append(f"| Q{q} | {resolving} |")

    out.append("")
    out.append(END)
    return "\n".join(out)


OPEN_QUESTIONS = DECISIONS.parent / "notes" / "OPEN_QUESTIONS.md"


def crossref_check(adrs: list[dict]) -> list[str]:
    return check_crossrefs(adrs, OPEN_QUESTIONS)


def splice(readme_text: str, generated: str) -> str:
    """Replace the BEGIN..END region; if absent, append it after the preamble."""
    if BEGIN in readme_text and END in readme_text:
        pre = readme_text[: readme_text.index(BEGIN)]
        post = readme_text[readme_text.index(END) + len(END) :]
        return pre + generated + post
    # First run: append to the end, preserving all hand-written content above.
    sep = (
        ""
        if readme_text.endswith("\n\n")
        else ("\n" if readme_text.endswith("\n") else "\n\n")
    )
    return readme_text + sep + generated + "\n"


def main() -> int:
    try:
        __import__("subprocess").run(
            [
                "bash",
                __import__("os").path.join(
                    __import__("os").path.dirname(__file__), "tool-log.sh"
                ),
                __import__("os").path.basename(__file__),
            ],
            check=False,
        )  # tool-log (plan 012)
    except Exception:
        pass
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--check", action="store_true", help="exit 1 if README is stale")
    args = ap.parse_args()

    adrs = collect()
    generated = render(adrs)
    current = README.read_text(encoding="utf-8")
    new = splice(current, generated)

    if args.check:
        rc = 0
        if new != current:
            print("FAIL: docs/decisions/README.md generated region is STALE.")
            print(
                "      Run `just adr-index` to regenerate. Diff (current → expected):"
            )
            diff = difflib.unified_diff(
                current.splitlines(),
                new.splitlines(),
                fromfile="README.md (committed)",
                tofile="README.md (regenerated)",
                lineterm="",
            )
            print("\n".join(diff))
            rc = 1
        errs = crossref_check(adrs)
        if errs:
            print("FAIL: OPEN_QUESTIONS ⟺ ADR `Resolves:` cross-reference drift:")
            for e in errs:
                print(f"       {e}")
            rc = 1
        serrs = status_consistency_check(adrs)
        if serrs:
            print("FAIL: ADR Status drift (sentinel frontmatter ≠ prose narrative):")
            for e in serrs:
                print(f"       {e}")
            rc = 1
        if rc == 0:
            print("adr-index: OK — README current + Q⟺ADR + Status copies consistent.")
        return rc

    README.write_text(new, encoding="utf-8")
    print(f"adr-index: wrote {README} ({len(adrs)} ADRs).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
