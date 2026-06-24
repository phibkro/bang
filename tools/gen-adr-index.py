#!/usr/bin/env python3
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
import re
import sys
from pathlib import Path

DECISIONS = Path(__file__).resolve().parent.parent / "docs" / "decisions"
README = DECISIONS / "README.md"

BEGIN = "<!-- BEGIN GENERATED ADR INDEX — do not edit; run `just adr-index` -->"
END = "<!-- END GENERATED ADR INDEX -->"

# `- **Status**: …`, `- **Status:** …` (colon inside emphasis), `- Status: …`.
# The colon may sit before OR after the closing `**`, so allow `*` on both sides.
FIELD_RE = re.compile(
    r"^\s*[-*]\s*\*{0,2}([A-Za-z][\w -]*?)\*{0,2}\s*:\s*\*{0,2}\s*(.*\S)\s*$"
)
# H1 title, after stripping a leading `ADR-NNNN`/`NNNN` + `·`/`—`/`-` separator.
H1_RE = re.compile(r"^#\s+(.*\S)\s*$")
TITLE_STRIP_RE = re.compile(r"^(?:ADR[- ]?)?\d{4}\s*[·—–-]\s*", re.IGNORECASE)


def norm_key(k: str) -> str:
    """Lowercase, drop spaces/hyphens — so 'Depends-on' == 'Depends on'."""
    return re.sub(r"[ \-]", "", k).lower()


def nums(value: str) -> list[str]:
    """Extract the 4-digit ADR numbers from a field value, in order."""
    return re.findall(r"\b(\d{4})\b", value)


def qnums(value: str) -> list[str]:
    """Extract Q-numbers (Q3, Q19) from a Resolves value, in order."""
    return re.findall(r"\bQ(\d+)\b", value)


SENTINEL = "<!-- adr-frontmatter -->"


def parse_adr(path: Path) -> dict:
    """Parse one ADR's H1 title + its machine-frontmatter block.

    The frontmatter is the contiguous bullet block right after the `<!--
    adr-frontmatter -->` sentinel (terminated by the first blank line after the
    bullets). Reading ONLY this block — not the first matching bullet anywhere —
    keeps the index authoritative: a scoped prose bullet elsewhere (e.g. 0023's
    "Supersedes ADR-0022 **D3**", a partial supersession) never leaks into the
    machine relationships. A missing sentinel is a hard error (flag-before-build).
    """
    num = path.name[:4]
    title = None
    fields: dict[str, str] = {}
    lines = path.read_text(encoding="utf-8").splitlines()

    for line in lines:
        m = H1_RE.match(line)
        if m:
            title = TITLE_STRIP_RE.sub("", m.group(1)).strip()
            break

    if SENTINEL not in lines:
        raise SystemExit(
            f"FAIL: {path.name} has no `{SENTINEL}` frontmatter block.\n"
            f"      Every ADR needs the machine-frontmatter block (run the sweep)."
        )
    start = lines.index(SENTINEL) + 1
    in_bullets = False
    block_end = len(lines)
    for off, line in enumerate(lines[start:]):
        m = FIELD_RE.match(line)
        if m:
            fields[norm_key(m.group(1))] = m.group(2).strip()
            in_bullets = True
        elif line.strip() == "":
            if in_bullets:
                block_end = start + off
                break  # blank line after the bullets ends the frontmatter block
            continue  # blank line(s) between sentinel and first bullet
        else:
            block_end = start + off
            break  # any non-bullet, non-blank line ends the block

    # The prose Status (the human narrative bullet AFTER the block, or a `##
    # Status` section as in 0016) — the second copy of a fact that can drift from
    # the sentinel Status. None if the ADR has no separate prose Status.
    prose_status = None
    for line in lines[block_end:]:
        m = FIELD_RE.match(line)
        if m and norm_key(m.group(1)) == "status":
            prose_status = m.group(2).strip()
            break
    if prose_status is None:
        for i, line in enumerate(lines):
            if line.strip() == "## Status":
                for nxt in lines[i + 1:]:
                    if nxt.strip():
                        prose_status = nxt.strip()
                        break
                break

    return {"num": num, "file": path.name, "title": title,
            "fields": fields, "prose_status": prose_status}


def status_of(fields: dict[str, str]) -> str:
    """First word of Status (so 'Accepted (user-grilled, …)' → 'Accepted')."""
    raw = fields.get("status", "")
    return raw.split()[0].rstrip(".") if raw else "—"


def collect() -> list[dict]:
    adrs = [parse_adr(p) for p in sorted(DECISIONS.glob("[0-9][0-9][0-9][0-9]-*.md"))]
    by_num = {a["num"]: a for a in adrs}

    # Derive inverse links from every ADR's Supersedes / Amends.
    for a in adrs:
        a["superseded_by"] = []
        a["amended_by"] = []
    for a in adrs:
        for tgt in nums(a["fields"].get("supersedes", "")):
            if tgt in by_num:
                by_num[tgt]["superseded_by"].append(a["num"])
        for tgt in nums(a["fields"].get("amends", "")):
            if tgt in by_num:
                by_num[tgt]["amended_by"].append(a["num"])
    return adrs


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
        deps = join_links(nums(f.get("depends-on", "") or f.get("dependson", "")), by_num)
        title = (a["title"] or "—").replace("|", "\\|")
        summary = (f.get("summary", "—")).replace("|", "\\|")
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
# `- [Q19 — …](#…)  · ✓ RESOLVED (ADR-0040)` — the index line + its status marker.
Q_INDEX_RE = re.compile(r"^- \[Q(\d+)\b.*?\]\([^)]*\)(?:\s*·\s*(.*))?$")


def parse_open_questions() -> dict[int, dict]:
    """Map Qn → {'resolved': bool, 'partial': bool, 'adrs': [nums]} from the index."""
    out: dict[int, dict] = {}
    for line in OPEN_QUESTIONS.read_text(encoding="utf-8").splitlines():
        m = Q_INDEX_RE.match(line)
        if not m:
            continue
        q = int(m.group(1))
        marker = (m.group(2) or "").strip()
        resolved = "✓ RESOLVED" in marker
        partial = marker.startswith("◑") or "PARTIAL" in marker
        # ADR nums named in the marker — but only when the marker claims a resolution.
        adrs = nums(marker) if (resolved or partial) else []
        out[q] = {"resolved": resolved, "partial": partial, "adrs": adrs}
    return out


def status_word(raw: str | None) -> str | None:
    """First word of a Status value, normalized — 'Accepted (…)' → 'accepted'."""
    return raw.split()[0].rstrip(".").lower() if raw else None


def status_consistency_check(adrs: list[dict]) -> list[str]:
    """Each ADR carries Status twice (sentinel frontmatter + prose narrative).
    They must agree on the first status word, else the two copies have drifted
    (e.g. an Accepted→Superseded flip applied to one but not the other)."""
    errs: list[str] = []
    for a in adrs:
        sentinel = status_word(a["fields"].get("status"))
        prose = status_word(a.get("prose_status"))
        if prose is None:
            continue  # no second copy → nothing to drift against
        if sentinel != prose:
            errs.append(
                f"{a['num']}: sentinel Status `{sentinel}` ≠ prose Status "
                f"`{prose}` ({a['file']}). Reconcile the two copies."
            )
    return errs


def crossref_check(adrs: list[dict]) -> list[str]:
    """The Q ⟺ ADR bidirectional check (catches the Q19 drift). Returns errors."""
    errs: list[str] = []
    qmap = parse_open_questions()

    # ADR `Resolves: Qn` → Qn declared per ADR.
    adr_resolves: dict[int, list[str]] = {}
    for a in adrs:
        for q in qnums(a["fields"].get("resolves", "")):
            adr_resolves.setdefault(int(q), []).append(a["num"])

    # (1) Forward: every ADR named in a ✓-RESOLVED marker must declare Resolves: Qn.
    for q, info in qmap.items():
        if not info["resolved"]:
            continue
        for adr in info["adrs"]:
            if adr not in adr_resolves.get(q, []):
                errs.append(
                    f"Q{q}: OPEN_QUESTIONS marks it RESOLVED by ADR-{adr}, but "
                    f"{adr}-*.md does not declare `Resolves: Q{q}`."
                )

    # (2) Reverse: every ADR `Resolves: Qn` ⟹ Qn is NOT marked OPEN in the ledger.
    #     This is the Q19 leg — an ADR claims a resolution the ledger still calls OPEN.
    for q, decl_adrs in adr_resolves.items():
        info = qmap.get(q)
        if info is None:
            errs.append(
                f"Q{q}: declared resolved by {', '.join(decl_adrs)}, but Q{q} is "
                f"absent from OPEN_QUESTIONS.md."
            )
        elif not (info["resolved"] or info["partial"]):
            errs.append(
                f"Q{q}: declared resolved by {', '.join(decl_adrs)}, but "
                f"OPEN_QUESTIONS.md still marks Q{q} as OPEN. Flip its status marker."
            )
    return errs


def splice(readme_text: str, generated: str) -> str:
    """Replace the BEGIN..END region; if absent, append it after the preamble."""
    if BEGIN in readme_text and END in readme_text:
        pre = readme_text[: readme_text.index(BEGIN)]
        post = readme_text[readme_text.index(END) + len(END):]
        return pre + generated + post
    # First run: append to the end, preserving all hand-written content above.
    sep = "" if readme_text.endswith("\n\n") else ("\n" if readme_text.endswith("\n") else "\n\n")
    return readme_text + sep + generated + "\n"


def main() -> int:
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
            print("      Run `just adr-index` to regenerate. Diff (current → expected):")
            diff = difflib.unified_diff(
                current.splitlines(), new.splitlines(),
                fromfile="README.md (committed)", tofile="README.md (regenerated)",
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
