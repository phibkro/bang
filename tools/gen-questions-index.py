#!/usr/bin/env python3
# tool: role=gen couples=docs/notes/questions/*.md,docs/notes/OPEN_QUESTIONS.md,genblock.py runs-in=fitness
"""gen-questions-index.py — the design-question ledger, generated from the OKF files.

`docs/notes/questions/*.md` is a flat folder of one-question-per-file notes, each
carrying OKF-shaped frontmatter (`type`/`title`/`description` + `status`/`area`/`ties`,
optional `resolved-by`). This renders `docs/notes/OPEN_QUESTIONS.md` — the canonical,
agent-visible ledger CLAUDE.md points at — as a MULTI-VIEW index over those files:

  1. **By area**   — grouped type-system/effects/surface/tooling/meta (title · description
                     · status · ties): the human reading view.
  2. **By status** — open / partial / decided / superseded: what's live vs closed at a
                     glance. These rows ALSO carry the `✓ RESOLVED (ADR-…)` / `◑ PARTIAL`
                     markers that `gen-adr-index.py` reads to enforce the Q⟺ADR bijection —
                     so a question's resolution lives in ONE place (its frontmatter) and
                     flows to both ledgers.
  3. **Tie graph** — a mermaid graph of the `ties` edges.

The whole file is a pure function of the question files + their frontmatter — it cannot
drift (the ADR-ledger / gen-notes-index pattern applied to the question ledger). The POINT
of the structure is VALIDATED EDGES: every `ties:` entry must name a real question file
(`Q<N>-…md`) or a real ADR (`docs/decisions/`). A dangling tie is a `sys.exit` (`see-also`
is freeform, NOT validated).

  gen-questions-index.py           # regenerate docs/notes/OPEN_QUESTIONS.md
  gen-questions-index.py --check   # exit 1 if it is stale (round-trip gate, for fitness)
"""
import os
import re
import sys

from genblock import validate_mermaid  # reuse the import-graph mermaid compile-check

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
QDIR = os.path.join(ROOT, "docs", "notes", "questions")
DECISIONS = os.path.join(ROOT, "docs", "decisions")
OUT = os.path.join(ROOT, "docs", "notes", "OPEN_QUESTIONS.md")

AREA_ORDER = ["type-system", "effects", "surface", "tooling", "meta"]
STATUS_ORDER = ["open", "partial", "decided", "superseded"]
REQUIRED = ["type", "title", "description", "status", "area", "ties", "see-also"]

# The stable, hand-written preamble (a constant so regeneration reproduces it byte-for-byte).
PREAMBLE = """\
> **The design-question ledger — deferred design decisions (PROJECT / NEXT docs).**
> These are contributor-facing questions about where the *language* goes next: forks that
> surfaced during work and were intentionally deferred, not bugs and not in-flight tasks
> (those live in GitHub Issues · `CONTEXT.md` · `paths/`). A question with an ADR is
> **closed** — its resolution is recorded here (status `decided`) and in that ADR.
>
> One file per question under `docs/notes/questions/` (OKF-shaped: `type`/`title`/
> `description` frontmatter + `status`/`area`/`ties`, optional `resolved-by`). This file
> is GENERATED from those files by `tools/gen-questions-index.py` — three views over the
> same frontmatter, so they cannot drift. `ties` edges are VALIDATED (a tie to a
> nonexistent question/ADR fails the generator); `see-also` is freeform.
>
> **Add a question:** drop a `Q<N>-<slug>.md` in `docs/notes/questions/` (copy an existing
> one), then `just questions-index`. Discipline (`docs/notes/spec-proof-discipline.md`):
> never silently mutate a theorem/definition to dodge a question — record it here instead."""


def parse_frontmatter(text, path):
    m = re.match(r"---\n(.*?)\n---\n", text, re.DOTALL)
    if not m:
        sys.exit(f"gen-questions-index: {path} has no `---`-delimited frontmatter.")
    fm = {}
    for line in m.group(1).splitlines():
        if not line.strip():
            continue
        km = re.match(r"([\w-]+):\s*(.*)$", line)
        if not km:
            sys.exit(f"gen-questions-index: malformed frontmatter line in {path}: {line!r}")
        key, val = km.group(1), km.group(2).strip()
        if val.startswith("[") and val.endswith("]"):
            inner = val[1:-1].strip()
            fm[key] = [x.strip().strip('"').strip("'") for x in inner.split(",")] if inner else []
        else:
            fm[key] = val.strip('"').strip("'")
    missing = [k for k in REQUIRED if k not in fm]
    if missing:
        sys.exit(f"gen-questions-index: {path} frontmatter missing {missing}.")
    if fm["area"] not in AREA_ORDER:
        sys.exit(f"gen-questions-index: {path} has unknown area {fm['area']!r} "
                 f"(taxonomy: {AREA_ORDER}).")
    if fm["status"] not in STATUS_ORDER:
        sys.exit(f"gen-questions-index: {path} has unknown status {fm['status']!r} "
                 f"(taxonomy: {STATUS_ORDER}).")
    fm.setdefault("resolved-by", [])
    return fm


def load_questions():
    """[(qid, frontmatter)] sorted by qid, from docs/notes/questions/Q*.md."""
    out = []
    for fn in sorted(os.listdir(QDIR)):
        if not re.match(r"Q\d+-.*\.md$", fn):
            continue
        qid = re.match(r"(Q\d+)-", fn).group(1)
        fm = parse_frontmatter(open(os.path.join(QDIR, fn), encoding="utf-8").read(),
                               f"docs/notes/questions/{fn}")
        fm["_file"] = fn
        fm["_slug"] = re.match(r"Q\d+-(.*)\.md$", fn).group(1)
        out.append((qid, fm))
    out.sort(key=lambda p: int(p[0][1:]))
    return out


def valid_ids(questions):
    """The set of link targets a tie may point at: question file Q-ids ∪ ADR-ids."""
    ids = {qid for qid, _ in questions}
    for fn in os.listdir(DECISIONS):
        dm = re.match(r"(\d{4})-.*\.md$", fn)
        if dm:
            ids.add(f"ADR-{dm.group(1)}")
    return ids


def node_id(link):
    return link.replace("-", "_")


def marker(fm):
    """The resolution marker gen-adr-index reads (Q⟺ADR bijection). Derived from
    status + resolved-by so the resolution has ONE home (the question's frontmatter)."""
    rby = fm.get("resolved-by", [])
    tail = f" ({' + '.join(rby)})" if rby else ""
    head = {"open": "OPEN", "partial": "◑ PARTIAL", "decided": "✓ RESOLVED",
            "superseded": "SUPERSEDED"}[fm["status"]]
    return head + (tail if fm["status"] != "open" else "")


def render(questions):
    label_short = {qid: fm["_slug"] for qid, fm in questions}

    def target_label(link):
        if link.startswith("ADR-"):
            return link
        if link in label_short:
            return f"{link} · {label_short[link]}"
        return link

    L = ["<!-- note-status: active -->",
         "<!-- GENERATED by tools/gen-questions-index.py — do not hand-edit. Regenerate with "
         "`just questions-index`; `--check` gates it in `just fitness`. -->",
         "",
         "# Open questions — the design-question ledger",
         "",
         "<!-- PREAMBLE:START (hand-written, stable) -->",
         PREAMBLE,
         "<!-- PREAMBLE:END -->",
         ""]

    # ── View 1: by area (the human reading view) ──
    L.append("## By area")
    L.append("")
    by_area = {a: [] for a in AREA_ORDER}
    for qid, fm in questions:
        by_area[fm["area"]].append((qid, fm))
    for area in AREA_ORDER:
        rows = by_area[area]
        if not rows:
            continue
        L.append(f"### {area} ({len(rows)})")
        L.append("")
        for qid, fm in sorted(rows, key=lambda p: int(p[0][1:])):
            ties = ", ".join(fm["ties"]) if fm["ties"] else "—"
            L.append(f"- **[{qid} — {fm['title']}]({fm['_file']})** — {fm['description']} "
                     f"· _{fm['status']}_  ")
            L.append(f"  ties: {ties}")
        L.append("")

    # ── View 2: by status (live-vs-closed + the machine-readable resolution markers) ──
    L.append("## By status")
    L.append("")
    L.append("The `· ✓ RESOLVED (ADR-…)` / `· ◑ PARTIAL` markers below are the Q⟺ADR ledger "
             "`gen-adr-index.py` reads —")
    L.append("derived from each question's `resolved-by` frontmatter, so a resolution has a "
             "single home.")
    L.append("")
    by_status = {}
    for qid, fm in questions:
        by_status.setdefault(fm["status"], []).append((qid, fm))
    for status in STATUS_ORDER:
        rows = by_status.get(status, [])
        if not rows:
            continue
        L.append(f"### {status} ({len(rows)})")
        L.append("")
        for qid, fm in sorted(rows, key=lambda p: int(p[0][1:])):
            L.append(f"- [{qid} — {fm['title']}]({fm['_file']})  · {marker(fm)}")
        L.append("")

    # ── View 3: the tie graph ──
    L.append("## Tie graph")
    L.append("")
    L.append("Nodes = questions (`Q<N> · slug`) + their tie targets (other questions, ADRs). An")
    L.append("edge `A --> B` reads \"A ties B\". Generated from the `ties:` frontmatter; a dangling")
    L.append("edge fails generation, so every arrow resolves to a real question or ADR.")
    L.append("")
    L.append("```mermaid")
    L.append("graph LR")
    emitted = set()

    def emit_node(link, cls):
        if link in emitted:
            return
        emitted.add(link)
        L.append(f'  {node_id(link)}["{target_label(link)}"]:::{cls}')

    for qid, fm in questions:
        emit_node(qid, "q")
    for qid, fm in questions:
        for t in fm["ties"]:
            emit_node(t, "adr" if t.startswith("ADR-") else "extq")
    for qid, fm in questions:
        for t in fm["ties"]:
            L.append(f"  {node_id(qid)} --> {node_id(t)}")
    L.append("  classDef q fill:#dbeafe,stroke:#2563eb,color:#1e3a8a;")
    L.append("  classDef extq fill:#eef2ff,stroke:#6366f1,color:#312e81;")
    L.append("  classDef adr fill:#f1f5f9,stroke:#64748b,color:#334155;")
    L.append("```")
    L.append("")
    return "\n".join(L)


def main():
    try: __import__("subprocess").run(["bash", __import__("os").path.join(__import__("os").path.dirname(__file__), "tool-log.sh"), __import__("os").path.basename(__file__)], check=False)  # tool-log (plan 012)
    except Exception: pass
    args = sys.argv[1:]
    questions = load_questions()
    if not questions:
        sys.exit("gen-questions-index: no Q*.md files in docs/notes/questions/.")
    ids = valid_ids(questions)

    # EDGE VALIDATION — the point of the whole thing.
    dangling = []
    for qid, fm in questions:
        for t in fm["ties"]:
            if t not in ids:
                dangling.append((qid, t))
    if dangling:
        print("── gen-questions-index (edge validation) ──")
        for qid, t in dangling:
            print(f"  DANGLING TIE: {qid} ties {t!r} — no such question or ADR.")
        sys.exit(1)

    content = render(questions)

    if "--check" in args:
        cur = open(OUT, encoding="utf-8").read() if os.path.exists(OUT) else ""
        if cur != content:
            print("── gen-questions-index ──")
            print("FAIL: docs/notes/OPEN_QUESTIONS.md is stale — run `just questions-index`.")
            return 1
        status, msg = validate_mermaid(content)
        print(f"questions-index: OK — OPEN_QUESTIONS.md ≡ the question files. "
              f"(mermaid: {status} — {msg})")
        return 1 if status == "fail" else 0

    # build: compile the mermaid before persisting — never write a broken graph
    status, msg = validate_mermaid(content)
    if status == "fail":
        print(f"── gen-questions-index ──\nFAIL: mermaid does not compile (NOT written):\n{msg}")
        return 1
    open(OUT, "w", encoding="utf-8").write(content)
    tail = "mermaid compiles ✓" if status == "pass" else f"(compile-check {status})"
    print(f"questions-index: wrote docs/notes/OPEN_QUESTIONS.md ({len(questions)} questions). {tail}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
