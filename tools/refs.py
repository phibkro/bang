#!/usr/bin/env python3
"""refs.py — the reference library as a generated, queried, tested derivation.

`references/refs.bib` is the SINGLE SOURCE OF TRUTH. Everything else is derived:

  build   parse refs.bib + scan papers/ → references/index.json (the queryable
          artifact) + regenerate the generated block in references/README.md.
          hop/ondisk/sha256 are AUTO-derived (filesystem facts, never hand-typed);
          topic/grounds/role are the only manual facets, in a bib `keywords` field.
  check   the fitness rung (sibling of check-refs.py): every PDF has a key; every
          `grounds:ADR-NNNN` names a real ADR; every Lean `-- shape: <stem>` cite
          resolves to a key; every pinned `sha256` matches the file on disk.
  query   the loogle analog: `refs.py query capability-escape` greps the facets
          (key/title/topic/grounds) → key · hop · title · path, cheap retrieval
          without loading the whole README prose into context.

Zero dependencies (stdlib only), exactly like check-refs.py — the bibtex parse is a
brace-balanced hand-roll, robust to nested `{{POPL}}` and multi-line fields.

Facet schema (a bib `keywords = {...}` field, space/comma-separated `facet:value`):
  topic:<slug>     cross-cutting concern (capability-safety, graded-types,
                   calculation, lr, wasmfx, stm, effect-algebra, proof-discipline…)
  grounds:ADR-NNNN the decision this paper grounds   (validated against docs/decisions/)
  grounds:task-NN  the task it serves                 (not validated — tasks are ephemeral)
  grounds:inv-N    the invariant it grounds
  role:<slug>      substrate | confirmed-sota | frontier | speculative | off-topic
Auto-derived (NEVER in keywords): hop (papers/<hop>/), ondisk (file exists),
  sha256 (computed), venue/year (from the entry type/fields).
"""
import hashlib
import json
import os
import re
import subprocess
import sys

ROOT = os.path.abspath(os.environ.get("REFS_ROOT", "."))
BIB = os.path.join(ROOT, "references/refs.bib")
PAPERS = os.path.join(ROOT, "references/papers")
INDEX = os.path.join(ROOT, "references/index.json")
README = os.path.join(ROOT, "references/README.md")
DECISIONS = os.path.join(ROOT, "docs/decisions")

GEN_BEGIN = "<!-- BEGIN GENERATED refs-index (just refs-index) — do not hand-edit -->"
GEN_END = "<!-- END GENERATED refs-index -->"

# A `-- shape: <stem>` token is paper-like (validate it) iff it carries a venue tag
# or a multi-hyphen author-venue shape; bare words (`shape: scratch/…`, `shape: the`)
# are not paper citations and are skipped.
VENUE_RE = re.compile(r"(popl|icfp|oopsla|pldi|esop|fscd|lics|jfp|haskell|mfps|csl|toplas|ppopp|concur|itp|cade)\d{2}")


# ── bibtex parse (brace-balanced, stdlib only) ──────────────────────────────

def parse_bib(text):
    """Yield entry dicts: {key, type, fields:{lower→raw}, keywords:[facet:value]}."""
    entries = []
    i, n = 0, len(text)
    while i < n:
        at = text.find("@", i)
        if at < 0:
            break
        m = re.match(r"@(\w+)\s*\{\s*([^,\s]+)\s*,", text[at:])
        if not m:
            i = at + 1
            continue
        etype, key = m.group(1).lower(), m.group(2)
        # find the brace-balanced body
        body_start = at + m.end() - 1  # points at the comma; scan from the '{'
        depth, j = 0, at + len(f"@{m.group(1)}")
        while j < n and text[j] != "{":
            j += 1
        start = j
        depth = 0
        while j < n:
            if text[j] == "{":
                depth += 1
            elif text[j] == "}":
                depth -= 1
                if depth == 0:
                    break
            j += 1
        body = text[start + 1:j]
        fields = parse_fields(body)
        kw = fields.get("keywords", "")
        facets = re.split(r"[,\s]+", kw.strip()) if kw.strip() else []
        entries.append({"key": key, "type": etype, "fields": fields,
                        "keywords": [f for f in facets if ":" in f]})
        i = j + 1
    return entries


def parse_fields(body):
    """field = {value} | field = "value" | field = bareword, brace-balanced."""
    fields, i, n = {}, 0, len(body)
    # drop the leading `key,` already consumed by caller; body begins after first comma
    body = body[body.find(",") + 1:] if "," in body else body
    i, n = 0, len(body)
    while i < n:
        m = re.match(r"\s*(\w+)\s*=\s*", body[i:])
        if not m:
            break
        name = m.group(1).lower()
        i += m.end()
        if i >= n:
            break
        if body[i] == "{":
            depth, j = 0, i
            while j < n:
                if body[j] == "{":
                    depth += 1
                elif body[j] == "}":
                    depth -= 1
                    if depth == 0:
                        break
                j += 1
            val = body[i + 1:j]
            i = j + 1
        elif body[i] == '"':
            j = body.find('"', i + 1)
            val = body[i + 1:j]
            i = j + 1
        else:
            j = i
            while j < n and body[j] not in ",\n":
                j += 1
            val = body[i:j].strip()
            i = j
        fields[name] = " ".join(val.split())  # collapse internal whitespace
        # advance past trailing comma
        while i < n and body[i] in ", \n\t":
            i += 1
    return fields


# ── filesystem facts ────────────────────────────────────────────────────────

def pdf_map():
    """stem → relative path for every PDF under papers/."""
    out = {}
    for dp, _, files in os.walk(PAPERS):
        for f in files:
            if f.endswith(".pdf"):
                out[f[:-4]] = os.path.relpath(os.path.join(dp, f), ROOT)
    return out


def sha256(path):
    h = hashlib.sha256()
    with open(os.path.join(ROOT, path), "rb") as fh:
        for chunk in iter(lambda: fh.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


def hop_of(path):
    # references/papers/<hop>/file.pdf
    parts = path.split(os.sep)
    try:
        return parts[parts.index("papers") + 1] if path.endswith(".pdf") else None
    except (ValueError, IndexError):
        return None


def build_index():
    text = open(BIB, encoding="utf-8").read()
    entries = parse_bib(text)
    pdfs = pdf_map()
    index = []
    for e in entries:
        key = e["key"]
        path = pdfs.get(key)
        rec = {
            "key": key,
            "title": e["fields"].get("title", "").replace("{", "").replace("}", ""),
            "year": e["fields"].get("year", ""),
            "doi": e["fields"].get("doi", ""),
            "eprint": e["fields"].get("eprint", ""),
            "topics": [f.split(":", 1)[1] for f in e["keywords"] if f.startswith("topic:")],
            "grounds": [f.split(":", 1)[1] for f in e["keywords"] if f.startswith("grounds:")],
            "role": next((f.split(":", 1)[1] for f in e["keywords"] if f.startswith("role:")), ""),
            "ondisk": path is not None,
            "hop": hop_of(path) if path else None,
            "path": path,
            "sha256_pinned": e["fields"].get("sha256", ""),
        }
        index.append(rec)
    return entries, index


# ── subcommands ─────────────────────────────────────────────────────────────

def render(index):
    """Pure: (index) → (index.json text, README summary block). Shared by build + check
    so the committed derivations can't drift from refs.bib (the `gen-adr-index --check` move)."""
    index = sorted(index, key=lambda r: (r["hop"] or "~", r["key"]))
    json_text = json.dumps(index, indent=2, ensure_ascii=False) + "\n"

    def fmt(counter):
        return ", ".join(f"{k} ({n})" for k, n in sorted(counter.items(), key=lambda x: -x[1])) or "—"

    on = sum(1 for r in index if r["ondisk"])
    tagged = sum(1 for r in index if r["topics"] or r["grounds"])
    topics, roles, hops = {}, {}, {}
    for r in index:
        for t in r["topics"]:
            topics[t] = topics.get(t, 0) + 1
        if r["role"]:
            roles[r["role"]] = roles.get(r["role"], 0) + 1
        if r["hop"]:
            hops[r["hop"]] = hops.get(r["hop"], 0) + 1
    # COMPACT SUMMARY only — the full records live in index.json + `just refs <q>`;
    # dumping 72 rows here would re-bloat the prose the whole design exists to avoid.
    block = "\n".join([
        GEN_BEGIN,
        f"_Generated by `tools/refs.py build`. **{len(index)}** entries · **{on}** on-disk · "
        f"**{tagged}** facet-tagged. Full records: `references/index.json`. Query: `just refs <term>`._",
        "",
        f"- **topics:** {fmt(topics)}",
        f"- **roles:** {fmt(roles)}",
        f"- **on-disk by hop:** {fmt(hops)}",
        GEN_END,
    ])
    return json_text, block


def splice_block(md, block):
    return re.sub(re.escape(GEN_BEGIN) + r".*?" + re.escape(GEN_END), block, md, flags=re.DOTALL)


def cmd_build():
    _, index = build_index()
    json_text, block = render(index)
    open(INDEX, "w", encoding="utf-8").write(json_text)
    if os.path.exists(README):
        md = open(README, encoding="utf-8").read()
        if GEN_BEGIN in md and GEN_END in md:
            open(README, "w", encoding="utf-8").write(splice_block(md, block))
            note = "README block regenerated"
        else:
            note = "README has no GEN markers (skipped; add them to enable)"
    else:
        note = "no README"
    on = sum(1 for r in index if r["ondisk"])
    tagged = sum(1 for r in index if r["topics"] or r["grounds"])
    print(f"built index.json: {len(index)} entries, {on} on-disk, {tagged} tagged "
          f"({len(index) - tagged} untagged). {note}.")
    return 0


def cmd_check():
    entries, index = build_index()
    by_key = {r["key"] for r in index}
    pdfs = pdf_map()
    hard, soft = [], []

    # 1. every PDF has a bib key (no orphan PDFs). A `<stem>-alt` is a documented
    #    sha256-distinct second rendering (README): valid iff its base stem is a key.
    for stem, path in sorted(pdfs.items()):
        base = stem[:-4] if stem.endswith("-alt") else stem
        if base not in by_key:
            hard.append(f"orphan PDF (no bib key): {path}")

    # 2. grounds:ADR-NNNN names a real ADR
    adrs = {f[:4] for f in os.listdir(DECISIONS) if re.match(r"\d{4}-", f)} if os.path.isdir(DECISIONS) else set()
    for r in index:
        for g in r["grounds"]:
            m = re.match(r"ADR-(\d{4})$", g)
            if m and m.group(1) not in adrs:
                hard.append(f"{r['key']}: grounds:{g} names no ADR in docs/decisions/")

    # 3. pinned sha256 matches the file
    for r in index:
        if r["sha256_pinned"]:
            if not r["ondisk"]:
                hard.append(f"{r['key']}: sha256 pinned but no PDF on disk")
            elif sha256(r["path"]) != r["sha256_pinned"]:
                hard.append(f"{r['key']}: sha256 MISMATCH (file != pinned)")

    # 4. every Lean `-- shape: <stem>` paper-cite resolves to a key (prefix match)
    lean = subprocess.run(["git", "ls-files", "*.lean"], cwd=ROOT, capture_output=True, text=True).stdout.split()
    cite_re = re.compile(r"shape:\s*([a-z][a-z0-9./-]+)")
    for f in lean:
        for ln, line in enumerate(open(os.path.join(ROOT, f), errors="replace"), 1):
            for m in cite_re.finditer(line):
                stem = m.group(1).rstrip(".")
                if stem.startswith("scratch") or "/" in stem or not VENUE_RE.search(stem):
                    continue  # non-paper shape (scratch file, prose, module)
                if not any(k.startswith(stem) for k in by_key):
                    hard.append(f"{f}:{ln}: `shape: {stem}` resolves to no bib key")

    # 5. the committed derivations must match a fresh render (drift = stale; the
    #    gen-adr-index --check move applied to index.json + the README block).
    json_text, block = render(index)
    if not os.path.exists(INDEX) or open(INDEX, encoding="utf-8").read() != json_text:
        hard.append("references/index.json is stale or missing — run `just refs-index`")
    if os.path.exists(README):
        md = open(README, encoding="utf-8").read()
        if GEN_BEGIN in md and splice_block(md, block) != md:
            hard.append("references/README.md generated block is stale — run `just refs-index`")

    # 6. soft: entries with no facet tags (incremental — warn, don't fail)
    for r in index:
        if not (r["topics"] or r["grounds"] or r["role"]):
            soft.append(f"{r['key']}: untagged (no topic/grounds/role)")

    print("── check-bib (refs.bib fitness) ──")
    for s in soft:
        print(f"  warn  {s}")
    if soft:
        print(f"  ({len(soft)} untagged — incremental, not a failure)")
    if not hard:
        print(f"PASS: {len(index)} entries; {len(pdfs)} PDFs all keyed; "
              f"ADR/sha256/Lean-cite references all resolve.")
        return 0
    for h in hard:
        print(f"FAIL  {h}")
    print(f"FAIL: {len(hard)} hard error(s).")
    return 1


def cmd_query(q):
    _, index = build_index()
    ql = q.lower()
    hits = [r for r in index if ql in r["key"].lower() or ql in r["title"].lower()
            or any(ql in t for t in r["topics"]) or any(ql in g.lower() for g in r["grounds"])]
    if not hits:
        print(f"no refs match '{q}'")
        return 0
    for r in sorted(hits, key=lambda r: (r["hop"] or "~", r["key"])):
        loc = r["path"] or "(bib-only)"
        facets = " ".join(r["topics"] + r["grounds"])
        print(f"{r['key']}\n    {r['title']}\n    {loc}  [{facets}]")
    print(f"\n{len(hits)} match(es).")
    return 0


def main():
    args = sys.argv[1:]
    if not args or args[0] == "build":
        return cmd_build()
    if args[0] == "check":
        return cmd_check()
    if args[0] == "query" and len(args) > 1:
        return cmd_query(" ".join(args[1:]))
    print("usage: refs.py [build | check | query <term>]", file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main())
