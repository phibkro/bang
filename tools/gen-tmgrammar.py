#!/usr/bin/env python3
# tool: role=gen couples=Bang/Frontend/Surface.lean,web/docs/bang.tmLanguage.json runs-in=fitness
"""Generate web/docs/bang.tmLanguage.json — a TextMate grammar DERIVED from the reified parser tables.

Single source of truth (the generate rung of the derivation ladder):
  • Bang/Frontend/Surface.lean — the SAME reified tables the parser consults:
      - `keywordRule`  → keyword-led constructs (`if`/`handle`/`state`/…)   [via gen-reference.extract_keyword_rules]
      - `opInfo`       → operators (`+`/`-`/`==`/…)                          [via gen-reference.extract_op_table]
      - `pIdent`'s reserved list → the reserved binder words (`get`/`put`/`new`/`resume`/`param`/…)
      - the effect-channel labels (`throws`/`state`/`stm`/`Div`)            [via gen-reference.extract_labels]
    A grammar generated from these tables cannot drift from what the parser recognises — the same
    move gen-reference.py already makes for the reference DOCS, now for editor highlighting.

The HAND-WRITTEN RESIDUE (kept as explicit constants below, INSIDE the generator, because it is
lexical structure the reified rule/op tables do not carry): `--` line comments (issue #62), string
literals, number literals, and the effect/handler block punctuation (`{` `}` `(` `)` `,` `;`).

Real linguist/GitHub registration is POST-ADOPTION (a linguist PR is an outward action, operator's
button) — this grammar drives editor/site highlighting (Shiki, tree-sitter's TextMate consumers,
the slice-4 VS Code extension), NOT per-repo GitHub rendering.

Usage:  gen-tmgrammar.py            regenerate web/docs/bang.tmLanguage.json
        gen-tmgrammar.py --check    exit 1 if the committed grammar != the regenerated one (fitness leg)
"""
import json
import os
import re
import subprocess
import sys
import pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
import importlib.util

_spec = importlib.util.spec_from_file_location("gen_reference", ROOT / "tools/gen-reference.py")
_gr = importlib.util.module_from_spec(_spec)
# gen-reference's module-level code is import-safe (no side effects until main()).
_spec.loader.exec_module(_gr)

SURFACE = ROOT / "Bang/Frontend/Surface.lean"
OUT = ROOT / "web/docs/bang.tmLanguage.json"

# ── Hand-written lexical residue (NOT in the reified tables) ──
# TextMate regexes for the lexical layer the rule/op tables don't carry.
LINE_COMMENT = "--.*$"          # issue #62: `--` runs to end-of-line, maximal-munch over `-`/`->`
STRING_PATTERN = r'"'           # string opens on `"`; the JSON rule captures the body + escapes
NUMBER_PATTERN = r"\b-?\d+\b"   # integer literals (Int is unbounded ℤ, ADR-0067)
PUNCTUATION = r"[{}(),;]"       # effect/handler/tuple block punctuation


def extract_reserved_binders(text):
    """The reserved words `pIdent` rejects at a binder position — the identifier keywords the
    parser will not let you bind. Extracted from `pIdent`'s own `t = "…"` chain (never hand-copied):
    a hand-list would silently drift when a reservation is added/removed. Operator/punctuation
    tokens in that chain (`+`, `=>`, `.`, …) are dropped — those are covered by opInfo / punctuation,
    not identifier keywords."""
    m = re.search(r"def pIdent\b.*?\n(.*?)\n\s*then\b", text, re.S)
    if not m:
        sys.exit("gen-tmgrammar: could not locate `def pIdent`'s reserved chain — the reserved-binder set is keyed off it.")
    words = re.findall(r't\s*=\s*"([^"]+)"', m.group(1))
    # keep only word-shaped reservations (identifiers); punctuation/operators are handled elsewhere.
    binders = [w for w in words if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", w)]
    if not binders:
        sys.exit("gen-tmgrammar: `pIdent`'s reserved chain parsed to no identifier keywords — the chain shape changed.")
    # de-dup, preserving source order.
    seen, out = set(), []
    for w in binders:
        if w not in seen:
            seen.add(w)
            out.append(w)
    return out


def alternation(words):
    """A TextMate alternation over literal words, longest-first (so a longer keyword is never
    shadowed by a prefix)."""
    return "|".join(re.escape(w) for w in sorted(set(words), key=lambda w: (-len(w), w)))


def render():
    surf = SURFACE.read_text()

    # keyword-led constructs: the leading keyword of each `keywordRule` entry.
    kw_led = [kw for kw, _form in _gr.extract_keyword_rules(surf)]
    # reserved binder words (pIdent) — the full identifier-keyword set (get/put/new/resume/param/…).
    reserved = extract_reserved_binders(surf)
    # operators from opInfo (punctuation-shaped — no word boundaries).
    ops = [op for op, _l, _r in _gr.extract_op_table(surf)]
    # effect-channel label NAMES (throws/state/stm/Div) — the row-annotation vocabulary.
    # extract_labels returns (defName, value, summary); the surface NAME is the def stripped of `Label`.
    labels = [re.sub(r"Label$", "", n) for n, _v, _s in _gr.extract_labels(surf)]

    # The keyword scope covers BOTH the keyword-led constructs AND the reserved binder words —
    # they are one lexical class (parser-recognised words a program cannot rebind). Union, source-
    # order-stable, so the grammar names every parser keyword exactly once.
    keyword_words = []
    seen = set()
    for w in kw_led + reserved:
        if w not in seen:
            seen.add(w)
            keyword_words.append(w)

    grammar = {
        "$schema": "https://raw.githubusercontent.com/martinring/tmlanguage/master/tmlanguage.json",
        "_generated": "by tools/gen-tmgrammar.py from Bang/Frontend/Surface.lean — do not hand-edit; run `just tmgrammar`.",
        "name": "BANG",
        "scopeName": "source.bang",
        "patterns": [
            {"include": "#comments"},
            {"include": "#strings"},
            {"include": "#keywords"},
            {"include": "#effect-labels"},
            {"include": "#operators"},
            {"include": "#numbers"},
            {"include": "#punctuation"},
        ],
        "repository": {
            "comments": {
                "name": "comment.line.double-dash.bang",
                "match": LINE_COMMENT,
            },
            "strings": {
                "name": "string.quoted.double.bang",
                "begin": STRING_PATTERN,
                "end": STRING_PATTERN,
                "patterns": [
                    {"name": "constant.character.escape.bang", "match": r"\\."},
                ],
            },
            "keywords": {
                "name": "keyword.control.bang",
                "match": rf"\b(?:{alternation(keyword_words)})\b",
            },
            "effect-labels": {
                "name": "support.type.effect.bang",
                "match": rf"\b(?:{alternation(labels)})\b",
            },
            "operators": {
                "name": "keyword.operator.bang",
                "match": "|".join(re.escape(op) for op in sorted(set(ops), key=lambda o: (-len(o), o))),
            },
            "numbers": {
                "name": "constant.numeric.bang",
                "match": NUMBER_PATTERN,
            },
            "punctuation": {
                "name": "punctuation.bang",
                "match": PUNCTUATION,
            },
        },
    }
    return json.dumps(grammar, indent=2, ensure_ascii=False) + "\n"


def main():
    try:
        subprocess.run(["bash", os.path.join(os.path.dirname(__file__), "tool-log.sh"),
                        os.path.basename(__file__)], check=False)
    except Exception:
        pass
    content = render()
    if "--check" in sys.argv:
        current = OUT.read_text() if OUT.exists() else ""
        if current != content:
            print("tmgrammar: STALE — web/docs/bang.tmLanguage.json != regenerated. Run `just tmgrammar`.")
            sys.exit(1)
        print("tmgrammar: OK — bang.tmLanguage.json ≡ the reified parser tables.")
        return
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(content)
    print(f"tmgrammar: wrote {OUT.relative_to(ROOT)} (keywords + operators + reserved binders from Surface.lean).")


if __name__ == "__main__":
    main()
