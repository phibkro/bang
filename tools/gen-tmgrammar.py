#!/usr/bin/env python3
# tool: role=gen couples=docfacts/language.json,web/docs/bang.tmLanguage.json runs-in=fitness
"""Generate web/docs/bang.tmLanguage.json — a TextMate grammar DERIVED from the reified parser tables.

Serialized source of truth: `docfacts/language.json`, loaded through
`load_language_fact()`. The bundle is generated from the reified parser tables and is the same
consumer boundary used by the maintained language reference.

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

from docfacts_language import load_language_fact

ROOT = pathlib.Path(__file__).resolve().parent.parent
OUT = ROOT / "web/docs/bang.tmLanguage.json"

# ── Hand-written lexical residue (NOT in the reified tables) ──
# TextMate regexes for the lexical layer the rule/op tables don't carry.
LINE_COMMENT = "--.*$"          # issue #62: `--` runs to end-of-line, maximal-munch over `-`/`->`
STRING_PATTERN = r'"'           # string opens on `"`; the JSON rule captures the body + escapes
NUMBER_PATTERN = r"\b-?\d+\b"   # integer literals (Int is unbounded ℤ, ADR-0067)
PUNCTUATION = r"[{}(),;]"       # effect/handler/tuple block punctuation


def alternation(words):
    """A TextMate alternation over literal words, longest-first (so a longer keyword is never
    shadowed by a prefix)."""
    return "|".join(re.escape(w) for w in sorted(set(words), key=lambda w: (-len(w), w)))


def render():
    language = load_language_fact()
    grammar_fact = language["grammar"]

    kw_led = [row["keyword"] for row in grammar_fact["keywordRules"]]
    reserved = grammar_fact["reservedIdentifiers"]
    ops = [row["symbol"] for row in grammar_fact["operators"]]
    labels = [row["name"] for row in grammar_fact["effectLabels"]]

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
        "_generated": "by tools/gen-tmgrammar.py from docfacts/language.json — do not hand-edit; run `just tmgrammar`.",
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
    print(f"tmgrammar: wrote {OUT.relative_to(ROOT)} (keywords + operators + reserved binders from language docfacts).")


if __name__ == "__main__":
    main()
