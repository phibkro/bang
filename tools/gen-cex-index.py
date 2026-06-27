#!/usr/bin/env python3
"""gen-cex-index.py — generate the counterexample-registry index from the witnesses.

The index table in docs/notes/counterexamples.md is a pure function of two roots:

  • Bang/Counterexamples.lean — the registry MANIFEST. Its `import Bang.X` lines (a
    commented `-- import` = a PRE-EXISTING-RED witness, excluded from the build target)
    declare membership, and each carries a structured `-- cex: guards=<live statement>
    [red=<reason>]` annotation naming the live statement the witness pins. This is the
    one field not cleanly recoverable from the witness prose, so it lives here.
  • each witness Bang/X.lean — its leading `/-! … -/` (or `/- … -/`) doc-comment header
    is the SoT for WHAT the witness refutes/witnesses. We extract the first sentence;
    we never hand-duplicate it.

Hand-maintaining the table lets it drift from those roots; generating it makes drift
unrepresentable (the generate>test>convention ladder — see .claude/codebase-maintenance.md
and the sibling tools/gen-adr-index.py for the ADR ledger this imitates).

Axiom standing is NOT embedded as a per-theorem set (the kernel is its SoT): the column
records the verified VERDICT (green witnesses are axiom-clean; reds do not compile) and
points at the live gate `just cex-axioms` (= `lake env lean Bang/Counterexamples.lean`,
which `#print axioms` each headline theorem). The lake build of the manifest re-verifies
every green witness is sorry-free.

Usage:
    gen-cex-index.py            # rewrite the generated region in counterexamples.md
    gen-cex-index.py --check    # exit 1 if the committed region is stale
"""

from __future__ import annotations

import argparse
import difflib
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "Bang" / "Counterexamples.lean"
INDEX = ROOT / "docs" / "notes" / "counterexamples.md"

BEGIN = "<!-- BEGIN GENERATED CEX INDEX — do not edit; run `just counterexamples` -->"
END = "<!-- END GENERATED CEX INDEX -->"

TRUSTED = "{propext, Classical.choice, Quot.sound}"

# A manifest member: `import Bang.X  -- cex: guards=…` (green) or the same `--`-commented
# (red). Captures: the leading `--` (commented ⇒ red), the module, the meta string.
MEMBER_RE = re.compile(
    r"^\s*(--\s*)?import\s+(Bang\.[A-Za-z0-9_.]+)\s*--\s*cex:\s*(.*\S)\s*$"
)
# The first doc-comment block in a witness file (`/-! … -/` or `/- … -/`).
DOCBLOCK_RE = re.compile(r"/-!?\s*(.*?)-/", re.DOTALL)


def first_sentence(docblock: str, module: str) -> str:
    """First sentence of a witness's leading doc comment, the `Bang/X.lean — ` filename
    prefix stripped. Flatten wrapped lines so a sentence split mid-wrap stays whole."""
    flat = re.sub(r"\s+", " ", docblock).strip()
    fname = module.split(".")[-1]
    flat = re.sub(rf"^Bang/{re.escape(fname)}\.lean\s*[—–-]\s*", "", flat)
    m = re.search(r"^(.*?\.)(?:\s|$)", flat)  # up to the first `. ` (period + space/end)
    return (m.group(1) if m else flat).strip()


def parse_meta(meta: str) -> tuple[str, str | None]:
    """Split a `guards=… [red=…]` meta string into (guards, red_reason | None)."""
    red = None
    rm = re.search(r"\bred=(.*)$", meta)
    if rm:
        red = rm.group(1).strip()
        meta = meta[: rm.start()].strip()
    guards = re.sub(r"^guards=\s*", "", meta).strip()
    return guards, red


def file_for(module: str) -> Path:
    return ROOT / (module.replace(".", "/") + ".lean")


def collect() -> list[dict]:
    members = []
    for line in MANIFEST.read_text(encoding="utf-8").splitlines():
        m = MEMBER_RE.match(line)
        if not m:
            continue
        red_member = m.group(1) is not None
        module = m.group(2)
        guards, red_reason = parse_meta(m.group(3))
        path = file_for(module)
        if not path.exists():
            raise SystemExit(f"FAIL: manifest names {module} but {path} is missing.")
        block = DOCBLOCK_RE.search(path.read_text(encoding="utf-8"))
        if not block:
            raise SystemExit(f"FAIL: {path.name} has no leading /-! … -/ header to extract.")
        members.append({
            "module": module,
            "file": path.relative_to(ROOT).as_posix(),
            "refutes": first_sentence(block.group(1), module),
            "guards": guards,
            "red": red_member,
            "red_reason": red_reason,
        })
    if not members:
        raise SystemExit("FAIL: no `import Bang.X  -- cex: …` members found in the manifest.")
    return members


def md_escape(s: str) -> str:
    return s.replace("|", "\\|")


def render(members: list[dict]) -> str:
    out = [BEGIN, ""]
    out.append("| Witness | What it refutes / witnesses | Live statement it guards | Axiom standing |")
    out.append("|---|---|---|---|")
    for w in members:
        link = f"[`{w['module']}`](../../{w['file']})"
        if w["red"]:
            axiom = md_escape(f"RED — does not compile ({w['red_reason']})")
        else:
            axiom = "clean — gate `just cex-axioms`"
        out.append(
            f"| {link} | {md_escape(w['refutes'])} | {md_escape(w['guards'])} | {axiom} |"
        )
    greens = sum(1 for w in members if not w["red"])
    reds = sum(1 for w in members if w["red"])
    out.append("")
    out.append(
        f"_{greens} green (built + axiom-gated via `Bang/Counterexamples.lean`; "
        f"axiom sets ⊆ {TRUSTED}), {reds} pre-existing-red (excluded from the build "
        f"target). Generated from the manifest + witness headers — `just counterexamples`._"
    )
    out.append("")
    out.append(END)
    return "\n".join(out)


def splice(text: str, generated: str) -> str:
    if BEGIN in text and END in text:
        pre = text[: text.index(BEGIN)]
        post = text[text.index(END) + len(END):]
        return pre + generated + post
    sep = "" if text.endswith("\n\n") else ("\n" if text.endswith("\n") else "\n\n")
    return text + sep + generated + "\n"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--check", action="store_true", help="exit 1 if the index is stale")
    args = ap.parse_args()

    members = collect()
    generated = render(members)
    current = INDEX.read_text(encoding="utf-8")
    new = splice(current, generated)

    if args.check:
        if new != current:
            print("FAIL: docs/notes/counterexamples.md generated region is STALE.")
            print("      Run `just counterexamples` to regenerate. Diff (committed → expected):")
            diff = difflib.unified_diff(
                current.splitlines(), new.splitlines(),
                fromfile="counterexamples.md (committed)",
                tofile="counterexamples.md (regenerated)", lineterm="",
            )
            print("\n".join(diff))
            return 1
        print(f"cex-check: OK — index current ({len(members)} witnesses).")
        return 0

    INDEX.write_text(new, encoding="utf-8")
    print(f"cex-index: wrote {INDEX} ({len(members)} witnesses).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
