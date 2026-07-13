#!/usr/bin/env python3
# tool: role=lib couples=tools/clone-report.py,tools/gen-proof-assets.py runs-in=manual
"""leanlex.py — tiny shared lexer helpers for Lean sources (comment stripping).

Single home for "what is code vs comment in a .lean file" so the analysis
tools (clone-report, gen-proof-assets) can't disagree about it.
"""

from __future__ import annotations


def strip_comments(text: str) -> str:
    """Remove Lean line comments (`-- …`) and (nested) block comments
    (`/- … -/`), preserving newlines so line numbers survive."""
    out: list[str] = []
    i, n, depth = 0, len(text), 0
    while i < n:
        two = text[i : i + 2]
        if depth == 0 and two == "--":
            j = text.find("\n", i)
            i = n if j == -1 else j  # keep the newline
        elif two == "/-":
            depth += 1
            i += 2
        elif depth > 0 and two == "-/":
            depth -= 1
            i += 2
        elif depth > 0:
            if text[i] == "\n":
                out.append("\n")
            i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)
