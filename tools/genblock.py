"""genblock.py — the shared GEN-marker block primitive (#113).

A generated doc carries a `<!-- BEGIN … -->…<!-- END … -->` region a tool
regenerates or `--check`s. The actual splice (`re.sub` over the marked region)
was copy-pasted across gen-gate-index / gen-import-graph / gen-proof-state /
refs — this is the one copy. Each generator keeps a 2-line adapter binding its
own markers (and its own regen/`--check` flow, which genuinely varies).

(`gen-adr-index.py` keeps its own append-on-absent variant — different behaviour.)
"""
import re


def splice(md: str, begin: str, end: str, block: str) -> str:
    """Replace the BEGIN…END region (inclusive) of `md` with `block`."""
    return re.sub(re.escape(begin) + r".*?" + re.escape(end), block, md, flags=re.DOTALL)
