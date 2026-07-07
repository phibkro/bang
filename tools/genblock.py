"""genblock.py — shared generator primitives.

Two things generators copy-pasted, now with one home each:

  splice          — the GEN-marker block replace (`<!-- BEGIN … -->…<!-- END … -->`),
                    was duplicated across gen-gate-index / gen-import-graph /
                    gen-proof-state / refs (#113).
  validate_mermaid — compile a mermaid fence with `mmdc` (catches generator bugs
                    like a raw newline in a label or an id clash). Was inline in
                    gen-import-graph; gen-questions-index reuses the SAME check.

(`gen-adr-index.py` keeps its own append-on-absent variant — different behaviour.)
"""
import os
import re
import shutil
import subprocess
import tempfile


def splice(md: str, begin: str, end: str, block: str) -> str:
    """Replace the BEGIN…END region (inclusive) of `md` with `block`."""
    return re.sub(re.escape(begin) + r".*?" + re.escape(end), block, md, flags=re.DOTALL)


def validate_mermaid(block):
    """Render the ```mermaid fence in `block` with `mmdc` — ('pass'|'fail'|'skip', msg).
    Drift checks (`--check`) only confirm the TEXT matches the source; THIS confirms the
    diagram actually COMPILES. `mmdc` lives in the dev shell (`nix develop`); skip if absent."""
    if not shutil.which("mmdc"):
        return ("skip", "mmdc not on PATH (it's in the dev shell — `nix develop`); compile-check skipped")
    m = re.search(r"```mermaid\n(.*?)\n```", block, re.DOTALL)
    if not m:
        return ("skip", "no mermaid fence in the block")
    d = tempfile.mkdtemp()
    mmd, cfg, svg = (os.path.join(d, x) for x in ("g.mmd", "pptr.json", "g.svg"))
    open(mmd, "w").write(m.group(1))
    open(cfg, "w").write('{"args":["--no-sandbox","--disable-gpu"]}')  # sandboxed env needs --no-sandbox
    try:
        r = subprocess.run(["mmdc", "-i", mmd, "-o", svg, "-p", cfg],
                           capture_output=True, text=True, timeout=180)
        ok = r.returncode == 0 and os.path.exists(svg)
        return ("pass", "mermaid compiles (mmdc render OK)") if ok else \
               ("fail", (r.stderr or r.stdout).strip()[-500:])
    finally:
        shutil.rmtree(d, ignore_errors=True)
