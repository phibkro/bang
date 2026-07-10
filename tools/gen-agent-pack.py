#!/usr/bin/env python3
# tool: role=gen couples=.claude/lane-discipline.md,.claude/agents/*.md,genblock.py runs-in=fitness
"""gen-agent-pack.py — splice the lane-discipline pack into each subagent role file.

The standing IC rules live once in `.claude/lane-discipline.md` (the PACK region between
`<!-- BEGIN PACK lane-discipline -->` and `<!-- END PACK lane-discipline -->`). Subagent
role files (`.claude/agents/*.md`) need those rules too, but the Claude-Code harness does
NOT expand `@path` / `$(...)` injection in an agent body (empirically verified 2026-07-10:
a scratch agent with an `@`-reference and a `$(...)` in its body saw NEITHER expanded, while
a literal body token WAS visible). So this is the repo's generate-rung fallback: a marked
GENERATED block spliced verbatim into each role file, drift-gated by `--check` in `just
fitness` — the same move as gen-tools-index / gen-gate-index.

  gen-agent-pack.py           # (re)splice the block into every .claude/agents/*.md
  gen-agent-pack.py --check   # exit 1 if any role file's block is stale vs the PACK region
"""
import glob
import os
import re
import subprocess
import sys

ROOT = subprocess.run(["git", "rev-parse", "--show-toplevel"],
                      capture_output=True, text=True).stdout.strip()
SRC = os.path.join(ROOT, ".claude", "lane-discipline.md")
AGENTS_GLOB = os.path.join(ROOT, ".claude", "agents", "*.md")

PACK_BEGIN = "<!-- BEGIN PACK lane-discipline"
PACK_END = "<!-- END PACK lane-discipline -->"
GEN_BEGIN = "<!-- BEGIN GENERATED lane-discipline (tools/gen-agent-pack.py — do not hand-edit) -->"
GEN_END = "<!-- END GENERATED lane-discipline -->"

from genblock import splice as _splice  # the shared GEN-marker primitive (#113)


def pack_body():
    """The PACK region of lane-discipline.md, WITHOUT its own PACK markers."""
    md = open(SRC, encoding="utf-8").read()
    m = re.search(re.escape(PACK_BEGIN) + r".*?-->\n(.*?)\n" + re.escape(PACK_END),
                  md, re.DOTALL)
    if not m:
        return None
    return m.group(1).strip()


def gen_block(body):
    return f"{GEN_BEGIN}\n{body}\n{GEN_END}"


def apply(md, block):
    """Replace an existing GEN block, else append it (with a separating blank line)."""
    if GEN_BEGIN in md and GEN_END in md:
        return _splice(md, GEN_BEGIN, GEN_END, block)
    return md.rstrip() + "\n\n" + block + "\n"


def main():
    try: __import__("subprocess").run(["bash", __import__("os").path.join(__import__("os").path.dirname(__file__), "tool-log.sh"), __import__("os").path.basename(__file__)], check=False)  # tool-log (plan 012)
    except Exception: pass
    check = "--check" in sys.argv
    body = pack_body()
    if body is None:
        print("── gen-agent-pack ──")
        print(f"ERROR: no PACK region ({PACK_BEGIN} … {PACK_END}) in {os.path.relpath(SRC, ROOT)}.")
        return 1
    block = gen_block(body)

    files = sorted(glob.glob(AGENTS_GLOB))
    stale = []
    for f in files:
        cur = open(f, encoding="utf-8").read()
        new = apply(cur, block)
        if check:
            if new != cur:
                stale.append(os.path.relpath(f, ROOT))
        else:
            if new != cur:
                open(f, "w", encoding="utf-8").write(new)

    print("── gen-agent-pack ──")
    if check:
        if stale:
            print("FAIL: role files carry a stale lane-discipline block — run `just agent-pack`:")
            for s in stale:
                print(f"    {s}")
            return 1
        print(f"PASS: {len(files)} role file(s) carry the current pack.")
        return 0
    print(f"agent-pack: spliced the pack into {len(files)} role file(s).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
