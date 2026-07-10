#!/usr/bin/env python3
# tool: role=gen couples=tools/DeadCode.lean,Bang/**/*.lean,Main.lean runs-in=manual
"""gen-deadcode-imports.py — keep tools/DeadCode.lean's import block ≡ the module set.

The dead-code analyzer must see EVERY declaration in the project, including any
module orphaned by nothing (imported by no other module) — that is precisely the
class the route-1 rename chain fell into, and the class a "reachable from Audit's
closure" import list would MISS. So the import block is the full `Bang.**` module
set (a pure function of `find Bang -name '*.lean'`) plus `Main` — generated here,
never hand-maintained (drift → a new module silently escapes the scan).

Usage:
  tools/gen-deadcode-imports.py           # rewrite the GEN block in tools/DeadCode.lean
  tools/gen-deadcode-imports.py --check   # fail (exit 1) if the block is stale
"""
import os, re, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TARGET = os.path.join(ROOT, "tools", "DeadCode.lean")
BEGIN = "-- BEGIN GEN deadcode-imports (tools/gen-deadcode-imports.py) --"
END = "-- END GEN deadcode-imports --"


def module_names():
    mods = []
    for dirpath, _, files in os.walk(os.path.join(ROOT, "Bang")):
        for f in sorted(files):
            if f.endswith(".lean"):
                rel = os.path.relpath(os.path.join(dirpath, f), ROOT)
                mods.append(rel[:-len(".lean")].replace(os.sep, "."))
    return sorted(mods)


def gen_block():
    lines = [BEGIN, "import Main"]
    lines += [f"import {m}" for m in module_names()]
    lines.append(END)
    return "\n".join(lines)


def main():
    try: __import__("subprocess").run(["bash", __import__("os").path.join(__import__("os").path.dirname(__file__), "tool-log.sh"), __import__("os").path.basename(__file__)], check=False)  # tool-log (plan 012)
    except Exception: pass
    check = "--check" in sys.argv
    src = open(TARGET).read()
    block = gen_block()
    new = re.sub(re.escape(BEGIN) + r".*?" + re.escape(END), block, src, flags=re.DOTALL)
    if BEGIN not in src:
        print(f"ERROR: {TARGET} has no GEN markers ({BEGIN!r})", file=sys.stderr)
        return 1
    if check:
        if new != src:
            print(f"STALE: tools/DeadCode.lean import block ≠ module set. Run tools/gen-deadcode-imports.py", file=sys.stderr)
            return 1
        print("tools/DeadCode.lean import block is up to date.")
        return 0
    open(TARGET, "w").write(new)
    n = len(module_names())
    print(f"tools/DeadCode.lean: regenerated import block ({n} Bang modules + Main).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
