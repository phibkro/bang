#!/usr/bin/env python3
# tool: role=check couples=justfile,tools/run-batteries.sh,tools/git-hooks/pre-commit,.claude/settings.json runs-in=fitness
"""check-runs-in.py — the `runs-in=` claim is VALIDATED, not just declared (plan 012 slice 2).

Each tools/ script carries a `# tool: … runs-in=<fitness|verify|hook|manual|ci>` header.
That field is a CLAIM about where the script fires. It drifted once (a script claimed
`runs-in=verify` for weeks while wired to nothing, found by reading). This makes the drift
a loud CHECK FAILURE instead of a reading task — the same generate/check move the rest of
tools/ rides:

  (a) every `runs-in=verify` script is REACHABLE from the gate — invoked by a recipe in the
      `verify` dependency chain (transitive) OR enrolled in run-batteries.sh's `batteries` array.
  (b) every `batteries` array entry names a real script whose header says `runs-in=verify`
      (the array is the enrollment point; a typo or a mis-tagged battery fails loud).
  (c) every `runs-in=hook` script is referenced by a hook installation — the git pre-commit
      source, `.claude/settings.json` (the Claude-Code harness hooks), or IS the pre-commit
      itself. (The plan said "pre-commit source"; the honest reachability includes the harness
      hooks, which the pre-commit does not reference — see the deviation note in the report.)
  (d) [plan maintenance-note] a `runs-in=deprecated`… — deferred to slice 3, which adds the
      `status=` field; a `deprecated` tool may not appear in any gate chain. See check_deprecated.

A conservative subset (batteries + hook only) is the sanctioned fallback if the justfile
chain parse turns fragile; it does NOT here — the verify chain is 4 static deps, each a
recipe with literal `tools/…` command lines.
"""
import os
import re
import sys

ROOT = os.path.abspath(os.environ.get("REFS_ROOT", "."))
JUSTFILE = os.path.join(ROOT, "justfile")
BATTERIES = os.path.join(ROOT, "tools", "run-batteries.sh")
PRECOMMIT = os.path.join(ROOT, "tools", "git-hooks", "pre-commit")
SETTINGS = os.path.join(ROOT, ".claude", "settings.json")

HEADER_RE = re.compile(r"^(?:#|//)\s*tool:\s*"
                       r"role=(\S+)\s+couples=(\S+)\s+runs-in=(\S+)\s*$")
TOOL_INVOKE_RE = re.compile(r"tools/([\w./-]+\.(?:sh|py|mjs))")


def required_scripts():
    import subprocess
    out = subprocess.run(["git", "ls-files", "tools/"], capture_output=True,
                         text=True, cwd=ROOT).stdout.splitlines()
    return sorted(f for f in out
                  if f.endswith((".py", ".sh", ".mjs")) or f == "tools/git-hooks/pre-commit")


def header_of(path):
    """(role, couples, runs_in) or None."""
    for line in open(os.path.join(ROOT, path), encoding="utf-8").read().splitlines()[:6]:
        m = HEADER_RE.match(line)
        if m:
            return m.group(1), m.group(2), m.group(3)
    return None


def parse_recipes(text):
    """name -> list of raw command lines. `name: dep1 dep2` captured as deps too."""
    recipes, deps, cur = {}, {}, None
    for line in text.splitlines():
        m = re.match(r"^([a-zA-Z][\w-]*)(?:\s+[A-Z][\w=\"]*)*\s*:(.*)$", line)
        if m and not line.startswith(" "):
            cur = m.group(1)
            recipes.setdefault(cur, [])
            deps[cur] = [d for d in m.group(2).strip().split() if d and not d.startswith("#")]
        elif cur and (line.startswith("    ") or line.startswith("\t")):
            s = line.strip()
            if s and not s.startswith("#"):
                recipes[cur].append(s)
        elif line and not line.startswith(" "):
            cur = None
    return recipes, deps


def chain_closure(root, deps):
    """Transitive set of recipe names reachable as deps from `root` (incl. root)."""
    seen, stack = set(), [root]
    while stack:
        n = stack.pop()
        if n in seen:
            continue
        seen.add(n)
        stack.extend(deps.get(n, []))
    return seen


def tools_invoked_by(recipe_names, recipes):
    """Every tools/<file> literal invoked by any command line of the named recipes.
    Skips the tool-log telemetry call (it is instrumentation, not a gate leg)."""
    found = set()
    for name in recipe_names:
        for cmd in recipes.get(name, []):
            if "tools/tool-log.sh" in cmd:
                continue
            for m in TOOL_INVOKE_RE.finditer(cmd):
                found.add(m.group(1))
    return found


def batteries_array():
    """The battery basenames enrolled in run-batteries.sh (the `batteries=(…)` array)."""
    txt = open(BATTERIES, encoding="utf-8").read()
    m = re.search(r"batteries=\((.*?)\)", txt, re.DOTALL)
    if not m:
        return None
    return [w for w in m.group(1).split() if w and not w.startswith("\\")]


def main():
    try: __import__("subprocess").run(["bash", __import__("os").path.join(__import__("os").path.dirname(__file__), "tool-log.sh"), __import__("os").path.basename(__file__)], check=False)  # tool-log (plan 012)
    except Exception: pass
    scripts = required_scripts()
    hdrs = {s: header_of(s) for s in scripts}
    missing_hdr = [s for s, h in hdrs.items() if h is None]
    if missing_hdr:
        print("── check-runs-in ──")
        print("FAIL: tools/ scripts missing the `# tool:` header (gen-tools-index owns this too):")
        for s in missing_hdr:
            print(f"    {s}")
        return 1

    recipes, deps = parse_recipes(open(JUSTFILE, encoding="utf-8").read())
    verify_chain = chain_closure("verify", deps)
    verify_tools = tools_invoked_by(verify_chain, recipes)   # e.g. {selfcheck.mjs, run-batteries.sh, audit.sh}

    bats = batteries_array()
    if bats is None:
        print("── check-runs-in ──")
        print("FAIL: could not parse the `batteries=(…)` array in tools/run-batteries.sh.")
        return 1
    battery_scripts = {f"{b}.sh" for b in bats}
    reachable = verify_tools | battery_scripts

    errors = []

    # (a) every runs-in=verify script is reachable
    for s, (role, couples, runs_in) in hdrs.items():
        if runs_in == "verify":
            base = s[len("tools/"):]
            if base not in reachable:
                errors.append(f"(a) {s} claims runs-in=verify but is NOT reachable from the "
                              f"verify chain (recipes {sorted(verify_chain)}) nor in the "
                              f"run-batteries `batteries` array.")

    # (b) every batteries entry has a matching runs-in=verify script
    verify_bases = {s[len('tools/'):] for s, (r, c, ri) in hdrs.items() if ri == "verify"}
    for b in bats:
        base = f"{b}.sh"
        path = f"tools/{base}"
        if path not in hdrs:
            errors.append(f"(b) batteries entry `{b}` → {path} does not exist.")
        elif base not in verify_bases:
            errors.append(f"(b) batteries entry `{b}` → {path} exists but its header does "
                          f"NOT say runs-in=verify (says runs-in={hdrs[path][2]}).")

    # (c) every runs-in=hook script is referenced by a hook installation
    pre_src = open(PRECOMMIT, encoding="utf-8").read() if os.path.exists(PRECOMMIT) else ""
    settings_src = open(SETTINGS, encoding="utf-8").read() if os.path.exists(SETTINGS) else ""
    for s, (role, couples, runs_in) in hdrs.items():
        if runs_in == "hook":
            base = s[len("tools/"):]                # e.g. hooks/session-start.sh, git-hooks/pre-commit
            leaf = os.path.basename(s)
            is_precommit = s == "tools/git-hooks/pre-commit"
            referenced = (is_precommit
                          or leaf in pre_src or base in pre_src
                          or leaf in settings_src or base in settings_src)
            if not referenced:
                errors.append(f"(c) {s} claims runs-in=hook but is referenced by neither the "
                              f"pre-commit source nor .claude/settings.json.")

    print("── check-runs-in ──")
    if errors:
        print(f"FAIL: {len(errors)} runs-in claim(s) unvalidated:")
        for e in errors:
            print(f"    {e}")
        return 1
    print(f"PASS: {sum(1 for h in hdrs.values() if h[2]=='verify')} verify-tagged reachable · "
          f"{len(bats)} batteries all runs-in=verify · "
          f"{sum(1 for h in hdrs.values() if h[2]=='hook')} hook-tagged referenced.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
