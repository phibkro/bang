#!/usr/bin/env python3
"""gen-proof-state.py — generate CONTEXT.md's proof-state line from the gate (the root).

CONTEXT.md hand-maintains a "proof-state" summary (which headline theorems are
axiom-clean · the sorry count · the sha). That is a SURVEY of `Bang/Audit.lean`
(the 24 `#print axioms <thm>` headlines) + `tools/burndown.sh` + `git` — copies of
facts that drift. This regenerates that summary from those roots, the same move as
`gen-adr-index.py` / `gen-gate-index.py` (the generate>test>convention ladder).

TREE-AWARENESS (why this is a fresh tool, not a copy of the others):
  Proof-state lives in `Audit.lean`, which is only current on the PROOF worktrees;
  the DOCS tree (where CONTEXT.md lives) carries stale / in-flight Lean. So the
  root we read (`--lean-root`) is decoupled from the doc we write (`--context`).
  And the gate is olean-backed: a warm olean can report a stale axiom set, so a
  real claim is read only after a force-rebuild (`touch` always; `--build` runs
  `lake build Bang.Audit` for an authoritative render).

  `--check` DEGRADES GRACEFULLY: if `lake` is unavailable, or no headline's
  `#print axioms` actually printed (Audit not buildable — the normal docs-tree
  state AND mid-reshape on the proof trees), it SKIPs (exit 0) rather than fail.
  Only when Audit builds and headlines print does it assert the committed block
  ≡ a fresh render. This is what lets it ride `just fitness` now (no build gate)
  and auto-activate when a proof tree goes green.

Zero dependencies (stdlib), like the other tools/ scripts.

Usage:
    gen-proof-state.py                       # rewrite the block in ./CONTEXT.md
    gen-proof-state.py --lean-root ../proof  # read Audit/burndown/git from there
    gen-proof-state.py --build               # force `lake build Bang.Audit` first
    gen-proof-state.py --check               # SKIP if not buildable; else gate drift
"""
from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys

BEGIN = "<!-- BEGIN GENERATED proof-state (just proof-state) — do not hand-edit -->"
END = "<!-- END GENERATED proof-state -->"

# The trusted-3: an axiom set ⊆ this is "clean". Anything else (incl. sorryAx) flags.
TRUSTED = {"propext", "Classical.choice", "Quot.sound"}

HEADLINE_RE = re.compile(r"^\s*#print axioms\s+(\S+)\s*$")
# `'Bang.foo' depends on axioms: [propext, Classical.choice]` — list may span lines.
DEPENDS_RE = re.compile(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", re.DOTALL)
# `'Bang.foo' does not depend on any axioms`
NODEPS_RE = re.compile(r"'([^']+)' does not depend on any axioms")
TOTAL_RE = re.compile(r"^TOTAL\s+(\d+)\s+(\d+)\s+(\d+)")


def headlines(lean_root: str) -> list[str]:
    """The headline theorem names from the active `#print axioms` lines in Audit.lean."""
    path = os.path.join(lean_root, "Bang", "Audit.lean")
    out = []
    for line in open(path, encoding="utf-8").read().splitlines():
        m = HEADLINE_RE.match(line)
        if m:
            out.append(m.group(1))
    return out


def run(cmd: list[str], cwd: str):
    """Run a command; return (rc, combined-output) or None if the binary is missing."""
    try:
        p = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=900)
        return p.returncode, (p.stdout or "") + (p.stderr or "")
    except FileNotFoundError:
        return None
    except subprocess.TimeoutExpired:
        return 1, ""


def axiom_report(lean_root: str, build: bool):
    """Force a fresh read of the axiom gate. Returns the report text, or None if
    `lake` is unavailable (→ caller SKIPs). `touch` always; `--build` rebuilds the
    import oleans first (authoritative, for the generate path)."""
    audit = os.path.join(lean_root, "Bang", "Audit.lean")
    if build:
        if run(["lake", "build", "Bang.Audit"], lean_root) is None:
            return None
    if os.path.exists(audit):
        os.utime(audit, None)  # touch: re-elaborate Audit against current oleans
    res = run(["lake", "env", "lean", "Bang/Audit.lean"], lean_root)
    return None if res is None else res[1]


def parse_axioms(text: str) -> dict[str, list[str]]:
    """fullname -> axiom list, from a `lake env lean Bang/Audit.lean` report."""
    found: dict[str, list[str]] = {}
    for name in NODEPS_RE.findall(text):
        found[name] = []
    for name, axs in DEPENDS_RE.findall(text):
        found[name] = [a.strip() for a in axs.split(",") if a.strip()]
    return found


def match(headline: str, report: dict[str, list[str]]):
    """An Audit headline (`lr_sound`, resolved to `Bang.lr_sound`) vs a fully-qualified
    report name. Dot-anchored so `compile_forward_sim` ≠ `compile_forward_sim_pure`."""
    for name, axs in report.items():
        if name == headline or name.endswith("." + headline) or headline.endswith("." + name):
            return axs
    return None


def classify(lean_root: str, report: dict[str, list[str]]):
    """(clean, pending, flagged) — flagged is [(headline, [bad+axioms])]."""
    clean, pending, flagged = [], [], []
    for h in headlines(lean_root):
        axs = match(h, report)
        if axs is None:
            pending.append(h)
        elif set(axs) <= TRUSTED:
            clean.append(h)
        else:
            flagged.append((h, axs))
    return clean, pending, flagged


def sorry_total(lean_root: str):
    """The burndown sorry count (TOTAL row, sorry column), or None if it can't run."""
    res = run(["bash", "tools/burndown.sh"], lean_root)
    if res is None or res[0] != 0:
        return None
    for line in res[1].splitlines():
        m = TOTAL_RE.match(line)
        if m:
            return int(m.group(1))
    return None


def sha(lean_root: str) -> str:
    # The proof-state's PROVENANCE = the last commit that touched the `Bang/` library
    # (what could move the axiom census) — NOT `HEAD`. Embedding HEAD made the generated
    # block self-invalidating: every docs/tooling commit moved HEAD, so `--check` went
    # stale on a change that couldn't affect the proof-state. Anchoring to the last
    # `Bang/` commit keeps the block green across non-proof commits (derivation-ladder fix).
    res = run(["git", "-C", lean_root, "log", "-1", "--format=%h", "--", "Bang"], lean_root)
    return res[1].strip() if res and res[0] == 0 and res[1].strip() else "unknown"


def render(lean_root: str, report: dict[str, list[str]]) -> str:
    clean, pending, flagged = classify(lean_root, report)
    s = sorry_total(lean_root)
    lines = [
        BEGIN,
        f"_Generated by `tools/gen-proof-state.py --lean-root <…>`. Proof-state at `{sha(lean_root)}`._",
        "",
        f"- **headlines:** {len(clean)} clean (⊆ trusted-3) · {len(pending)} pending "
        f"(build in flight) · {len(flagged)} flagged",
    ]
    for name, axs in flagged:
        lines.append(f"- **flagged:** `{name}` → [{', '.join(axs)}]")
    lines.append(f"- **sorries:** {s if s is not None else 'unknown'} (per `burndown.sh`)")
    lines.append(END)
    return "\n".join(lines)


def splice(md: str, block: str) -> str:
    return re.sub(re.escape(BEGIN) + r".*?" + re.escape(END), block, md, flags=re.DOTALL)


def buildable(report, lean_root) -> bool:
    """Audit is buildable iff at least one headline's axiom report actually printed."""
    _, pending, _ = classify(lean_root, report)
    return len(pending) < len(headlines(lean_root))


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--lean-root", default=".", help="where to run lake/git (default: cwd)")
    ap.add_argument("--context", default=None, help="doc to write (default: <lean-root>/CONTEXT.md)")
    ap.add_argument("--build", action="store_true", help="force `lake build Bang.Audit` first")
    ap.add_argument("--check", action="store_true", help="SKIP if not buildable; else gate drift")
    args = ap.parse_args()

    lean_root = os.path.abspath(args.lean_root)
    context = os.path.abspath(args.context or os.path.join(lean_root, "CONTEXT.md"))

    # FAST PATH (--check only): the block derives ONLY from `Bang/` (Audit headlines +
    # burndown sorries), and its embedded provenance sha is the last `Bang/` commit. If
    # that still equals the current last-`Bang/` commit, the block provably cannot have
    # drifted → PASS WITHOUT invoking `lake` — the gate's single most expensive leg
    # (~1.5s, the only one that elaborates the spine). Docs/tooling commits skip it.
    if args.check and os.path.exists(context):
        md0 = open(context, encoding="utf-8").read()
        m = re.search(r"Proof-state at `([0-9a-f]+)`", md0)
        if BEGIN in md0 and END in md0 and m and m.group(1) == sha(lean_root):
            print("── proof-state ──\nPASS: block provenance sha ≡ last `Bang/` commit "
                  "(unchanged) — lake skipped.")
            return 0
        # else fall through to the full lake-based check below.

    report_text = axiom_report(lean_root, build=args.build)
    report = parse_axioms(report_text) if report_text is not None else {}

    if args.check:
        # Degrade gracefully: lake missing, or Audit not buildable → SKIP (don't fail).
        if report_text is None:
            print("── proof-state ──\nSKIP: `lake` unavailable in "
                  f"{lean_root} (proof-state check inactive).")
            return 0
        if not buildable(report, lean_root):
            print("── proof-state ──\nSKIP: Audit.lean not buildable in "
                  f"{lean_root} (proof-state check inactive until the tree greens).")
            return 0
        block = render(lean_root, report)
        md = open(context, encoding="utf-8").read()
        if BEGIN not in md or END not in md:
            print(f"── proof-state ──\nFAIL: {context} has no GEN markers — run `just proof-state`.")
            return 1
        if splice(md, block) != md:
            print("── proof-state ──\nFAIL: CONTEXT.md proof-state block is stale "
                  "— run `just proof-state`.")
            return 1
        print("── proof-state ──\nPASS: proof-state block ≡ the live axiom gate.")
        return 0

    block = render(lean_root, report)
    md = open(context, encoding="utf-8").read()
    if BEGIN not in md or END not in md:
        print(f"proof-state: {context} has no GEN markers — add them to enable generation.",
              file=sys.stderr)
        return 1
    open(context, "w", encoding="utf-8").write(splice(md, block))
    print(f"proof-state: regenerated the block in {os.path.relpath(context, lean_root)}.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
