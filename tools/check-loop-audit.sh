#!/usr/bin/env bash
# tool: role=check couples=docs/notes/loop-audit.md,ROADMAP.md runs-in=fitness
# check-loop-audit.sh — loop-audit freshness fitness function.
#
# docs/notes/loop-audit.md is the judgment-tier instrument (feedback loops by radius,
# refreshed at each checkpoint ◊). ROADMAP.md changes only at checkpoint boundaries
# (its own update discipline) — so a ROADMAP commit NEWER than the loop-audit's last
# commit means a checkpoint moved without the audit being refreshed. This check can't
# mechanize the judgment; it mechanizes the TRIGGER (the freshness), same pattern as
# gen-proof-state's staleness gate. Same-commit updates pass (>= tolerance).
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

AUDIT="docs/notes/loop-audit.md"
ROADMAP="ROADMAP.md"

echo "── check-loop-audit (◊-refresh freshness) ──"

if [ ! -f "$AUDIT" ]; then
  echo "FAIL: $AUDIT missing — seed it (see the 2026-07-08 evaluation) or drop this leg."
  exit 1
fi

# In-flight refresh (staged/dirty loop-audit) passes — the pre-commit hook runs BEFORE the
# commit exists, so the commit that adds/refreshes the audit must not be blocked by it.
# (A ROADMAP-only commit slips this hook-time check; the NEXT fitness run / CI catches it.)
if [ -n "$(git status --porcelain -- "$AUDIT")" ]; then
  echo "PASS: loop-audit refresh in flight (staged/uncommitted edit)."
  exit 0
fi

# Committed timestamps only (unborn/uncommitted files → 0 ⇒ fails until committed together).
t_audit="$(git log -1 --format=%ct -- "$AUDIT" 2>/dev/null || echo 0)"
t_roadmap="$(git log -1 --format=%ct -- "$ROADMAP" 2>/dev/null || echo 0)"
: "${t_audit:=0}" "${t_roadmap:=0}"

if [ "$t_audit" -ge "$t_roadmap" ]; then
  echo "PASS: loop-audit is as fresh as ROADMAP (last audit commit ≥ last ROADMAP commit)."
  exit 0
fi

echo "STALE  $AUDIT — ROADMAP.md moved ($(date -d "@$t_roadmap" +%F)) after the last loop-audit"
echo "       refresh ($(date -d "@$t_audit" +%F)). A ROADMAP change ≈ a checkpoint boundary:"
echo "       re-grade the loop table + update its _Position:_ stamp, commit them together."
echo "FAIL: refresh docs/notes/loop-audit.md (see its 'How to refresh' section)."
exit 1
