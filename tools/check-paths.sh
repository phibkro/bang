#!/usr/bin/env bash
# check-paths.sh — PATH lifecycle fitness function.
#
# A `paths/PATH-*.md` is a unit of in-flight work (CLAUDE.md). When its work lands
# it should be `git mv`'d to `paths/archive/`. Two litter modes this catches:
#   ORPHAN — an active PATH not referenced from CONTEXT.md or ROADMAP.md. Either its
#            work is done (archive it) or a fresh agent can't find it from the
#            orientation docs (link it). The G2 "stale PATH" survey-residue, climbed.
#   DUP    — a PATH present in BOTH paths/ and paths/archive/ (a copy-not-move bug;
#            two copies of the same doc that can disagree).
# The glob matches only PATH-*.md (README.md / _template.md are scaffolding, skipped).
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

issues=""
for f in paths/PATH-*.md; do
  [ -e "$f" ] || continue
  b="$(basename "$f")"; stem="${b%.md}"
  if ! grep -qE "$stem" CONTEXT.md ROADMAP.md 2>/dev/null; then
    issues+="ORPHAN  $f — not referenced in CONTEXT.md or ROADMAP.md (done → archive, or link it)\n"
  fi
  if [ -e "paths/archive/$b" ]; then
    issues+="DUP     $b — in BOTH paths/ and paths/archive/ (copy-not-move)\n"
  fi
done

echo "── check-paths (PATH lifecycle) ──"
if [ -z "$issues" ]; then
  echo "PASS: every active PATH is reachable from CONTEXT/ROADMAP; none double-archived."
  exit 0
fi
printf "%b" "$issues"
echo "FAIL: stale/orphaned active PATH(s) — \`git mv paths/X paths/archive/\` when done, or link from CONTEXT/ROADMAP."
exit 1
