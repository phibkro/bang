#!/usr/bin/env bash
# check-adr-links.sh — ADR integrity lint for docs/decisions/.
#
# The maintenance instance flagged: this repo DELETED ADR-0003/0004 (and collapsed
# 0010–0014); research says supersede-don't-delete, and there was no lint guarding
# the index ↔ file ↔ cross-reference web from drifting. This adds one.
#
# THREE checks, graded by whether the finding is breakage or history:
#
#   (A) FAIL — file ↔ index bijection. Every `docs/decisions/NNNN-*.md` has a
#       README index row, and every index row points to a file that exists.
#       A missing row or a row for a vanished file is a real drift → exit 1.
#
#   (B) FAIL — markdown link targets resolve. Every `](NNNN-….md)` link inside the
#       decisions dir points to a file that exists → a dead in-repo link is breakage.
#
#   (C) WARN — cross-reference resolution. Every "ADR-NNNN" mentioned in prose either
#       has a file, OR is documented history (the README "Recent culls" note, or the
#       adr-template placeholder). Unknown dangling refs are REPORTED, not failed —
#       deleted-ADR history (0003/0004/0010–0014) is intentional and pre-existing
#       (the brief: report it, don't fail the build on pre-existing history).
#
# Exit 1 only on (A)/(B). (C) prints WARN lines and still exits 0.
set -euo pipefail

ROOT="${1:-.}"
DIR="$ROOT/docs/decisions"
README="$DIR/README.md"

[ -d "$DIR" ]    || { echo "FAIL: $DIR not found"; exit 1; }
[ -f "$README" ] || { echo "FAIL: $README not found"; exit 1; }

fail=0

# ── (A) file ↔ index bijection ───────────────────────────────────────────────
# Files: every NNNN-*.md except the README itself.
files="$(cd "$DIR" && ls | grep -E '^[0-9]{4}-.*\.md$' | grep -oE '^[0-9]{4}' | sort -u)"
# Index rows: lines like `| [NNNN](NNNN-….md) | … |`.
rows="$(grep -oE '^\| \[[0-9]{4}\]' "$README" | grep -oE '[0-9]{4}' | sort -u)"

missing_row="$(comm -23 <(printf '%s\n' "$files") <(printf '%s\n' "$rows"))"
missing_file="$(comm -13 <(printf '%s\n' "$files") <(printf '%s\n' "$rows"))"

if [ -n "$missing_row" ]; then
  echo "FAIL: ADR files with NO README index row:"
  printf '       %s\n' $missing_row
  fail=1
fi
if [ -n "$missing_file" ]; then
  echo "FAIL: README index rows pointing to a MISSING ADR file:"
  printf '       %s\n' $missing_file
  fail=1
fi

# ── (B) markdown link targets resolve ────────────────────────────────────────
# Every `](NNNN-….md)` link in the dir must name an existing file.
dead_links=""
while IFS= read -r target; do
  [ -z "$target" ] && continue
  [ -f "$DIR/$target" ] || dead_links="$dead_links $target"
done < <(grep -rhoE '\]\([0-9]{4}-[A-Za-z0-9-]+\.md\)' "$DIR"/*.md \
           | sed -E 's/^\]\(//; s/\)$//' | sort -u)

if [ -n "$dead_links" ]; then
  echo "FAIL: dead markdown links to non-existent ADR files:"
  printf '       %s\n' $dead_links
  fail=1
fi

# ── (C) cross-reference resolution (WARN-only) ───────────────────────────────
# Numbers mentioned as `ADR-NNNN` / `ADRs NNNN` / `ADR NNNN`. A ref is OK if it
# has a file. Otherwise it must be DOCUMENTED history: named in the README
# "Recent culls" note, or the template's `ADR-0123` placeholder. Anything else
# is reported as a genuine dangling cross-reference (still exit 0).
refs="$(grep -rhoE 'ADRs?[- ][0-9]{4}|ADRs? [0-9]{4}' "$DIR"/*.md \
          | grep -oE '[0-9]{4}' | sort -u)"

# Documented-history allowlist: the culls (0003/0004 deleted, 0010–0014 collapsed)
# + the adr-template placeholder (0123). These are intentional, recorded in README.
documented="0003
0004
0010
0011
0012
0013
0014
0123"

warned=0
for n in $refs; do
  # Skip if any file starts with NNNN- (the ref resolves to a live ADR).
  if ls "$DIR/$n"-*.md >/dev/null 2>&1; then continue; fi
  if printf '%s\n' "$documented" | grep -qx "$n"; then
    if [ "$warned" -eq 0 ]; then
      echo "WARN: cross-references to ADRs with no file (documented history — see README 'Recent culls'):"
      warned=1
    fi
    echo "       ADR-$n (intentional: deleted/collapsed or template placeholder)"
  else
    if [ "$warned" -eq 0 ]; then
      echo "WARN: cross-references to ADRs with no file:"
      warned=1
    fi
    echo "       ADR-$n (UNDOCUMENTED dangling ref — add to README culls note or fix)"
  fi
done

if [ "$fail" -eq 0 ]; then
  echo "adr-links: OK — index ↔ file bijection clean, all in-repo links resolve${warned:+ (see WARN above)}"
  exit 0
fi
exit 1
