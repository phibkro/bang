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
#   (C) FAIL — refs ≡ files. Every "ADR-NNNN" mentioned ANYWHERE in `Bang/` + `docs/`
#       (not just docs/decisions/) must resolve to a `docs/decisions/NNNN-*.md` file,
#       OR be documented history (deleted/collapsed ADRs 0003/0004/0010–0014, or the
#       adr-template `ADR-0123` placeholder). An UNDOCUMENTED dangling ref is how the
#       0056/0057/0060 phantoms accrued — a ref with no file and no allowlist entry →
#       exit 1. `just adr-check` guards ledger ≡ files; this guards refs ≡ files (the
#       gap that let phantom ADRs live in code/docs with no decision record). ADR-0042.
#
# Exit 1 on (A)/(B)/(C). Documented-history refs in (C) print an informational note
# and do NOT fail (they are the recorded, intentional culls).
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

# ── (C) refs ≡ files (FAIL on undocumented dangling) ─────────────────────────
# Numbers mentioned as `ADR-NNNN` / `ADRs NNNN` / `ADR NNNN` anywhere in `Bang/` +
# `docs/` (broader than just docs/decisions/ — that narrow scope is exactly how the
# 0056/0057/0060 phantoms hid in code comments and notes with no decision record).
# A ref is OK if it resolves to a file. Otherwise it must be DOCUMENTED history
# (README "Recent culls" note or the template's `ADR-0123` placeholder) → informational.
# Anything else is an UNDOCUMENTED dangling ref → exit 1.
ref_roots=""
for r in "$ROOT/Bang" "$ROOT/docs"; do
  [ -e "$r" ] && ref_roots="$ref_roots $r"
done
refs="$(grep -rhoE 'ADRs?[- ][0-9]{4}|ADRs? [0-9]{4}' $ref_roots 2>/dev/null \
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

noted=0
for n in $refs; do
  # Skip if any file starts with NNNN- (the ref resolves to a live ADR).
  if ls "$DIR/$n"-*.md >/dev/null 2>&1; then continue; fi
  if printf '%s\n' "$documented" | grep -qx "$n"; then
    if [ "$noted" -eq 0 ]; then
      echo "note: refs to ADRs with no file (documented history — see README 'Recent culls'):"
      noted=1
    fi
    echo "       ADR-$n (intentional: deleted/collapsed or template placeholder)"
  else
    echo "FAIL: ADR-$n is referenced in Bang/ or docs/ but has NO docs/decisions/$n-*.md file"
    echo "       (a phantom ADR — write the decision record, or add $n to the documented-history allowlist if intentionally culled)"
    fail=1
  fi
done

if [ "$fail" -eq 0 ]; then
  echo "adr-links: OK — index ↔ file bijection clean, in-repo links resolve, all ADR refs in Bang/+docs/ have files${noted:+ (documented-history notes above)}"
  exit 0
fi
exit 1
