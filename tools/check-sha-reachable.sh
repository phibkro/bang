#!/usr/bin/env bash
# check-sha-reachable.sh — orientation-doc SHA reachability fitness function.
# ──────────────────────────────────────────────────────────────────────────────
# CONTEXT.md and ROADMAP.md cite commit SHAs as waypoints ("banked at `91a6515`",
# "route-B de-risked at `ef71972`"). A rebase/drop/amend that orphans a cited SHA
# makes the described state SILENTLY false — the prose still reads fine, but the
# anchor it points at no longer exists. This climbs that from convention to test:
# every backtick-wrapped SHA-shaped token must resolve to a real commit object.
#
# Scope: backtick-wrapped lowercase-hex tokens, 7–40 chars (`91a6515` … full sha).
# A token is a SHA CLAIM iff it is all-hex of that length; verified via
# `git cat-file -e <sha>^{commit}`.
#
# False-positive guard: a 7-hex word that is English-hex (`deafbed`, `accede`)
# and isn't a commit would false-FAIL. Documented non-SHA hex goes ONCE in
# tools/sha-allow.txt (mirrors tools/refs-allow.txt: one token per line + reason);
# seed it only when a real false positive appears.
set -euo pipefail

ROOT="${1:-.}"
cd "$ROOT"
DOCS=(CONTEXT.md ROADMAP.md)
ALLOWFILE="tools/sha-allow.txt"

# ── allowlist: documented non-SHA hex tokens (substring/exact match) ──────────
allow=""
if [ -f "$ALLOWFILE" ]; then
  allow="$(sed -E 's/#.*$//; s/[[:space:]]+//g' "$ALLOWFILE" | grep -E '.' || true)"
fi
is_allowed() {  # $1 = bare token
  [ -n "$allow" ] && printf '%s\n' "$allow" | grep -qxF "$1"
}

# ── collect cited SHA-shaped tokens ───────────────────────────────────────────
tokens="$(grep -hoE '`[0-9a-f]{7,40}`' "${DOCS[@]}" 2>/dev/null \
  | tr -d '`' | sort -u || true)"

unreachable=""
checked=0
for t in $tokens; do
  is_allowed "$t" && continue
  checked=$((checked + 1))
  if ! git cat-file -e "${t}^{commit}" 2>/dev/null; then
    unreachable="${unreachable}${t}\n"
  fi
done

echo "── check-sha-reachable (orientation-doc SHA waypoints) ──"
if [ -z "$unreachable" ]; then
  echo "PASS: all $checked cited SHA(s) in ${DOCS[*]} resolve to commit objects."
  exit 0
fi
echo "FAIL: cited SHA(s) resolve to NO commit (rebased/dropped/amended — fix the waypoint, or"
echo "      if it is documented non-SHA hex, add it to $ALLOWFILE with a reason):"
printf "       ✗ %b" "$unreachable"
exit 1
