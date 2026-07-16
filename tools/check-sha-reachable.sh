#!/usr/bin/env bash
# tool: role=check couples=CONTEXT.md,ROADMAP.md,sha-allow.txt,provenance.py runs-in=fitness
source "$(git rev-parse --show-toplevel 2>/dev/null)/tools/tool-log.sh" 2>/dev/null && tool_log "$(basename "$0")" || true
# Orientation-doc provenance gate. Untyped SHA tokens are commit claims and must
# resolve uniquely to ancestors of the declared stable endpoint. The proof-state's
# typed tree claim is checked separately against that endpoint's exact Bang tree.

set -euo pipefail

ROOT="${1:-.}"
cd "$ROOT"
DOCS=(CONTEXT.md ROADMAP.md)
ALLOWFILE="tools/sha-allow.txt"
STABLE_REF="${PROVENANCE_STABLE_REF:-HEAD}"
EVIDENCE_END="${PROVENANCE_END:-HEAD}"

if [[ $(git rev-parse --is-shallow-repository) == true ]]; then
  echo "── check-sha-reachable (canonical orientation provenance) ──"
  echo "FAIL: canonical ancestry/provenance requires a complete, non-shallow history."
  exit 1
fi

if ! stable_commit=$(git rev-parse --verify "${STABLE_REF}^{commit}" 2>/dev/null); then
  echo "── check-sha-reachable (canonical orientation provenance) ──"
  echo "FAIL: stable endpoint '$STABLE_REF' is not a complete local commit."
  exit 1
fi
if ! evidence_commit=$(git rev-parse --verify "${EVIDENCE_END}^{commit}" 2>/dev/null); then
  echo "── check-sha-reachable (canonical orientation provenance) ──"
  echo "FAIL: evidence endpoint '$EVIDENCE_END' is not a complete local commit."
  exit 1
fi

allow=""
if [[ -f "$ALLOWFILE" ]]; then
  allow=$(sed -E 's/#.*$//; s/[[:space:]]+//g' "$ALLOWFILE" | grep -E '.' || true)
fi
is_allowed() {
  [[ -n "$allow" ]] && printf '%s\n' "$allow" | grep -qxF "$1"
}

tokens=$(grep -hoE '`[0-9a-f]{7,40}`' "${DOCS[@]}" 2>/dev/null | tr -d '`' | sort -u || true)
failures=()
checked=0
for token in $tokens; do
  is_allowed "$token" && continue
  checked=$((checked + 1))
  mapfile -t matches < <(git rev-parse --disambiguate="$token" 2>/dev/null || true)
  if (( ${#matches[@]} != 1 )); then
    failures+=("$token (object prefix has ${#matches[@]} matches; expected exactly one)")
    continue
  fi
  resolved=${matches[0]}
  if [[ $(git cat-file -t "$resolved" 2>/dev/null || true) != commit ]]; then
    failures+=("$token (unique object is not a commit)")
    continue
  fi
  if ! git merge-base --is-ancestor "$resolved" "$stable_commit"; then
    failures+=("$token (commit is not an ancestor of ${stable_commit:0:12})")
  fi
done

tree_claims=$(grep -hoE '`tree:[0-9a-f]{40,64}`' "${DOCS[@]}" 2>/dev/null \
  | sed -E 's/^`tree:|`$//g' | sort -u || true)
tree_checked=0

proof_tree=$(grep -hoE 'Proof-state for Bang tree `tree:[0-9a-f]{40,64}`' CONTEXT.md 2>/dev/null \
  | sed -E 's/.*`tree:([0-9a-f]+)`/\1/' || true)
if [[ -n "$proof_tree" ]]; then
  if [[ $(printf '%s\n' "$proof_tree" | wc -l) -ne 1 ]]; then
    failures+=("proof-state has multiple Bang tree claims")
  elif ! expected_tree=$(git rev-parse --verify "${evidence_commit}:Bang" 2>/dev/null); then
    failures+=("evidence endpoint has no Bang tree")
  elif [[ "$proof_tree" != "$expected_tree" ]]; then
    failures+=("proof-state Bang tree is not ${evidence_commit:0:12}:Bang")
  fi
else
  failures+=("proof-state has no typed Bang tree claim")
fi
for object_id in $tree_claims; do
  tree_checked=$((tree_checked + 1))
  if [[ "$object_id" != "$proof_tree" ]]; then
    failures+=("tree:$object_id (untyped-purpose tree claims are forbidden)")
  elif [[ $(git cat-file -t "$object_id" 2>/dev/null || true) != tree ]]; then
    failures+=("tree:$object_id (missing or wrong object type)")
  fi
done

echo "── check-sha-reachable (canonical orientation provenance) ──"
if (( ${#failures[@]} == 0 )); then
  echo "PASS: $checked commit claim(s) are canonical ancestors; $tree_checked typed tree claim(s) are exact/reachable."
  exit 0
fi
echo "FAIL: provenance claim(s) are not bound to stable endpoint ${stable_commit}:"
printf '       ✗ %s\n' "${failures[@]}"
exit 1
