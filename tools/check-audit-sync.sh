#!/usr/bin/env bash
# check-audit-sync.sh — keep the soundness gate ≡ the headline-theorem set.
#
# The maintenance instance flagged: Audit.lean's `#print axioms` list is
# hand-maintained (convention rung) — a NEW headline theorem added to Spec.lean
# can be silently forgotten in the gate, shipping an ungated soundness claim.
# This lifts the sync from convention → test (the SoT ladder: drift caught at CI).
#
# THE RULE (forward direction only): every top-level `theorem` in Bang/Spec.lean
# — the verification spine — must appear as a `#print axioms <name>` line in
# Bang/Audit.lean. Extra Audit entries (Surface, CalcVM, …) are fine; this guards
# the one drift that matters: a spine theorem that nobody gates.
#
# Exit 1 if any Spec headline theorem is missing from the gate.
set -euo pipefail

ROOT="${1:-.}"
SPEC="$ROOT/Bang/Spec.lean"
AUDIT="$ROOT/Bang/Audit.lean"

[ -f "$SPEC" ]  || { echo "FAIL: $SPEC not found"; exit 1; }
[ -f "$AUDIT" ] || { echo "FAIL: $AUDIT not found"; exit 1; }

# Spec headline theorems: top-level `theorem <name>` (Spec is `namespace Bang`,
# so names are bare). Strip to the bare name.
spec_names="$(grep -oE '^theorem [A-Za-z_][A-Za-z0-9_]*' "$SPEC" \
                | awk '{print $2}' | sort -u)"

# Audited names: the argument of each `#print axioms <arg>`, reduced to its bare
# last component (drop any `Bang.` / `Bang.Surface.` / … namespace prefix) so it
# matches a Spec bare name.
audit_names="$(grep -oE '^#print axioms [A-Za-z_][A-Za-z0-9_.]*' "$AUDIT" \
                 | awk '{print $3}' | sed -E 's/.*\.//' | sort -u)"

missing="$(comm -23 <(printf '%s\n' "$spec_names") <(printf '%s\n' "$audit_names"))"

if [ -n "$missing" ]; then
  echo "FAIL: Spec.lean headline theorems MISSING from Audit.lean's #print axioms gate:"
  printf '       %s\n' $missing
  echo "       → add a '#print axioms <name>' line to Bang/Audit.lean, or it ships ungated."
  exit 1
fi

echo "audit-sync: OK — all $(printf '%s\n' "$spec_names" | grep -c .) Spec headline theorems are gated in Audit.lean"
exit 0
