#!/usr/bin/env bash
# check-all-modules.sh — structural fitness for the module-system migration (Phase 1a).
#
# POLICY (operator, modules-everywhere): every `Bang/**/*.lean` must carry a Lean
# module header — a line that is exactly `module` — UNLESS it is on the documented
# exception allowlist below. This makes "the tree is module-ified" a STRUCTURAL gate
# instead of a remembered convention: a new .lean file without a `module` header (or a
# file that silently loses one) turns this RED until it is fixed or explicitly allowlisted.
#
# The `module` keyword may follow a leading doc-comment, so we scan the WHOLE file for a
# standalone `^module$` line (not just line 1) — that is the header on every module file
# in this tree and appears nowhere else (it is not a Lean term).
#
# Set-equality, like check-primitives.sh: a STALE allowlist entry (a file that now HAS a
# header, or no longer exists) is flagged too, so the exception set can't rot.
set -euo pipefail

ROOT="${1:-.}"
cd "$ROOT"

# ── The exception allowlist: files that GENUINELY cannot be modules, with the reason.
# Operator intent is ZERO exceptions; each line here is a reviewed, justified carve-out.
#
#   Bang/Frontend/Surface/PropTest.lean
#     The Plausible `#test` STACK-LAWS harness. Plausible's `Gen`/`Arbitrary` API is
#     `meta` in v4.30, and a `meta` generator may not call the RUNTIME stack constructors
#     (push/empty/pop) it must build samples from. That meta/runtime phase split is
#     irreducible — the property-test generators bridge compile-time sampling and runtime
#     values — so this file cannot be a `module`. It IS the verified-spine / tested-
#     superset seam made structural (the tested rung lives outside the module spine).
#     TEMPORARY — retired by #80: when the stress-test / property-fuzz harness moves to a
#     SEPARATE test target OUTSIDE Bang/, these Surface property-tests move with it and
#     Bang/ becomes 0-exception, all-module. PropTest's location here is a way-station,
#     not a permanent home — do not over-invest in it.
ALLOWLIST="$(cat <<'EOF'
Bang/Frontend/Surface/PropTest.lean
EOF
)"

allow="$(printf '%s\n' "$ALLOWLIST" | grep -v '^[[:space:]]*$' | sort -u)"

missing=""   # non-allowlisted files with NO module header  → violations
stale_has="" # allowlisted files that DO have a header        → allowlist is stale
stale_gone="" # allowlisted files that no longer exist        → allowlist is stale

while IFS= read -r f; do
  f="${f#./}"
  if grep -qxE 'module[[:space:]]*' "$f"; then has=1; else has=0; fi
  if printf '%s\n' "$allow" | grep -qxF "$f"; then
    # allowlisted: it should NOT have a header (else the carve-out is obsolete)
    [ "$has" -eq 1 ] && stale_has="$stale_has $f"
  else
    [ "$has" -eq 0 ] && missing="$missing $f"
  fi
done < <(find Bang -name '*.lean' | sort)

# allowlisted files that have vanished
while IFS= read -r a; do
  [ -z "$a" ] && continue
  [ -f "$a" ] || stale_gone="$stale_gone $a"
done < <(printf '%s\n' "$allow")

total="$(find Bang -name '*.lean' | wc -l | tr -d ' ')"
nexc="$(printf '%s\n' "$allow" | grep -c . || true)"

if [ -z "$missing" ] && [ -z "$stale_has" ] && [ -z "$stale_gone" ]; then
  echo "modules: OK — $((total - nexc))/$total Bang/*.lean carry a \`module\` header; $nexc documented exception(s)."
  exit 0
fi

echo "FAIL: module-header policy (every Bang/*.lean is a \`module\` or an allowlisted exception)."
if [ -n "$missing" ]; then
  echo "  ── MISSING \`module\` header (add one, or allowlist with a reason in tools/check-all-modules.sh):"
  printf '       + %s\n' $missing
fi
if [ -n "$stale_has" ]; then
  echo "  ── STALE allowlist (file is NOW a module — remove it from the exception list):"
  printf '       - %s\n' $stale_has
fi
if [ -n "$stale_gone" ]; then
  echo "  ── STALE allowlist (file no longer exists — remove it from the exception list):"
  printf '       - %s\n' $stale_gone
fi
exit 1
