#!/usr/bin/env bash
# check-bang-root.sh — import-root coherence fitness function.
# ──────────────────────────────────────────────────────────────────────────────
# Climbs the "keep Bang.lean in sync" rule from CONVENTION (a comment asking you
# to remember) to TEST: every Bang/**/*.lean module must be imported in the
# library root Bang.lean, so a NEW file can't sit silently unbuilt (and therefore
# ungated — never compiled, never axiom-checked). A stale file that vanished from
# disk but lingers in an exclusion is flagged too.
#
# The one exception is the regression-witness allowlist, kept co-located IN
# Bang.lean as a marked line so the policy is a single edit in the root itself:
#
#     -- root-exclude: CapEscapeWitness LWRegress   (…rationale…)
#
# Those modules are built standalone (their own `#guard`s gate them); they are
# deliberately out of the build spine. Edit that line to add/remove an exclusion.
#
# FAIL if: a non-excluded module isn't imported (silently unbuilt), OR an excluded
# name doesn't exist on disk (stale exclusion). Exit 1 on either.
set -euo pipefail

ROOT="${1:-.}"
cd "$ROOT"
ROOTFILE="Bang.lean"

[ -f "$ROOTFILE" ] || { echo "── check-bang-root ──"; echo "FAIL: $ROOTFILE not found"; exit 1; }

# ── imported modules: `import Bang.X` / `import Bang.Sub.Y` → `X` / `Sub.Y` ────
imported="$(grep -E '^import Bang\.' "$ROOTFILE" \
  | sed -E 's/^import +Bang\.//; s/[[:space:]].*$//' | sort -u)"

# ── actual modules: find Bang -name '*.lean' → `X` / `Sub.Y` (drop Bang/, .lean,
#    '/'→'.'). This is the same dotted form the imports use.
actual="$(find Bang -name '*.lean' \
  | sed -E 's#^Bang/##; s#\.lean$##; s#/#.#g' | sort -u)"

# ── exclusion allowlist: parsed from the `-- root-exclude:` line in Bang.lean ──
exclude="$(grep -E '^-- root-exclude:' "$ROOTFILE" \
  | sed -E 's/^-- root-exclude://; s/\(.*$//' | tr ' ' '\n' | grep -E '.' | sort -u || true)"

# A module is "expected imported" iff it is actual AND not excluded.
expected="$(comm -23 <(printf '%s\n' "$actual") <(printf '%s\n' "$exclude"))"

# ── failures ──────────────────────────────────────────────────────────────────
# (a) expected-but-not-imported: a file that exists, isn't excluded, isn't imported.
missing="$(comm -23 <(printf '%s\n' "$expected") <(printf '%s\n' "$imported"))"
# (b) stale exclusion: an excluded name that no longer exists on disk.
stale_excl="$(comm -23 <(printf '%s\n' "$exclude") <(printf '%s\n' "$actual"))"

echo "── check-bang-root (import-root coherence) ──"
if [ -z "$missing" ] && [ -z "$stale_excl" ]; then
  n_imp="$(printf '%s\n' "$imported" | grep -c . || true)"
  n_exc="$(printf '%s\n' "$exclude" | grep -c . || true)"
  echo "PASS: all $n_imp modules imported in $ROOTFILE ($n_exc excluded witness(es): $(printf '%s ' $exclude))."
  exit 0
fi

if [ -n "$missing" ]; then
  echo "FAIL: module(s) exist but are NOT imported in $ROOTFILE (silently unbuilt — add an import, or exclude in the -- root-exclude: line):"
  printf '       + %s\n' $missing
fi
if [ -n "$stale_excl" ]; then
  echo "FAIL: -- root-exclude: names a module that no longer exists on disk (stale exclusion — drop it):"
  printf '       - %s\n' $stale_excl
fi
exit 1
