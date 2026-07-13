#!/usr/bin/env bash
# tool: role=release couples=CHANGELOG.md,justfile runs-in=manual
# release.sh — the release battery (plan 011).
#
# `just release vX.Y.Z` does everything EXCEPT publish:
#   1. asserts clean main + verification, then ALWAYS rebuilds and checks tag↔binary identity,
#      the strict production site, and strict doc pins (`--skip-verify` skips only the broad suite)
#   2. extracts this version's notes = the conventional-commit entries since the PREVIOUS
#      tag (`git describe --tags --abbrev=0`), reusing gen-changelog.py's own render() so
#      the notes are the SAME derivation as CHANGELOG.md, not a second copy of the regex
#      (CHANGELOG.md itself has no per-version sections — it is one flat "Unreleased"
#      block against a fixed baseline sha, see tools/gen-changelog.py:34-37 — so this
#      script re-scopes the same extraction to <prev-tag>..HEAD rather than slicing the
#      rendered file)
#   3. creates an ANNOTATED LOCAL tag carrying those notes as the tag message
#   4. prints — but does NOT run — the `git push` and `gh release create` commands
#
# The operator's finger stays on the publish button: this script's job ends at a local
# tag + printed commands. See plans/011-public-early-plumbing.md HARD RULE.
#
# Usage:
#   tools/release.sh vX.Y.Z              # normal
#   tools/release.sh vX.Y.Z --skip-verify  # skip `just verify` (loud warning, still gates clean+main)
set -euo pipefail

VERSION="${1:-}"
SKIP_VERIFY=0
if [[ "${2:-}" == "--skip-verify" ]]; then
  SKIP_VERIFY=1
fi

if [[ -z "$VERSION" ]]; then
  echo "usage: tools/release.sh vX.Y.Z [--skip-verify]" >&2
  exit 1
fi

if [[ ! "$VERSION" =~ ^v[0-9]+\.[0-9]+\.[0-9]+$ ]]; then
  echo "release: '$VERSION' must be a stable vX.Y.Z tag (got: $VERSION)" >&2
  exit 1
fi

ROOT="$(git rev-parse --show-toplevel)"
cd "$ROOT"

# --- gate 1: clean tree ---
if [[ -n "$(git status --porcelain)" ]]; then
  echo "release: working tree is not clean — commit or stash first." >&2
  git status --porcelain >&2
  exit 1
fi

# --- gate 2: on main ---
BRANCH="$(git branch --show-current)"
if [[ "$BRANCH" != "main" ]]; then
  echo "release: must be on 'main' (currently on '$BRANCH')." >&2
  exit 1
fi

# --- gate 3: tag doesn't already exist ---
if git rev-parse -q --verify "refs/tags/$VERSION" >/dev/null; then
  echo "release: tag $VERSION already exists locally." >&2
  exit 1
fi

# --- gate 4: broad verification (the ONLY gate --skip-verify waives) ---
if [[ "$SKIP_VERIFY" -eq 1 ]]; then
  echo "release: WARNING — --skip-verify skips ONLY 'just verify'." >&2
  echo "         Fresh build, tag↔binary identity, strict site, and doc-pin gates remain mandatory." >&2
  echo "         Use only for a throwaway/test tag; it carries no broad green guarantee." >&2
else
  echo "release: running 'just verify' (this can take a while — cold build is minutes)…"
  if ! just verify; then
    echo "release: 'just verify' failed — fix it before tagging, or pass --skip-verify" \
         "(loudly, for a non-release tag only)." >&2
    exit 1
  fi
fi

# --- gate 5: fresh runner + exact compiler provenance ---
echo "release: rebuilding the runner before checking $VERSION identity…"
lake build bang
bash tools/check-release-version.sh "$VERSION" .lake/build/bin/bang

# --- gate 6: production docs must render every diagram ---
if ! just site-build; then
  echo "release: strict site build failed — no tag created." >&2
  exit 1
fi

# --- gate 7: doc pins STRICT — a release may not ship prose known-stale against its
# own sources (warn-tier in fitness becomes fail-tier here; restamp or amend first).
if ! python3 tools/check-doc-pins.py --strict; then
  echo "release: stale doc pins — re-verify + restamp the flagged notes before tagging." >&2
  exit 1
fi

# --- extract notes: conventional-commit entries since the previous tag ---
PREV_TAG="$(git describe --tags --abbrev=0 2>/dev/null || true)"
if [[ -n "$PREV_TAG" ]]; then
  RANGE_START="$PREV_TAG"
else
  RANGE_START=""  # no prior tag: gen-changelog's own BASELINE applies (entries() default)
fi

NOTES="$(python3 - "$ROOT" "$RANGE_START" "$VERSION" <<'PYEOF'
import importlib.util
import os
import sys

root, range_start, version = sys.argv[1], sys.argv[2], sys.argv[3]

spec = importlib.util.spec_from_file_location(
    "gen_changelog", os.path.join(root, "tools", "gen-changelog.py"))
gen_changelog = importlib.util.module_from_spec(spec)
sys.path.insert(0, os.path.join(root, "tools"))  # gen-changelog imports genblock
spec.loader.exec_module(gen_changelog)

if range_start:
    # Reuse commits()/entries() but scoped to <prev-tag>..HEAD instead of BASELINE..HEAD —
    # the same ENTRY_RE/SECTIONS derivation, just re-windowed to this release.
    import subprocess
    res = subprocess.run(
        ["git", "-C", root, "log", f"{range_start}..HEAD", "--reverse", "--format=%h\x1f%s"],
        capture_output=True, text=True)
    lines = res.stdout.splitlines() if res.returncode == 0 else []
    buckets = {t: [] for t, _ in gen_changelog.SECTIONS}
    for line in lines:
        m = gen_changelog.ENTRY_RE.match(line)
        if not m or m.group("type") not in buckets:
            continue
        buckets[m.group("type")].append(
            (m.group("scope"), m.group("subject"), m.group("sha"), bool(m.group("bang"))))
else:
    buckets = gen_changelog.entries(root)

out = [f"bang {version}", ""]
populated = False
for t, heading in gen_changelog.SECTIONS:
    if not buckets[t]:
        continue
    populated = True
    out.append(f"{heading}:")
    for scope, subject, sha, bang in buckets[t]:
        mark = "[BREAKING] " if bang else ""
        pre = f"{scope}: " if scope else ""
        out.append(f"- {mark}{pre}{subject} ({sha})")
    out.append("")
if not populated:
    out.append("No conventional feat/fix/perf commits since the previous tag.")
print("\n".join(out).rstrip() + "\n")
PYEOF
)"

echo "release: notes for $VERSION (since ${PREV_TAG:-the MVP baseline}):"
echo "──────────────────────────────────────────────────────────────────"
echo "$NOTES"
echo "──────────────────────────────────────────────────────────────────"

# --- create the annotated local tag ---
git tag -a "$VERSION" -m "$NOTES"
echo "release: created local annotated tag $VERSION."

# --- print (do not run) the publish commands ---
NOTES_FILE="$(mktemp -t "release-notes-${VERSION}-XXXXXX.txt")"
printf '%s' "$NOTES" > "$NOTES_FILE"

cat <<EOF

release: tag created LOCALLY ONLY. Nothing has been pushed or published.
To publish, review the notes above, then run:

    git push origin $VERSION
    gh release create $VERSION --title "bang $VERSION" --notes-file "$NOTES_FILE"

(notes staged at $NOTES_FILE)
EOF
