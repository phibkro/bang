#!/usr/bin/env bash
# tool: role=workflow couples=none runs-in=manual
source "$(git rev-parse --show-toplevel 2>/dev/null)/tools/tool-log.sh" 2>/dev/null && tool_log "$(basename "$0")" || true
# new-worktree.sh — the ONE blessed way to spawn an isolated IC checkout (#40b).
# ──────────────────────────────────────────────────────────────────────────────
# DEFAULT MODE IS NOW A FULL LOCAL CLONE (2026-07-09). The linked-worktree mode
# shares .git/objects, and that shared store produced TEN index-poisoning
# incidents (memory: shared-worktree-git-autogc-corruption) — the last two
# (fx52, fuzz14) hit AT COMMIT TIME with every known trigger already guarded
# (no cache-get, pathspec-only adds, gc.auto=0). A clone owns its objects
# outright: `git clone` on a local path HARDLINKS immutable object files
# (near-zero disk, no alternates), so a missing-object ghost in one IC's store
# is structurally impossible to inflict on another's — and any object actually
# missing fails LOUDLY at clone time, not mid-commit.
#
#   tools/new-worktree.sh <dir> <branch> [base]            # full clone (DEFAULT)
#   tools/new-worktree.sh --shared <dir> <branch> [base]   # legacy linked worktree
#
# `base` is any local commit-ish (branch, tag, or SHA); it is resolved before
# cloning so detached exact-SHA callers get the same isolated-lane path.
#
# Clone mode: origin is re-pointed at the GitHub remote (push-per-slice works),
# and the local main checkout stays reachable as remote `local`.
#
# Both modes SEED .lake/packages from the main checkout as a REFLINK COPY
# (2026-07-05 lesson): lake's "URL has changed; deleting … and cloning again"
# codepath must only ever be able to nuke the IC's OWN copy. --reflink=auto is
# CoW-instant on btrfs (this repo's fs), silently a real copy elsewhere.
#
# Discipline that still rides on YOU inside the checkout:
#   • commit by PATHSPEC (`git add <path>`), never `git add -A`.
#   • NEVER `lake exe cache get` (build recipe + PreToolUse guard refuse it).
set -euo pipefail

mode="clone"
if [ "${1:-}" = "--shared" ]; then mode="shared"; shift; fi

cd "$(git rev-parse --show-toplevel)"
main_root="$(pwd)"

dir="${1:?usage: tools/new-worktree.sh [--shared] <dir> <branch> [base]}"
branch="${2:?usage: tools/new-worktree.sh [--shared] <dir> <branch> [base]}"
base="${3:-main}"
base_commit="$(git rev-parse --verify "${base}^{commit}")" || {
  echo "❌ base does not resolve to a local commit: $base"
  exit 1
}

# Must run from the MAIN checkout (git-dir == common-dir), with a built .lake to seed from.
gd="$(git rev-parse --git-dir)"; gcd="$(git rev-parse --git-common-dir)"
[ "$gd" = "$gcd" ] || { echo "❌ run from the MAIN checkout, not a linked worktree"; exit 1; }
[ -e .lake/packages/mathlib/.lake/build ] || {
  echo "❌ main checkout has no built .lake/packages/mathlib to seed from — run 'just build' first"; exit 1; }
[ -e "$dir" ] && { echo "❌ $dir already exists"; exit 1; }

github_url="$(git remote get-url origin)"

if [ "$mode" = "clone" ]; then
  # Full local clone: hardlinked objects, OWN store, no alternates. Verifies
  # every needed object exists NOW (a corrupt source fails here, loudly).
  # Resolve before cloning, then branch from the exact commit so a detached
  # candidate SHA works identically to a named source branch.
  git clone --no-checkout "$main_root" "$dir"
  git -C "$dir" remote rename origin local
  git -C "$dir" remote add origin "$github_url"
  git -C "$dir" fetch origin --quiet
  git -C "$dir" checkout -b "$branch" "$base_commit"
else
  git worktree add -b "$branch" "$dir" "$base_commit"
fi

# Seed: REFLINK-COPY the dependency tree so the first build finds oleans
# present (no cache-get) and owns its copy outright (see header). Bang/'s own
# build artifacts go to the checkout's OWN .lake/build as before.
mkdir -p "$dir/.lake"
cp -r --reflink=auto "$main_root/.lake/packages" "$dir/.lake/packages"

git -C "$dir" config gc.auto 0
git -C "$dir" config gc.autoDetach false

echo "✓ $mode checkout $dir  (branch $branch off $base @ ${base_commit:0:8})"
echo "  .lake/packages → seeded (reflink copy, isolated) · gc.auto=0 · gc.autoDetach=false"
if [ "$mode" = "clone" ]; then
  echo "  own object store (hardlinked) · origin → $github_url · local main → remote 'local'"
fi
echo "  → cd $dir && nix develop    [commit by pathspec; never 'lake exe cache get' here]"
