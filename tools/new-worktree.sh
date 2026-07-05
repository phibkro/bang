#!/usr/bin/env bash
# new-worktree.sh — the ONE blessed way to spawn an isolated IC worktree (#40b).
# ──────────────────────────────────────────────────────────────────────────────
# Many worktrees share one .git/objects. Two corruption vectors bit the store
# repeatedly (memory: shared-worktree-git-autogc-corruption):
#   (a) a FRESH worktree's first `lake build` hits the build recipe's
#       `[ -e .lake/… ] || lake exe cache get` — and cache-get-in-a-worktree
#       re-clones Mathlib + corrupts the shared store. This is the TRIGGER.
#   (b) `git add -A` then stages a phantom cache-tree entry that gc prunes.
# This script removes (a) at the source: it SEEDS .lake/packages from the main
# checkout so the fresh worktree's build sees oleans present and NEVER
# cache-gets. It also pins gc.auto=0 on the shared store.
#
# Seeding is a REFLINK COPY, not a symlink (2026-07-05 lesson): lake has a
# "URL has changed; deleting … and cloning again" codepath that DELETES and
# re-clones a package when the worktree's lake state disagrees — through a
# symlink that lands on the SHARED copy and nukes oleans + git state for every
# worktree at once (it did, twice in one day). A btrfs reflink copy is instant,
# costs no disk until divergence, and makes the blast radius per-worktree.
#
# Usage (run from the MAIN checkout):  tools/new-worktree.sh <dir> <branch> [base]
#   tools/new-worktree.sh ../lang-bang-foo foo-work main
#
# Discipline that still rides on YOU inside the worktree:
#   • commit by PATHSPEC (`git add <path>`), NEVER `git add -A` (vector (b)).
#   • NEVER `lake exe cache get` here (the build recipe + the PreToolUse guard
#     both refuse it now, but don't fight them — use `lake exe cache unpack`).
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"
main_root="$(pwd)"

dir="${1:?usage: tools/new-worktree.sh <dir> <branch> [base]}"
branch="${2:?usage: tools/new-worktree.sh <dir> <branch> [base]}"
base="${3:-main}"

# Must run from the MAIN checkout (git-dir == common-dir), with a built .lake to seed from.
gd="$(git rev-parse --git-dir)"; gcd="$(git rev-parse --git-common-dir)"
[ "$gd" = "$gcd" ] || { echo "❌ run from the MAIN checkout, not a linked worktree"; exit 1; }
[ -e .lake/packages/mathlib/.lake/build ] || {
  echo "❌ main checkout has no built .lake/packages/mathlib to seed from — run 'just build' first"; exit 1; }
[ -e "$dir" ] && { echo "❌ $dir already exists"; exit 1; }

git worktree add -b "$branch" "$dir" "$base"

# Seed: REFLINK-COPY the dependency tree so the worktree's first build finds
# oleans present (no cache-get) AND owns its copy outright — a lake re-clone in
# this worktree can only nuke ITSELF (see header). --reflink=auto: CoW-instant
# on btrfs (this repo's fs), silently a real copy elsewhere. Bang/'s own build
# artifacts go to the worktree's OWN .lake/build as before.
mkdir -p "$dir/.lake"
cp -r --reflink=auto "$main_root/.lake/packages" "$dir/.lake/packages"

git -C "$dir" config gc.auto 0
git -C "$dir" config gc.autoDetach false

echo "✓ worktree $dir  (branch $branch off $base)"
echo "  .lake/packages → seeded (reflink copy, isolated) · gc.auto=0 · gc.autoDetach=false"
echo "  → cd $dir && nix develop    [commit by pathspec; never 'lake exe cache get' here]"
