#!/usr/bin/env bash
# tool: role=devenv couples=tools/new-worktree.sh,justfile runs-in=manual
# seed-lake.sh — reflink-seed THIS worktree's .lake from the MAIN checkout's.
#
# Run from inside a fresh (harness- or hand-made) linked worktree BEFORE the first
# build. Copies the main checkout's .lake/packages (mathlib + deps, ~2G) AND
# .lake/build (Bang's own oleans) as --reflink=auto COPIES — on btrfs a CoW
# metadata operation, seconds not minutes — so the worktree's first `lake build`
# finds everything present and rebuilds only what its tree actually changes.
#
# COPY, never symlink: lake's "URL has changed → delete and re-clone" codepath
# deletes THROUGH a symlink and nukes the shared copy for every worktree (the
# 2026-07-05 incident); a reflink copy scopes any deletion to this worktree.
#
# Staleness is SAFE BY CONSTRUCTION: lake trace-hash-verifies artifacts against
# sources and rebuilds any mismatch — a stale (or even torn, if main was
# mid-build) seed can only cause a partial rebuild, never a wrong build.
#
# After seeding: `lake build` directly. NEVER `lake exe cache get` in a seeded
# worktree (the historic corruption trigger; the packages are already here).
set -euo pipefail

common_git_dir="$(git rev-parse --git-common-dir)"
main_root="$(dirname "$(realpath "$common_git_dir")")"
here="$(git rev-parse --show-toplevel)"

if [ "$(realpath "$here")" = "$main_root" ]; then
  echo "seed-lake: this IS the main checkout ($main_root) — nothing to seed."; exit 0
fi
[ -d "$main_root/.lake/packages/mathlib" ] || {
  echo "❌ seed-lake: main checkout has no built .lake/packages/mathlib — run 'just build' there first."; exit 1; }

mkdir -p "$here/.lake"
for part in packages build; do
  if [ -e "$here/.lake/$part" ]; then
    echo "seed-lake: .lake/$part already present — leaving it (idempotent)."
  elif [ -d "$main_root/.lake/$part" ]; then
    cp -r --reflink=auto "$main_root/.lake/$part" "$here/.lake/$part"
    echo "seed-lake: .lake/$part ← seeded (reflink copy from $main_root)."
  else
    echo "seed-lake: main has no .lake/$part — skipped."
  fi
done
echo "seed-lake: done. Next: 'nix develop --command lake build' (NO cache get)."
