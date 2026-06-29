#!/usr/bin/env bash
# check-git-hygiene.sh — multi-worktree git-store safety fitness function (#40).
# ──────────────────────────────────────────────────────────────────────────────
# This repo runs MANY git worktrees off ONE shared `.git/objects` (parallel proof
# ICs). In that setup a background auto-gc/repack is a CORRUPTION vector: it can
# prune loose objects another worktree's index/merge still references, mid-operation.
# It bit the store on 2026-06-27, -06-28, and -06-29 (the last lost 8925 blobs during
# a merge commit; recovered via `git fetch --refetch` + `git add -A` + push).
#
# `tools/setup.sh` disables it (`gc.auto 0`, `gc.autoDetach false`) — but that is a
# ONE-TIME convention: a fresh clone, a new worktree, or a git-version default reverts
# to gc-ENABLED silently. This climbs that safety from convention → TEST: every commit
# asserts the shared store still has gc disabled, failing LOUD (with the fix) if it drifted.
#
# Scope: the two config keys that govern the prune vector. Read from any worktree —
# `gc.auto`/`gc.autoDetach` are non-worktree-specific, so they live in the shared
# common config and one check covers every linked worktree.
set -euo pipefail

cd "${1:-.}"

auto="$(git config gc.auto 2>/dev/null || true)"
detach="$(git config gc.autoDetach 2>/dev/null || true)"

fail=0
if [ "$auto" != "0" ]; then
  echo "❌ check-git-hygiene: gc.auto is '${auto:-<unset>}', MUST be 0."
  echo "   Many worktrees share one .git/objects; background auto-gc prunes another"
  echo "   worktree's still-referenced loose objects mid-operation (corrupted the store 06-27/-29)."
  fail=1
fi
if [ "$detach" != "false" ]; then
  echo "❌ check-git-hygiene: gc.autoDetach is '${detach:-<unset>}', MUST be false."
  echo "   (a detached background gc races worktree writes invisibly)."
  fail=1
fi

if [ "$fail" = 1 ]; then
  echo "   FIX: bash tools/setup.sh   (or: git config gc.auto 0 && git config gc.autoDetach false)"
  exit 1
fi

echo "✓ check-git-hygiene: gc.auto=0, gc.autoDetach=false (multi-worktree store safe)"
