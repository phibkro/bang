#!/usr/bin/env bash
# tool: role=workflow couples=git-hooks/pre-commit runs-in=manual
# install-hooks.sh — link tracked git hooks into .git/hooks/
# Run once after cloning: bash tools/install-hooks.sh
# Skip a hook on demand: git commit --no-verify

set -euo pipefail
toplevel="$(git rev-parse --show-toplevel)"
cd "$toplevel"

# Hooks belong to the COMMON git dir, not `.git/hooks` — in a linked worktree `.git`
# is a gitfile (not a directory), so `mkdir -p .git/hooks` fails. `--git-common-dir`
# resolves to the shared dir (`<main>/.git`) from either the main tree or a worktree.
hooksdir="$(cd "$toplevel" && cd "$(git rev-parse --git-common-dir)" && pwd)/hooks"
mkdir -p "$hooksdir"

for hook in tools/git-hooks/*; do
  name=$(basename "$hook")
  target="$hooksdir/$name"
  # Idempotent: replace symlink each time so updates to tools/git-hooks/ take effect.
  # Absolute target so the link is valid regardless of the common dir's depth.
  rm -f "$target"
  ln -s "$toplevel/$hook" "$target"
  chmod +x "$hook"
  echo "✓ installed $name → $hook"
done

echo ""
echo "Hooks installed. Skip with: git commit --no-verify"
