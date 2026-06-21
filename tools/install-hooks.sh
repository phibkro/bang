#!/usr/bin/env bash
# install-hooks.sh — link tracked git hooks into .git/hooks/
# Run once after cloning: bash tools/install-hooks.sh
# Skip a hook on demand: git commit --no-verify

set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

mkdir -p .git/hooks

for hook in tools/git-hooks/*; do
  name=$(basename "$hook")
  target=".git/hooks/$name"
  # Idempotent: replace symlink each time so updates to tools/git-hooks/ take effect.
  rm -f "$target"
  ln -s "../../$hook" "$target"
  chmod +x "$hook"
  echo "✓ installed $name → $hook"
done

echo ""
echo "Hooks installed. Skip with: git commit --no-verify"
