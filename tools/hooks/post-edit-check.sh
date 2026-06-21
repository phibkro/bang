#!/usr/bin/env bash
# Claude Code PostToolUse hook for Edit/Write of Lean files.
#
# Wired in `.claude/settings.json` to fire after Edit/Write tool calls.
# Reads the tool-use JSON from stdin; if the edited file is a Bang/*.lean,
# runs `tools/check.sh` on it. Output is visible to the agent — surfaces
# Lean errors immediately, without the agent having to manually invoke
# the checker.
#
# Quiet on success (no output); verbose only on errors. Keeps the agent's
# context budget intact for green files.

set -euo pipefail

input=$(cat)
file=$(echo "$input" | jq -r '.tool_input.file_path // empty' 2>/dev/null || echo "")

# Only fire for Bang/*.lean files (the kernel we care about; not legacy Calc*)
case "$file" in
  */Bang/Spec.lean|*/Bang/Core.lean|*/Bang/Syntax.lean|*/Bang/Operational.lean| \
  */Bang/LR.lean|*/Bang/Compile.lean|*/Bang/Mult.lean|*/Bang/Compat.lean| \
  */Bang/Distribution.lean|*/Bang/Audit.lean|*/Bang/EffectRow.lean|*/Bang/Eval.lean)
    ;;
  *) exit 0 ;;
esac

cd "${CLAUDE_PROJECT_DIR:-$(git rev-parse --show-toplevel)}" || exit 0

# Strip path prefix to get Bang-relative path
rel_file="${file#${CLAUDE_PROJECT_DIR:-}/}"

# Run check; only surface output if there's an error
out=$(nix develop --command bash tools/check.sh "$rel_file" 2>&1 || true)
errs=$(echo "$out" | grep -E '^(error|warning):' | head -10 || true)

if [ -n "$errs" ]; then
  echo "── PostToolUse: Lean check on $rel_file ──"
  echo "$errs"
  echo "── end ──"
fi
