#!/usr/bin/env bash
# tool: role=check couples=check.sh runs-in=hook
source "$(git rev-parse --show-toplevel 2>/dev/null)/tools/tool-log.sh" 2>/dev/null && tool_log "$(basename "$0")" || true
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

# Only fire for the proof-spine files (post-#108 TIER paths — the flat Bang/X.lean
# list went stale after the restructure and silently killed this hook for months).
# Deliberately EXCLUDES the elaboration giants (AbstractMachine, EnvMachine,
# Frontend/TypeCheck): `lake env lean` on them takes minutes — lanes there run
# `just check FILE` / lean-lsp deliberately, not per-edit.
case "$file" in
  */Bang/Spec.lean|*/Bang/Core/IR.lean|*/Bang/Core/Typing.lean| \
  */Bang/Core/Semantics.lean|*/Bang/Core/Semantics/*.lean| \
  */Bang/Meta/LR.lean|*/Bang/Meta/BinaryLR.lean|*/Bang/Backend/Wasm.lean| \
  */Bang/Core/Grade.lean|*/Bang/Core/EffectRow.lean| \
  */Bang/Distribution.lean|*/Bang/Audit.lean)
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
