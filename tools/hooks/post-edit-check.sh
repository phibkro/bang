#!/usr/bin/env bash
# tool: role=check couples=check.sh,autoquality.sh,.claude/settings.json runs-in=hook
source "$(git rev-parse --show-toplevel 2>/dev/null)/tools/tool-log.sh" 2>/dev/null && tool_log "$(basename "$0")" || true
# Claude Code PostToolUse feedback for Edit/Write.
#
# - selected proof-spine Lean files get the existing fast Lean check;
# - changed Python/shell files get pinned formatter/linter feedback.
#
# All failures are advisory: diagnostics return as additional agent context, while
# the blocking repository-wide versions run through `just fitness` at pre-commit.

set -euo pipefail

input=$(cat)
file=$(jq -r '.tool_input.file_path // empty' <<<"$input" 2>/dev/null || true)
[[ -n "$file" ]] || exit 0

root=$(realpath -m -- "${CLAUDE_PROJECT_DIR:-$(git rev-parse --show-toplevel)}")
resolved=$(realpath -m -- "$root/$file")
if [[ "$file" = /* ]]; then
  resolved=$(realpath -m -- "$file")
fi
case "$resolved" in
  "$root"/*) rel_file=${resolved#"$root"/} ;;
  *) exit 0 ;;
esac
[[ -f "$root/$rel_file" ]] || exit 0

emit_context() {
  local message=$1
  jq -n --arg message "$message" '{
    hookSpecificOutput: {
      hookEventName: "PostToolUse",
      additionalContext: $message
    }
  }'
}

case "$rel_file" in
  *.py|*.sh|tools/git-hooks/*)
    if ! out=$(
      cd "$root" && nix develop --command bash tools/autoquality.sh "$rel_file" 2>&1
    ); then
      emit_context "autoquality failed for $rel_file:\n$out"
    fi
    exit 0
    ;;
esac

# Only fire Lean checks for the proof-spine files. Deliberately exclude the
# elaboration giants (AbstractMachine, EnvMachine, Frontend/TypeCheck): lanes
# there run `just check FILE` / lean-lsp deliberately, not per edit.
case "$rel_file" in
  Bang/Spec.lean|Bang/Core/IR.lean|Bang/Core/Typing.lean| \
  Bang/Core/Semantics.lean|Bang/Core/Semantics/*.lean| \
  Bang/Meta/LR.lean|Bang/Meta/BinaryLR.lean|Bang/Backend/Wasm.lean| \
  Bang/Core/Grade.lean|Bang/Core/EffectRow.lean| \
  Bang/Distribution.lean|Bang/Audit.lean)
    ;;
  *) exit 0 ;;
esac

set +e
if [ "${BANG_POST_EDIT_CHECK_NO_NIX:-0}" = "1" ]; then
  # Test seam: focused tests already run inside the dev shell and inject a
  # deterministic fake `lake` without recursively entering Nix.
  out=$(cd "$root" && bash tools/check.sh "$rel_file" 2>&1)
else
  out=$(cd "$root" && nix develop --command bash tools/check.sh "$rel_file" 2>&1)
fi
status=$?
set -e

if (( status != 0 )); then
  errs=$(grep -E '(^|: )(error|warning)(\([^)]*\))?:' <<<"$out" | head -10 || true)
  emit_context "Lean check failed for $rel_file (exit $status):\n${errs:-$out}"
fi

# PostToolUse feedback is intentionally advisory. The blocking status is
# preserved by tools/check.sh itself and by the pre-commit/full verification gates.
exit 0
