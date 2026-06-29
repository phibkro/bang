#!/usr/bin/env bash
# PreToolUse(Bash) guard — blocks the ONE unambiguous, structurally-detectable footgun
# that clobbered worktrees in multi-agent proof sessions: `lake exe cache get` run from
# inside a linked git worktree (it re-clones Mathlib and clobbers the checkout — #40).
#
# Deliberately NARROW. The grep-trap discipline (`grep "error:"` misses
# error(lean.unknownIdentifier):; `grep sorry` is unreliable) is HEURISTIC — a hook can
# only string-match the command, which false-positives when the pattern is quoted inside
# an echo / heredoc / commit message (it blocked its own introducing commit in testing).
# So that stays as CLAUDE.md "Gate-traps" guidance + the /gate skill, NOT a hard block.
#
# Input: PreToolUse JSON on stdin (.tool_input.command). Output: a deny decision JSON on a
# match (exit 0), else silent allow (exit 0). Never hard-errors the tool pipeline.
set -uo pipefail

input="$(cat 2>/dev/null || true)"
cmd="$(printf '%s' "$input" | jq -r '.tool_input.command // empty' 2>/dev/null || true)"
[ -z "$cmd" ] && exit 0

# `lake exe cache get` while CWD is a LINKED worktree → clobbers (#40). The worktree test
# is STRUCTURAL (git-dir != git-common-dir) — not a path-string match — so it can't
# false-positive on a quoted path inside a message. The `cd <worktree> && …` form from a
# main-tree session is left to guidance (rare; cwd here is the main checkout).
if printf '%s' "$cmd" | grep -qE 'lake +exe +cache +get'; then
  gd="$(git rev-parse --git-dir 2>/dev/null || true)"
  gcd="$(git rev-parse --git-common-dir 2>/dev/null || true)"
  if [ -n "$gd" ] && [ "$gd" != "$gcd" ]; then
    jq -n --arg r "lake exe cache get from inside a linked worktree re-clones Mathlib and clobbers the checkout (#40). Use 'lake exe cache unpack' if oleans are missing, or build on the main checkout." \
      '{hookSpecificOutput:{hookEventName:"PreToolUse",permissionDecision:"deny",permissionDecisionReason:$r}}' 2>/dev/null
    exit 0
  fi
fi

exit 0
