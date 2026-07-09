#!/usr/bin/env bash
# tool: role=check couples=new-worktree.sh runs-in=hook
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

# `lake exe cache get` while ANY linked worktree exists → deny (#40, HARDENED 2026-07-08).
# The old test (git-dir != git-common-dir on the HOOK's cwd) was EVADED twice in one
# incident: the hook executes in the project dir, not where the command's `cd` / the
# shell's persistent cwd points, so `cd <wt> && …` and `nix develop -c bash -c '… cache
# get …'` both sailed through (memory shared-worktree-git-autogc-corruption, the
# 2026-07-08 retros). The robust narrow rule the incident history supports: with live
# linked worktrees, EVERY cache-get in this repo has ended in a wedged mathlib — deny
# them all; with zero worktrees (plain first-time setup) it stays allowed. The regex is
# substring on purpose — nested shells included; quoted-mention false-positives are
# accepted for this one (the incident cost dwarfs the rare re-phrase).
if printf '%s' "$cmd" | grep -qE 'lake +exe +cache +get'; then
  root="${CLAUDE_PROJECT_DIR:-.}"
  wt_count="$(git -C "$root" worktree list --porcelain 2>/dev/null | grep -c '^worktree ' || true)"
  if [ "${wt_count:-0}" -gt 1 ]; then
    jq -n --arg r "lake exe cache get while linked worktrees exist wedges mathlib (#40; guard-evasion incident 2026-07-08). Seeded worktrees already have oleans — just 'lake build'. If oleans are genuinely missing: 'lake exe cache unpack', or remove the idle worktrees first." \
      '{hookSpecificOutput:{hookEventName:"PreToolUse",permissionDecision:"deny",permissionDecisionReason:$r}}' 2>/dev/null
    exit 0
  fi
fi

# Bare `git worktree add` → an UNSEEDED worktree, the #40b corruption vector (bit again
# 2026-07-05: a bare-created IC worktree resurfaced the phantom-cache-tree wedge; memory
# shared-worktree-git-autogc-corruption). The match is COMMAND-POSITION anchored (start,
# or after && ; |) so a quoted mention inside an echo/commit message doesn't trip it —
# same narrowness rationale as above. tools/new-worktree.sh invokes it internally via
# its own script name, which this string-match never sees.
if printf '%s' "$cmd" | grep -qE '(^|&&|;|\|)[[:space:]]*git +worktree +add'; then
  jq -n --arg r "bare 'git worktree add' creates an UNSEEDED worktree — the #40b corruption vector (recurred 2026-07-05). Use: tools/new-worktree.sh <dir> <branch> [base] — it seeds .lake from the main checkout and pins gc.auto=0." \
    '{hookSpecificOutput:{hookEventName:"PreToolUse",permissionDecision:"deny",permissionDecisionReason:$r}}' 2>/dev/null
  exit 0
fi

exit 0
