# tool: role=workflow couples=tools/*.sh,tools/*.py,justfile runs-in=manual
# tool-log.sh — the single home for invocation telemetry (plan 012 slice 1).
#
# Appends one `<ISO-8601-UTC> <name>` line to a repo-local, gitignored log so the
# tools-index can render a "last invoked" column and the operator can run a
# data-driven deprecation sweep. This is the SINGLE SOURCE OF TRUTH for the log
# PATH and LINE FORMAT — bash scripts source-and-call `tool_log`, python entry
# points shell out to `tools/tool-log.sh <name>`, and gen-tools-index.py parses
# the same file. Nobody hardcodes the path twice.
#
# MUST be failure-proof: a read-only checkout, a missing .claude/, or a full disk
# must NOT break the calling tool. Every step is guarded; the function always
# returns 0. It writes NOTHING outside the repo.
#
# Bash usage (one line after the `# tool:` header):
#   source "$(git rev-parse --show-toplevel)/tools/tool-log.sh" 2>/dev/null && tool_log "$(basename "$0")" || true
# CLI usage (python shells out):
#   bash tools/tool-log.sh gen-foo.py

tool_log() {
  # $1 = script basename (already stripped of any path)
  local name="${1:-unknown}"
  local root ts
  root="$(git rev-parse --show-toplevel 2>/dev/null)" || return 0
  [ -n "$root" ] || return 0
  [ -d "$root/.claude" ] || return 0
  ts="$(date -u +%Y-%m-%dT%H:%M:%SZ 2>/dev/null)" || return 0
  printf '%s %s\n' "$ts" "$name" >> "$root/.claude/tool-invocations.log" 2>/dev/null || true
  return 0
}

# When executed (not sourced), log the basename passed as $1 — this is the path
# the python entry points take. `${BASH_SOURCE[0]}` == `$0` only on direct exec.
if [ "${BASH_SOURCE[0]:-}" = "${0}" ]; then
  tool_log "${1:-unknown}" || true
fi
