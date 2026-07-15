#!/usr/bin/env bash
# tool: role=check couples=setup.sh runs-in=fitness
# Read-only readiness probe for the 15-minute contributor journey.
set -euo pipefail

repo="."
json=0
while [ "$#" -gt 0 ]; do
  case "$1" in
    --json)
      json=1
      shift
      ;;
    --repo)
      repo="${2:?--repo requires a path}"
      shift 2
      ;;
    *)
      printf 'onboarding-preflight: unknown argument: %s\n' "$1" >&2
      exit 2
      ;;
  esac
done

fail_error() {
  local message="$1"
  if [ "$json" -eq 1 ]; then
    printf '{"state":"error","ready":false,"missing":[],"message":"%s"}\n' "$message"
  else
    printf 'onboarding-preflight: %s\n' "$message" >&2
  fi
  exit 2
}

repo="$(cd "$repo" 2>/dev/null && pwd -P)" || fail_error 'repository path is not readable'

git_bin="${BANG_PREFLIGHT_GIT:-git}"
nix_bin="${BANG_PREFLIGHT_NIX:-nix}"
runner="$repo/.lake/build/bin/bang"
cache="$repo/.lake/packages/mathlib/.lake/build"

missing=()
if ! command -v "$git_bin" >/dev/null 2>&1 || ! "$git_bin" -C "$repo" rev-parse --git-dir >/dev/null 2>&1; then
  fail_error 'path is not a Git checkout'
fi

git_dir="$("$git_bin" -C "$repo" rev-parse --absolute-git-dir)"
common_dir="$("$git_bin" -C "$repo" rev-parse --path-format=absolute --git-common-dir)"
linked_worktree=false
[ "$git_dir" = "$common_dir" ] || linked_worktree=true

nix_present=false
if command -v "$nix_bin" >/dev/null 2>&1; then
  nix_present=true
else
  missing+=("nix")
fi
in_dev_shell=false
if [ -n "${IN_NIX_SHELL:-}" ]; then
  in_dev_shell=true
else
  missing+=("dev shell")
fi
cache_present=false
if [ -e "$cache" ]; then
  cache_present=true
else
  missing+=("Mathlib cache")
fi
runner_present=false
if [ -x "$runner" ] && "$runner" --version >/dev/null 2>&1; then
  runner_present=true
else
  missing+=("bang runner")
fi
auto="$("$git_bin" -C "$repo" config --get gc.auto 2>/dev/null || true)"
detach="$("$git_bin" -C "$repo" config --get gc.autoDetach 2>/dev/null || true)"
git_hygiene=true
if [ "$auto" != "0" ]; then
  missing+=("gc.auto=0")
  git_hygiene=false
fi
if [ "$detach" != "false" ]; then
  missing+=("gc.autoDetach=false")
  git_hygiene=false
fi

render_missing_json() {
  local first=1 item
  printf '['
  for item in "${missing[@]}"; do
    [ "$first" -eq 1 ] || printf ','
    printf '"%s"' "$item"
    first=0
  done
  printf ']'
}

if [ "${#missing[@]}" -gt 0 ]; then
  if [ "$json" -eq 1 ]; then
    printf '{"state":"cold-not-ready","ready":false,"missing":'
    render_missing_json
    printf ',"linkedWorktree":%s,"nixPresent":%s,"inDevShell":%s,"cachePresent":%s,"runnerPresent":%s,"gitHygiene":%s,"next":"nix develop, then just setup serially"}\n' \
      "$linked_worktree" "$nix_present" "$in_dev_shell" "$cache_present" "$runner_present" "$git_hygiene"
  else
    printf 'COLD / NOT READY\n'
    printf '  missing: %s\n' "$(IFS=', '; printf '%s' "${missing[*]}")"
    printf '  next: enter `nix develop`, then run `just setup` serially\n'
    printf '  do not start parallel first-time Lake jobs in this checkout\n'
  fi
  exit 1
fi

if [ "$json" -eq 1 ]; then
  printf '{"state":"ready","ready":true,"missing":[],"linkedWorktree":%s,"nixPresent":%s,"inDevShell":%s,"cachePresent":%s,"runnerPresent":%s,"gitHygiene":%s}\n' \
    "$linked_worktree" "$nix_present" "$in_dev_shell" "$cache_present" "$runner_present" "$git_hygiene"
else
  printf 'READY\n'
  printf '  checkout: %s\n' "$([ "$linked_worktree" = true ] && printf 'linked worktree' || printf 'standalone clone')"
  printf '  dev shell: active\n'
  printf '  Mathlib cache: present\n'
  printf '  bang runner: runnable\n'
  printf '  Git hygiene: configured\n'
fi
