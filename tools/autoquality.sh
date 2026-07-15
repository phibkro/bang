#!/usr/bin/env bash
# tool: role=check couples=flake.nix,justfile,tools/autoquality-files.txt,tools/git-hooks/pre-commit,tools/hooks/post-edit-check.sh runs-in=fitness,hook
# Pinned formatter/linter entry point for maintained Python and shell tooling.

set -euo pipefail

ROOT=$(git rev-parse --show-toplevel)
cd "$ROOT"

python_files=()
shell_files=()
declare -A seen_python=()
declare -A seen_shell=()

if [[ ${1:-} == -- ]]; then
  shift
fi

classify() {
  local input=$1
  local path

  if [[ "$input" = /* ]]; then
    path=$(realpath -m -- "$input")
  else
    path=$(realpath -m -- "$ROOT/$input")
  fi
  case "$path" in
    "$ROOT"/*) path=${path#"$ROOT"/} ;;
    *)
      printf 'autoquality: path is outside repository: %s\n' "$input" >&2
      return 1
      ;;
  esac
  if [[ ! -f "$path" ]]; then
    printf 'autoquality: file does not exist: %s\n' "$path" >&2
    return 1
  fi

  case "$path" in
    *.py)
      if [[ -z ${seen_python[$path]+present} ]]; then
        python_files+=("$path")
        seen_python[$path]=1
      fi
      ;;
    *.sh)
      if [[ -z ${seen_shell[$path]+present} ]]; then
        shell_files+=("$path")
        seen_shell[$path]=1
      fi
      ;;
    *)
      IFS= read -r first_line < "$path" || true
      if [[ "$first_line" =~ ^#!.*(ba)?sh([[:space:]]|$) ]] \
        && [[ -z ${seen_shell[$path]+present} ]]; then
        shell_files+=("$path")
        seen_shell[$path]=1
      fi
      ;;
  esac
}

if (( $# )); then
  for path in "$@"; do
    classify "$path"
  done
else
  while IFS= read -r path; do
    [[ -n "$path" && "$path" != \#* ]] || continue
    if [[ ! -f "$path" ]]; then
      printf 'autoquality: baseline file is missing: %s\n' "$path" >&2
      exit 1
    fi
    classify "$path"
  done < tools/autoquality-files.txt

  while IFS= read -r path; do
    [[ -n "$path" && -f "$path" ]] && classify "$path"
  done < <(
    {
      git diff-tree --first-parent --no-commit-id --name-only --diff-filter=ACM -r HEAD
      git diff --name-only --diff-filter=ACM HEAD
      git ls-files --others --exclude-standard
    } | sort -u
  )
fi

mapfile -t all_python < <(git ls-files '*.py')
if (( ${#all_python[@]} )); then
  ruff check --select E9,F63,F7,F82 -- "${all_python[@]}"
fi
if (( ${#python_files[@]} )); then
  ruff format --check -- "${python_files[@]}"
  ruff check -- "${python_files[@]}"
fi
if (( ${#shell_files[@]} )); then
  shellcheck --severity=warning -- "${shell_files[@]}"
fi

printf 'autoquality: PASS — %d full Python · %d shell · %d Python critical file(s).\n' \
  "${#python_files[@]}" "${#shell_files[@]}" "${#all_python[@]}"
