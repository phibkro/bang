#!/usr/bin/env bash
# tool: role=check couples=flake.nix,justfile,tools/autoquality-files.txt,tools/git-hooks/pre-commit,tools/hooks/post-edit-check.sh runs-in=fitness,hook
# Pinned formatter/linter entry point for maintained Python and shell tooling.

set -euo pipefail

ROOT=$(git rev-parse --show-toplevel)
cd "$ROOT"

python_files=()
shell_files=()
committed_files=()
dirty_files=()
untracked_files=()
all_python=()
declare -A seen_python=()
declare -A seen_shell=()
path_transport_tmp=""

cleanup_path_transport() {
  if [[ -n "$path_transport_tmp" ]]; then
    rm -f -- "$path_transport_tmp"
    path_transport_tmp=""
  fi
}
trap cleanup_path_transport EXIT

# Process substitution reports `mapfile`'s status, not the producer's. Capture
# each NUL stream in the parent shell, require Git success, and only then parse
# it. This keeps hostile names lossless without turning a producer failure into
# an empty-list false green.
git_paths_into() {
  local destination_name=$1
  shift
  local -n destination=$destination_name
  local status

  destination=()
  path_transport_tmp=$(mktemp --tmpdir bang-autoquality-paths-XXXXXX)
  if git "$@" > "$path_transport_tmp"; then
    # The nameref writes the caller-owned array; ShellCheck cannot see that use.
    # shellcheck disable=SC2034
    mapfile -d '' -t destination < "$path_transport_tmp"
    cleanup_path_transport
    return 0
  else
    status=$?
  fi
  printf 'autoquality: FAIL — Git path producer exited %d: git' "$status" >&2
  printf ' %q' "$@" >&2
  printf '\n' >&2
  cleanup_path_transport
  return "$status"
}

# Resolve the complete virtual-product range with the same endpoint contract as
# tools/provenance.py: CI supplies immutable base/head identities through
# PROVENANCE_STABLE_REF + PROVENANCE_END; those explicit facts fail closed if
# incomplete or inconsistent. A local feature branch uses the merge-base with
# origin/main (then main), so a remote advance cannot truncate the product range.
# A main push has stable == end, so its endpoint commit is still inspected. Only
# when no usable local stable history exists do we retain the historical,
# deliberately incomplete endpoint-only fallback, with a loud warning.
committed_product_paths() {
  local explicit_contract=0
  local end_ref=HEAD
  local end_sha=""
  local stable_ref=""
  local stable_sha=""
  local range_base=""

  if [[ -n ${PROVENANCE_STABLE_REF+x} || -n ${PROVENANCE_END+x} ]]; then
    explicit_contract=1
    if [[ -z ${PROVENANCE_STABLE_REF:-} || -z ${PROVENANCE_END:-} ]]; then
      printf 'autoquality: FAIL — explicit provenance requires both PROVENANCE_STABLE_REF and PROVENANCE_END.\n' >&2
      return 1
    fi
    stable_ref=$PROVENANCE_STABLE_REF
    end_ref=$PROVENANCE_END
  fi

  if ! end_sha=$(git rev-parse --verify "${end_ref}^{commit}" 2>/dev/null); then
    if (( explicit_contract )); then
      printf 'autoquality: FAIL — cannot resolve explicit product endpoint %s.\n' "$end_ref" >&2
      return 1
    fi
    printf 'autoquality: product endpoint HEAD is unavailable.\n' >&2
    return 1
  fi

  if (( ! explicit_contract )); then
    for candidate in refs/remotes/origin/main main; do
      if git rev-parse --verify "${candidate}^{commit}" >/dev/null 2>&1; then
        stable_ref=$candidate
        break
      fi
    done
  fi

  if [[ -n "$stable_ref" ]]; then
    stable_sha=$(git rev-parse --verify "${stable_ref}^{commit}" 2>/dev/null || true)
  fi

  if (( explicit_contract )); then
    if [[ -z "$stable_sha" ]]; then
      printf 'autoquality: FAIL — cannot resolve explicit stable endpoint %s.\n' "$stable_ref" >&2
      return 1
    fi
    if [[ "$stable_sha" != "$end_sha" ]] \
      && ! git merge-base --is-ancestor "$stable_sha" "$end_sha"; then
      printf 'autoquality: FAIL — explicit stable endpoint is not an ancestor of product endpoint.\n' >&2
      return 1
    fi
    if [[ "$stable_sha" != "$end_sha" ]]; then
      git_paths_into committed_files diff --name-only -z --diff-filter=ACM \
        "$stable_sha" "$end_sha"
      return
    fi
  elif [[ -n "$stable_sha" ]]; then
    range_base=$(git merge-base "$stable_sha" "$end_sha" 2>/dev/null || true)
    if [[ -n "$range_base" && "$range_base" != "$end_sha" ]]; then
      git_paths_into committed_files diff --name-only -z --diff-filter=ACM \
        "$range_base" "$end_sha"
      return
    fi
    if [[ -z "$range_base" ]]; then
      printf 'autoquality: local stable history has no merge-base; checking endpoint commit only.\n' >&2
    fi
  else
    printf 'autoquality: local stable endpoint is unavailable; checking endpoint commit only.\n' >&2
  fi

  git_paths_into committed_files diff-tree --root --first-parent \
    --no-commit-id --name-only -z --diff-filter=ACM -r "$end_sha"
}

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
  if ! committed_product_paths; then
    exit 1
  fi

  while IFS= read -r path; do
    [[ -n "$path" && "$path" != \#* ]] || continue
    if [[ ! -f "$path" ]]; then
      printf 'autoquality: baseline file is missing: %s\n' "$path" >&2
      exit 1
    fi
    classify "$path"
  done < tools/autoquality-files.txt

  for path in "${committed_files[@]}"; do
    [[ -n "$path" && -f "$path" ]] && classify "$path"
  done
  if ! git_paths_into dirty_files diff --name-only -z --diff-filter=ACM HEAD; then
    exit 1
  fi
  for path in "${dirty_files[@]}"; do
    [[ -n "$path" && -f "$path" ]] && classify "$path"
  done
  if ! git_paths_into untracked_files ls-files -z --others --exclude-standard; then
    exit 1
  fi
  for path in "${untracked_files[@]}"; do
    [[ -n "$path" && -f "$path" ]] && classify "$path"
  done
fi

if ! git_paths_into all_python ls-files -z '*.py'; then
  exit 1
fi
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
