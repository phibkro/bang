#!/usr/bin/env bash
# tool: role=test couples=autoquality.sh,tools/autoquality-files.txt,.github/workflows/verify.yml runs-in=fitness
# Falsification poles for complete product-range discovery in the pinned tooling gate.

set -euo pipefail

ROOT=$(git rev-parse --show-toplevel)
workdir=$(mktemp -d --tmpdir bang-autoquality-XXXXXX)
trap 'rm -rf "$workdir"' EXIT

passed=0
pass() {
  passed=$((passed + 1))
  printf '  ✓ %s\n' "$1"
}

make_fixture() {
  local name=$1
  local repo="$workdir/$name"
  mkdir -p "$repo/tools" "$repo/fake-bin"
  cp "$ROOT/tools/autoquality.sh" "$repo/tools/autoquality.sh"
  printf 'tools/autoquality.sh\n' > "$repo/tools/autoquality-files.txt"
  cat > "$repo/fake-bin/ruff" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
if [[ ${1:-} == format ]]; then
  for path in "$@"; do
    if [[ -f "$path" ]] && grep -Fq 'BAD_FORMAT' "$path"; then
      printf 'would reformat: %s\n' "$path" >&2
      exit 1
    fi
  done
fi
SH
  cat > "$repo/fake-bin/shellcheck" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
bad=0
for path in "$@"; do
  if [[ -f "$path" ]] && grep -Fq 'BAD_SHELL' "$path"; then
    if [[ -n ${FAKE_SHELLCHECK_LOG:-} ]]; then
      printf '%s\0' "$path" >> "$FAKE_SHELLCHECK_LOG"
    fi
    printf 'shell defect: %q\n' "$path" >&2
    bad=1
  fi
done
exit "$bad"
SH
  chmod +x "$repo/fake-bin/ruff" "$repo/fake-bin/shellcheck" \
    "$repo/tools/autoquality.sh"
  printf 'fake-bin/\n' > "$repo/.gitignore"
  git -C "$repo" init -q -b main
  git -C "$repo" config user.name 'Autoquality Test'
  git -C "$repo" config user.email 'autoquality@example.invalid'
  git -C "$repo" add .gitignore tools
  git -C "$repo" commit -qm 'chore: fixture baseline'
  printf '%s\n' "$repo"
}

expect_format_failure() {
  local name=$1 repo=$2 stable=$3 end=$4 needle=$5
  set +e
  (cd "$repo" && \
    PATH="$repo/fake-bin:$PATH" \
      PROVENANCE_STABLE_REF="$stable" PROVENANCE_END="$end" \
      bash tools/autoquality.sh) >"$workdir/stdout" 2>"$workdir/stderr"
  local status=$?
  set -e
  if [[ $status -eq 0 ]] || ! grep -Fq "$needle" "$workdir/stderr"; then
    printf 'FAIL: %s did not reject %s (status %s)\n' "$name" "$needle" "$status" >&2
    sed -n '1,120p' "$workdir/stdout" >&2
    sed -n '1,120p' "$workdir/stderr" >&2
    exit 1
  fi
  pass "$name"
}

expect_contract_failure() {
  local name=$1 repo=$2 stable=$3 end=$4 needle=$5
  set +e
  (cd "$repo" && \
    PATH="$repo/fake-bin:$PATH" \
      PROVENANCE_STABLE_REF="$stable" PROVENANCE_END="$end" \
      bash tools/autoquality.sh) >"$workdir/stdout" 2>"$workdir/stderr"
  local status=$?
  set -e
  if [[ $status -eq 0 ]] || ! grep -Fq "$needle" "$workdir/stderr"; then
    printf 'FAIL: %s did not fail closed (status %s)\n' "$name" "$status" >&2
    sed -n '1,120p' "$workdir/stderr" >&2
    exit 1
  fi
  pass "$name"
}

expect_git_producer_failure() {
  local name=$1 repo=$2 stable=$3 end=$4 mode=$5 expected_status=$6
  local real_git
  real_git=$(command -v git)
  mkdir -p "$repo/fail-bin"
  cat > "$repo/fail-bin/git" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
if [[ ${FAIL_GIT_PATH_PRODUCER:-} == diff && ${1:-} == diff \
      && ${2:-} == --name-only ]]; then
  exit 42
fi
if [[ ${FAIL_GIT_PATH_PRODUCER:-} == untracked && ${1:-} == ls-files ]]; then
  for arg in "$@"; do
    [[ "$arg" == --others ]] && exit 43
  done
fi
exec "${AUTOQUALITY_REAL_GIT:?}" "$@"
SH
  chmod +x "$repo/fail-bin/git"
  set +e
  (cd "$repo" && \
    PATH="$repo/fail-bin:$repo/fake-bin:$PATH" AUTOQUALITY_REAL_GIT="$real_git" \
      FAIL_GIT_PATH_PRODUCER="$mode" \
      PROVENANCE_STABLE_REF="$stable" PROVENANCE_END="$end" \
      bash tools/autoquality.sh) >"$workdir/stdout" 2>"$workdir/stderr"
  local status=$?
  set -e
  if [[ $status -eq 0 ]] \
    || ! grep -Fq "Git path producer exited $expected_status" "$workdir/stderr"; then
    printf 'FAIL: %s did not propagate producer status %s (got %s)\n' \
      "$name" "$expected_status" "$status" >&2
    sed -n '1,120p' "$workdir/stderr" >&2
    exit 1
  fi
  pass "$name"
}

expect_shell_paths_failure() {
  local name=$1 repo=$2 stable=$3 end=$4 log=$5
  shift 5
  local expected=("$@")
  local seen_paths=()
  declare -A seen=()
  rm -f "$log"
  set +e
  (cd "$repo" && \
    PATH="$repo/fake-bin:$PATH" FAKE_SHELLCHECK_LOG="$log" \
      PROVENANCE_STABLE_REF="$stable" PROVENANCE_END="$end" \
      bash tools/autoquality.sh) >"$workdir/stdout" 2>"$workdir/stderr"
  local status=$?
  set -e
  if [[ $status -eq 0 || ! -f "$log" ]]; then
    printf 'FAIL: %s did not reject the hostile shell path(s)\n' "$name" >&2
    sed -n '1,120p' "$workdir/stderr" >&2
    exit 1
  fi
  mapfile -d '' -t seen_paths < "$log"
  for path in "${seen_paths[@]}"; do
    seen["$path"]=1
  done
  if [[ ${#seen_paths[@]} -ne ${#expected[@]} ]]; then
    printf 'FAIL: %s checked %d hostile paths, expected %d\n' \
      "$name" "${#seen_paths[@]}" "${#expected[@]}" >&2
    exit 1
  fi
  for path in "${expected[@]}"; do
    if [[ -z ${seen[$path]+present} ]]; then
      printf 'FAIL: %s omitted path %q\n' "$name" "$path" >&2
      exit 1
    fi
  done
  pass "$name"
}

# The source commit carries the defect and HEAD is generated-only. This is the
# exact squash-PR shape that a HEAD-only discovery pass missed on main.
repo=$(make_fixture two-commit)
base=$(git -C "$repo" rev-parse HEAD)
git -C "$repo" switch -qc feature
printf '# BAD_FORMAT\n' > "$repo/source.py"
git -C "$repo" add source.py
git -C "$repo" commit -qm 'fix: product source'
printf 'generated\n' > "$repo/generated.txt"
git -C "$repo" add generated.txt
git -C "$repo" commit -qm 'chore: generated provenance'
mapfile -t old_head_paths < <(
  git -C "$repo" diff-tree --first-parent --no-commit-id --name-only \
    --diff-filter=ACM -r HEAD
)
set +e
(cd "$repo" && PATH="$repo/fake-bin:$PATH" \
  bash tools/autoquality.sh "${old_head_paths[@]}") \
  >"$workdir/stdout" 2>"$workdir/stderr"
old_status=$?
set -e
if [[ $old_status -ne 0 ]] || grep -Fq source.py "$workdir/stderr"; then
  printf 'FAIL: HEAD-only negative control unexpectedly found the source defect\n' >&2
  exit 1
fi
pass 'HEAD-only negative control misses the source-commit defect'
expect_format_failure 'two-commit range includes the source commit' \
  "$repo" "$base" HEAD source.py

# NUL transport is an end-to-end contract: Git must not quote or line-split a
# source-commit path before classify/shellcheck receives it. The newline case is
# the exact former bypass; the other names defend the same boundary broadly.
repo=$(make_fixture hostile-committed)
base=$(git -C "$repo" rev-parse HEAD)
git -C "$repo" switch -qc feature
hostile_committed=($'line\nbreak.sh' $'tab\tbreak.sh' 'back\slash.sh' 'føø.sh')
for path in "${hostile_committed[@]}"; do
  printf '# BAD_SHELL\n' > "$repo/$path"
done
git -C "$repo" add -- "${hostile_committed[@]}"
git -C "$repo" commit -qm 'fix: hostile shell paths'
printf 'generated\n' > "$repo/generated.txt"
git -C "$repo" add generated.txt
git -C "$repo" commit -qm 'chore: generated provenance'
expect_shell_paths_failure \
  'explicit two-commit range preserves newline, tab, backslash, and non-ASCII paths' \
  "$repo" "$base" HEAD "$workdir/committed-shell-paths" \
  "${hostile_committed[@]}"

# A checked NUL stream must propagate producer failure rather than treating it
# as an empty path set. Exercise both the committed range and untracked seam.
expect_git_producer_failure \
  'committed Git diff producer failure is fail-closed' \
  "$repo" "$base" HEAD diff 42
expect_git_producer_failure \
  'untracked Git ls-files producer failure is fail-closed' \
  "$repo" HEAD HEAD untracked 43

# A normal one-commit feature retains the same stable..end behavior.
repo=$(make_fixture single-commit)
base=$(git -C "$repo" rev-parse HEAD)
git -C "$repo" switch -qc feature
printf '# BAD_FORMAT\n' > "$repo/single.py"
git -C "$repo" add single.py
git -C "$repo" commit -qm 'fix: single product commit'
expect_format_failure 'single-commit feature includes its product file' \
  "$repo" "$base" HEAD single.py

# A local remote-tracking ref can advance on another line after the feature was
# cut. Local discovery uses the merge-base, not an endpoint-only fallback.
repo=$(make_fixture advanced-origin)
base=$(git -C "$repo" rev-parse HEAD)
git -C "$repo" switch -qc feature
printf '# BAD_FORMAT\n' > "$repo/advanced.py"
git -C "$repo" add advanced.py
git -C "$repo" commit -qm 'fix: feature source'
printf 'generated\n' > "$repo/generated.txt"
git -C "$repo" add generated.txt
git -C "$repo" commit -qm 'chore: generated provenance'
git -C "$repo" switch -q main
printf 'remote advance\n' > "$repo/remote.txt"
git -C "$repo" add remote.txt
git -C "$repo" commit -qm 'chore: advance main'
git -C "$repo" update-ref refs/remotes/origin/main HEAD
git -C "$repo" switch -q feature
set +e
(cd "$repo" && env -u PROVENANCE_STABLE_REF -u PROVENANCE_END \
  PATH="$repo/fake-bin:$PATH" bash tools/autoquality.sh) \
  >"$workdir/stdout" 2>"$workdir/stderr"
status=$?
set -e
if [[ $status -eq 0 ]] || ! grep -Fq advanced.py "$workdir/stderr"; then
  printf 'FAIL: advanced origin/main truncated the local product range\n' >&2
  exit 1
fi
pass 'advanced origin/main uses merge-base through both feature commits'

# The same divergent endpoints are invalid when CI declares them explicitly;
# silently weakening that contract would allow a partial gate.
expect_contract_failure 'nonlinear explicit provenance fails closed' \
  "$repo" refs/remotes/origin/main HEAD 'not an ancestor'
expect_contract_failure 'unresolvable explicit provenance fails closed' \
  "$repo" refs/remotes/origin/missing HEAD 'cannot resolve explicit stable endpoint'

# GitHub main-push provenance has stable == end. The endpoint commit must not
# collapse to an empty range.
repo=$(make_fixture main-push)
printf '# BAD_FORMAT\n' > "$repo/push.py"
git -C "$repo" add push.py
git -C "$repo" commit -qm 'fix: squash landing'
head=$(git -C "$repo" rev-parse HEAD)
expect_format_failure 'main push inspects the landed endpoint commit' \
  "$repo" "$head" "$head" push.py

# Dirty, untracked, and explicit hook invocations remain independent of the
# committed-range calculation.
repo=$(make_fixture working-tree)
base=$(git -C "$repo" rev-parse HEAD)
printf '# clean\n' > "$repo/dirty.py"
git -C "$repo" add dirty.py
git -C "$repo" commit -qm 'chore: tracked Python fixture'
printf '# BAD_FORMAT\n' > "$repo/dirty.py"
expect_format_failure 'dirty tracked file remains included' \
  "$repo" "$base" HEAD dirty.py
git -C "$repo" restore dirty.py
printf '# BAD_FORMAT\n' > "$repo/untracked.py"
expect_format_failure 'untracked file remains included' \
  "$repo" "$base" HEAD untracked.py
rm "$repo/untracked.py"
printf '# BAD_FORMAT\n' > "$repo/explicit.py"
set +e
(cd "$repo" && PATH="$repo/fake-bin:$PATH" bash tools/autoquality.sh explicit.py) \
  >"$workdir/stdout" 2>"$workdir/stderr"
status=$?
set -e
if [[ $status -eq 0 ]] || ! grep -Fq explicit.py "$workdir/stderr"; then
  printf 'FAIL: explicit hook path was not checked (status %s)\n' "$status" >&2
  exit 1
fi
pass 'explicit hook path remains included'

# Dirty and untracked discovery use the same NUL-safe transport as the committed
# range; neither path class may regress to line-oriented parsing.
repo=$(make_fixture hostile-working-tree)
base=$(git -C "$repo" rev-parse HEAD)
hostile_dirty=$'dirty\tback\\slash.sh'
hostile_untracked='untracked-føø.sh'
printf '# clean\n' > "$repo/$hostile_dirty"
git -C "$repo" add -- "$hostile_dirty"
git -C "$repo" commit -qm 'chore: hostile tracked fixture'
printf '# BAD_SHELL\n' > "$repo/$hostile_dirty"
printf '# BAD_SHELL\n' > "$repo/$hostile_untracked"
expect_shell_paths_failure \
  'dirty and untracked discovery preserve hostile paths' \
  "$repo" "$base" HEAD "$workdir/working-shell-paths" \
  "$hostile_dirty" "$hostile_untracked"

printf 'PASS: %d/%d autoquality range poles.\n' "$passed" 14
