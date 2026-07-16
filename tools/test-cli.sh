#!/usr/bin/env bash
# tool: role=test couples=none runs-in=verify
source "$(git rev-parse --show-toplevel 2>/dev/null)/tools/tool-log.sh" 2>/dev/null && tool_log "$(basename "$0")" || true
# test-cli.sh — the non-interactive gate for `bang`'s TOP-LEVEL CLI hygiene (issue #66/#67).
#
# Two concerns, both CLI-surface (not covered by test-repl.sh/test-fmt.sh/test-check-json.sh,
# which each gate one subcommand's own behavior): (1) `--help`/`--version` — a help/version
# REQUEST is a success (issue #66's --help-exits-1 fix), not folded into any one subcommand's
# usage path; (2) every non-zero RUNTIME outcome (oom/escapedCap/stuck/compiled-collapse) gets
# a human-readable stderr message ALONGSIDE its exit code (issue #67) — the exit code stays the
# machine contract, the message is the "the error teaches" half.
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"
bang=".lake/build/bin/bang"

if [ -z "${BANG_BIN_FRESH:-}" ]; then
  echo "building bang runner…" >&2
  lake build bang >&2
fi

pass=0
fail=0

check() {
  local name="$1" got="$2" want="$3"
  if [ "$got" = "$want" ]; then
    echo "✓ $name"; pass=$((pass + 1))
  else
    echo "✗ $name — expected [$want], got [$got]"; fail=$((fail + 1))
  fi
}

contains() {
  local name="$1" haystack="$2" needle="$3"
  if [[ "$haystack" == *"$needle"* ]]; then
    echo "✓ $name"; pass=$((pass + 1))
  else
    echo "✗ $name — expected to find [$needle] in [$haystack]"; fail=$((fail + 1))
  fi
}

# ── --help / -h : a help request is a SUCCESS (issue #66), text on STDOUT ──
help_out="$("$bang" --help 2>/dev/null)" && help_exit=0 || help_exit=$?
check "help-long-exit" "$help_exit" "0"
contains "help-long-stdout-usage" "$help_out" "USAGE:"
help_stderr="$("$bang" --help 2>&1 >/dev/null)" && help_stderr_exit=0 || help_stderr_exit=$?
check "help-long-stderr-invocation-exit" "$help_stderr_exit" "0"
check "help-long-stderr-empty" "$help_stderr" ""

got_h_exit=0
"$bang" -h >/dev/null 2>&1 || got_h_exit=$?
check "help-short-exit" "$got_h_exit" "0"

# ── --version / -v : prints a version, exit 0 ──
ver_out="$("$bang" --version 2>/dev/null)" && ver_exit=0 || ver_exit=$?
check "version-long-exit" "$ver_exit" "0"
contains "version-long-stdout-has-bang" "$ver_out" "bang "
got_v_out="$("$bang" -v 2>/dev/null)" && got_v_exit=0 || got_v_exit=$?
check "version-short-exit" "$got_v_exit" "0"
check "version-long-and-short-agree" "$got_v_out" "$ver_out"

# ── RUNTIME MESSAGES (issue #67): each non-zero outcome names the outcome + a next step ──
# oom (exit 2) — a genuinely-diverging `Div` recursion exhausts the fuel ceiling.
oom_tmp="$(mktemp /tmp/bang-cli-test-oom-XXXXXX.bang)"
printf 'let rec loop : Int -> Int ! {Div} = fun n => $loop (n + 1) in $loop 0' > "$oom_tmp"
# post-flip (v0.1.0): the sub-classified diagnosis is the ORACLE's contract — pin it there.
oom_stderr="$("$bang" run --engine=oracle "$oom_tmp" 2>&1 >/dev/null)" && oom_exit=0 || oom_exit=$?
rm -f "$oom_tmp"
check "oom-exit" "$oom_exit" "2"
contains "oom-message-names-outcome" "$oom_stderr" "out of fuel"
contains "oom-message-names-issue" "$oom_stderr" "#61"

# escapedCap (exit 3) — a `{get}` thunk forced after its `state` handler already returned.
esc_stderr="$("$bang" eval --engine=oracle --no-typecheck 'let c = (state 0 in {get}) in $c' 2>&1 >/dev/null)" && esc_exit=0 || esc_exit=$?
check "escaped-exit" "$esc_exit" "3"
contains "escaped-message-names-outcome" "$esc_stderr" "escaped its handler"
contains "escaped-message-names-adr" "$esc_stderr" "ADR-0063"

# stuck (exit 4, --no-typecheck only) — forcing a non-thunk value.
stuck_stderr="$("$bang" eval --engine=oracle --no-typecheck '$3' 2>&1 >/dev/null)" && stuck_exit=0 || stuck_exit=$?
check "stuck-exit" "$stuck_exit" "4"

# DEFAULT-ENGINE collapse contract (v0.1.0 flip, ADR-0094 A1): a failing program on the
# default env engine exits 5 with a message that ROUTES to the oracle for diagnosis.
defc_stderr="$("$bang" eval --no-typecheck '$3' 2>&1 >/dev/null)" && defc_exit=0 || defc_exit=$?
check "default-collapse-exit" "$defc_exit" "5"
contains "default-collapse-routes-to-oracle" "$defc_stderr" "engine=oracle"
contains "stuck-message-names-typecheck-flag" "$stuck_stderr" "--no-typecheck"

# compiled collapse (exit 5) — the SAME escape program, run on the calculated machine, which
# cannot sub-classify WHICH terminal it hit.
compiled_stderr="$("$bang" eval --no-typecheck --compiled 'let c = (state 0 in {get}) in $c' 2>&1 >/dev/null)" && compiled_exit=0 || compiled_exit=$?
check "compiled-collapse-exit" "$compiled_exit" "5"
contains "compiled-collapse-message-says-which" "$compiled_stderr" "does not sub-classify"

# ── `bang new` write boundary (#179): NAME is one safe segment and the PHYSICAL examples/
# parent stays under the current working root. Every fixture lives outside the repository; the
# runner must neither escape nor overwrite a directory entry (including dangling symlinks).
new_tmp="$(mktemp -d --tmpdir bang-cli-new-XXXXXX)"
trap 'rm -rf "$new_tmp"' EXIT
new_root="$new_tmp/project"
mkdir -p "$new_root/examples"
absbang="$(realpath "$bang")"

reject_new_name() {
  local case_name="$1" project_name="$2"
  local stderr exit_code=0
  stderr="$(cd "$new_root" && "$absbang" new "$project_name" 2>&1 >/dev/null)" || exit_code=$?
  check "new-reject-$case_name-exit" "$exit_code" "1"
  contains "new-reject-$case_name-diagnostic" "$stderr" "invalid project name '$project_name'"
}

reject_new_name "parent" "../escape"
check "new-reject-parent-no-escape" "$(test ! -e "$new_root/escape" && echo yes)" "yes"

absolute_escape="$new_tmp/absolute-escape"
reject_new_name "absolute" "$absolute_escape"
check "new-reject-absolute-no-escape" "$(test ! -e "$absolute_escape" && echo yes)" "yes"

reject_new_name "slash" "nested/name"
check "new-reject-slash-no-components" "$(test ! -e "$new_root/examples/nested" && echo yes)" "yes"
reject_new_name "backslash" 'nested\name'
reject_new_name "dot" "."
reject_new_name "dotdot" ".."
reject_new_name "hidden" ".hidden"
reject_new_name "whitespace" "two words"
empty_stderr="$(cd "$new_root" && "$absbang" new 2>&1 >/dev/null)" && empty_exit=0 || empty_exit=$?
check "new-reject-empty-exit" "$empty_exit" "1"
contains "new-reject-empty-diagnostic" "$empty_stderr" "invalid project name ''"
unknown_stderr="$(cd "$new_root" && "$absbang" new unknown-flag-name --bogus 2>&1 >/dev/null)" && unknown_exit=0 || unknown_exit=$?
check "new-unknown-flag-exit" "$unknown_exit" "1"
contains "new-unknown-flag-usage" "$unknown_stderr" "USAGE:"
check "new-unknown-flag-no-write" "$(test ! -e "$new_root/examples/unknown-flag-name" && echo yes)" "yes"

# Existing directories are rejected and their contents prove the failure path never authorizes
# rollback of a path this invocation did not create.
mkdir "$new_root/examples/existing"
printf 'keep-existing\n' > "$new_root/examples/existing/sentinel"
existing_stderr="$(cd "$new_root" && "$absbang" new existing 2>&1 >/dev/null)" && existing_exit=0 || existing_exit=$?
check "new-existing-exit" "$existing_exit" "1"
contains "new-existing-diagnostic" "$existing_stderr" "already exists"
check "new-existing-preserved" "$(cat "$new_root/examples/existing/sentinel")" "keep-existing"

# A failure of the atomic create itself returns directly: because ownership starts only after a
# successful createDir, this branch has no rollback authority.
no_create_root="$new_tmp/no-create-project"
mkdir -p "$no_create_root/examples"
chmod 0555 "$no_create_root/examples"
create_stderr="$(cd "$no_create_root" && "$absbang" new cannot-create 2>&1 >/dev/null)" && create_exit=0 || create_exit=$?
chmod 0755 "$no_create_root/examples"
check "new-create-failure-exit" "$create_exit" "1"
contains "new-create-failure-diagnostic" "$create_stderr" "could not create scaffold directory"
check "new-create-failure-no-target" "$(test ! -e "$no_create_root/examples/cannot-create" && echo yes)" "yes"

# readDir sees directory entries without following them, so both live and dangling target symlinks
# are no-overwrite failures. The outside sentinel also proves no traversal/cleanup occurred.
mkdir "$new_tmp/outside-target"
printf 'keep-symlink-target\n' > "$new_tmp/outside-target/sentinel"
ln -s "$new_tmp/outside-target" "$new_root/examples/linked"
linked_stderr="$(cd "$new_root" && "$absbang" new linked 2>&1 >/dev/null)" && linked_exit=0 || linked_exit=$?
check "new-symlink-target-exit" "$linked_exit" "1"
contains "new-symlink-target-diagnostic" "$linked_stderr" "already exists"
check "new-symlink-target-preserved" "$(cat "$new_tmp/outside-target/sentinel")" "keep-symlink-target"
ln -s "$new_tmp/missing-target" "$new_root/examples/dangling"
dangling_stderr="$(cd "$new_root" && "$absbang" new dangling 2>&1 >/dev/null)" && dangling_exit=0 || dangling_exit=$?
check "new-dangling-target-exit" "$dangling_exit" "1"
contains "new-dangling-target-diagnostic" "$dangling_stderr" "already exists"
check "new-dangling-target-preserved" "$(test -L "$new_root/examples/dangling" && echo yes)" "yes"

# A safe NAME is still refused when the examples/ PARENT resolves outside the working root.
symlink_root="$new_tmp/symlink-project"
outside_examples="$new_tmp/outside-examples"
mkdir "$symlink_root" "$outside_examples"
ln -s "$outside_examples" "$symlink_root/examples"
parent_stderr="$(cd "$symlink_root" && "$absbang" new safe-name 2>&1 >/dev/null)" && parent_exit=0 || parent_exit=$?
check "new-symlink-parent-exit" "$parent_exit" "1"
contains "new-symlink-parent-diagnostic" "$parent_stderr" "symlinked examples/ parent is not allowed"
check "new-symlink-parent-no-escape" "$(test ! -e "$outside_examples/safe-name" && echo yes)" "yes"

# Happy path: all generated files exist and the oracle is exactly what the runner prints.
valid_out="$(cd "$new_root" && "$absbang" new safe-name 2>/dev/null)" && valid_exit=0 || valid_exit=$?
check "new-valid-exit" "$valid_exit" "0"
contains "new-valid-created" "$valid_out" "created examples/safe-name/"
check "new-valid-files" \
  "$(test -f "$new_root/examples/safe-name/main.bang" && \
     test -f "$new_root/examples/safe-name/README.md" && \
     test -f "$new_root/examples/safe-name/expected.txt" && echo yes)" "yes"
valid_actual="$(cd "$new_root" && "$absbang" run examples/safe-name/main.bang)"
check "new-valid-oracle" "$valid_actual" "$(cat "$new_root/examples/safe-name/expected.txt")"

# Induce a post-create write failure without a product-only test seam: umask 0222 makes the newly
# created directory read/execute-only, so its first file creation fails. Rollback can still enumerate
# the empty directory and remove it through the writable parent.
cleanup_stderr="$(cd "$new_root" && umask 0222 && "$absbang" new cleanup-case 2>&1 >/dev/null)" && cleanup_exit=0 || cleanup_exit=$?
check "new-failure-exit" "$cleanup_exit" "1"
contains "new-failure-diagnostic" "$cleanup_stderr" "removed the incomplete scaffold"
check "new-failure-cleaned" "$(test ! -e "$new_root/examples/cleanup-case" && echo yes)" "yes"

echo "──────────────────────────────"
echo "cli: $pass passed, $fail failed"
[ "$fail" -eq 0 ]
