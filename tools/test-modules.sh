#!/usr/bin/env bash
# tool: role=test couples=Main.lean,Bang/Frontend/TypeCheck.lean runs-in=verify
source "$(git rev-parse --show-toplevel 2>/dev/null)/tools/tool-log.sh" 2>/dev/null && tool_log "$(basename "$0")" || true
# test-modules.sh — the non-interactive gate for ADR-0093 (file-modules, `import`/`use`/`pub`).
#
# Mirrors test-fmt.sh's shape (build once, exercise the binary, diff, tally pass/fail). The
# module-merge CORE's laws (the differential elaborate(import-merged) ≡ elaborate(hand-qualified)
# oracle, Bang/Frontend/TypeCheck.lean's `mergeModules` #guards) are already gated at the Lean
# level — this file gates the CLI SURFACE specifically: real multi-FILE resolution (`Main.lean`'s
# `resolveEntryFile`, which reads other files off disk — not #guard-testable at all, since #guard
# runs at compile time with no filesystem), exit codes, and error-message content.
#
# PIPEFAIL GOTCHA (guarded throughout, per the team-lead's explicit warning): every fallible
# command that feeds a `$(...)` capture is followed by `&& code=0 || code=$?` (never a bare
# pipeline under `set -o pipefail` with no guard) — a guard-free failing command under `set -e`
# would abort the WHOLE script at the first nonzero exit, silently skipping every check after it.
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"
bang=".lake/build/bin/bang"

if [ -z "${BANG_BIN_FRESH:-}" ]; then
  echo "building bang runner…" >&2
  lake build bang >&2
fi

pass=0
fail=0

# `check NAME GOT WANT` — generic string-equality tally (mirrors test-fmt.sh's helper).
check() {
  local name="$1" got="$2" want="$3"
  if [ "$got" = "$want" ]; then
    echo "✓ $name"; pass=$((pass + 1))
  else
    echo "✗ $name — expected [$want], got [$got]"; fail=$((fail + 1))
  fi
}

# `check_contains NAME HAYSTACK NEEDLE` — substring assertion (for error-message content checks,
# where the exact message text is secondary to the message NAMING the right things).
check_contains() {
  local name="$1" haystack="$2" needle="$3"
  if [[ "$haystack" == *"$needle"* ]]; then
    echo "✓ $name"; pass=$((pass + 1))
  else
    echo "✗ $name — expected to find [$needle] in [$haystack]"; fail=$((fail + 1))
  fi
}

fixdir="$(mktemp -d --tmpdir bang-modules-test-XXXXXX)"
trap 'rm -rf "$fixdir"' EXIT

# ── happy path: a real 2-file program (bare `import` + qualified ctor call + match) ──
cat > "$fixdir/geom.bang" <<'BANG'
pub data Pair = Mk(Int, Int)
BANG
cat > "$fixdir/happy_import.bang" <<'BANG'
import geom
let p = geom.Mk(3, 4) in
match (p : geom_Pair) { geom_Mk(a, b) -> a + b }
BANG
got_out="$("$bang" run "$fixdir/happy_import.bang" 2>/dev/null)" && got_exit=0 || got_exit=$?
check "happy-import-stdout" "$got_out" "7"
check "happy-import-exit" "$got_exit" "0"

# ── happy path: `use` hoists an unqualified ctor into scope ──
cat > "$fixdir/happy_use.bang" <<'BANG'
use geom (Mk)
match (Mk(3, 4) : geom_Pair) { Mk(a, b) -> a + b }
BANG
got_out="$("$bang" run "$fixdir/happy_use.bang" 2>/dev/null)" && got_exit=0 || got_exit=$?
check "happy-use-stdout" "$got_out" "7"
check "happy-use-exit" "$got_exit" "0"

# ── every EXISTING examples/*/main.bang still resolves + runs byte-identical to expected.txt ──
# (a decl-free/import-free file short-circuits through the SAME resolver — the D1 behavior-
# preservation claim, exercised here at the CLI rather than re-asserted in Lean.)
sweep_pass=0
sweep_fail=0
for dir in examples/*/; do
  main="$dir/main.bang"
  expected="$dir/expected.txt"
  name="$(basename "$dir")"
  [ -f "$main" ] && [ -f "$expected" ] || continue
  actual="$("$bang" run "$main" 2>/dev/null)" || { echo "✗ sweep-$name — run itself failed"; sweep_fail=$((sweep_fail + 1)); continue; }
  want="$(cat "$expected")"
  if [ "$actual" = "$want" ]; then
    sweep_pass=$((sweep_pass + 1))
  else
    echo "✗ sweep-$name — got [$actual] want [$want]"; sweep_fail=$((sweep_fail + 1))
  fi
done
if [ "$sweep_fail" -eq 0 ]; then
  echo "✓ existing-examples-unchanged ($sweep_pass/$sweep_pass)"; pass=$((pass + 1))
else
  echo "✗ existing-examples-unchanged ($sweep_fail failed)"; fail=$((fail + 1))
fi

# ── missing import: a loud error naming BOTH probed paths (D1) ──
cat > "$fixdir/missing_import.bang" <<'BANG'
import nonexistent
0
BANG
got_err="$("$bang" run "$fixdir/missing_import.bang" 2>&1 >/dev/null)" && got_err_exit=0 || got_err_exit=$?
check "missing-import-exit" "$got_err_exit" "1"
check_contains "missing-import-names-modname" "$got_err" "nonexistent"
check_contains "missing-import-names-samedir-path" "$got_err" "$fixdir"
check_contains "missing-import-names-root-path" "$got_err" "$(git rev-parse --show-toplevel)"

# ── import cycle: a loud error naming the cycle (ADR-0076's acyclic-DAG pin) ──
cat > "$fixdir/cycle_a.bang" <<'BANG'
import cycle_b
0
BANG
cat > "$fixdir/cycle_b.bang" <<'BANG'
import cycle_a
0
BANG
got_err="$("$bang" run "$fixdir/cycle_a.bang" 2>&1 >/dev/null)" && got_err_exit=0 || got_err_exit=$?
check "cycle-exit" "$got_err_exit" "1"
check_contains "cycle-names-cycle" "$got_err" "cycle"
check_contains "cycle-names-cycle_a" "$got_err" "cycle_a"
check_contains "cycle-names-cycle_b" "$got_err" "cycle_b"

# ── private-decl access: a loud error naming both the decl and the module (D3) ──
cat > "$fixdir/priv.bang" <<'BANG'
data Secret = Hidden(Int)
0
BANG
cat > "$fixdir/priv_use.bang" <<'BANG'
use priv (Secret)
0
BANG
got_err="$("$bang" run "$fixdir/priv_use.bang" 2>&1 >/dev/null)" && got_err_exit=0 || got_err_exit=$?
check "private-access-exit" "$got_err_exit" "1"
check_contains "private-access-names-decl" "$got_err" "Secret"
check_contains "private-access-names-module" "$got_err" "priv"
check_contains "private-access-says-private" "$got_err" "private"

# ── #73 fix: QUALIFIED (`Mod.name`) access to a non-pub decl must reject the SAME as the `use`
# path above — the exact enforcement hole the stranger-test found (`$(Bare.plain) 41` silently
# resolved to 42 with no error, while `use Bare (plain)` correctly rejected). Positive case
# alongside it: `pub`-qualified access must keep working (D3 is "private, not deleted", not
# "qualified access disabled"). ──
cat > "$fixdir/qualbare.bang" <<'BANG'
let plain = {fun x => x + 1}
BANG
cat > "$fixdir/qual_private.bang" <<'BANG'
import qualbare
let main = $(qualbare.plain) 41
BANG
got_err="$("$bang" run "$fixdir/qual_private.bang" 2>&1 >/dev/null)" && got_err_exit=0 || got_err_exit=$?
check "qualified-private-access-exit" "$got_err_exit" "1"
check_contains "qualified-private-access-names-decl" "$got_err" "plain"
check_contains "qualified-private-access-names-module" "$got_err" "qualbare"
check_contains "qualified-private-access-says-private" "$got_err" "private"

cat > "$fixdir/qualpub.bang" <<'BANG'
pub let plain = {fun x => x + 1}
BANG
cat > "$fixdir/qual_pub.bang" <<'BANG'
import qualpub
let main = $(qualpub.plain) 41
BANG
got_out="$("$bang" run "$fixdir/qual_pub.bang" 2>/dev/null)" && got_exit=0 || got_exit=$?
check "qualified-pub-access-stdout" "$got_out" "42"
check "qualified-pub-access-exit" "$got_exit" "0"

# ── same-dir import shadows a root-level module of the same name (D1's documented search order:
# same-dir FIRST, then root) — a decoy module living AT THE PROJECT ROOT (the resolver's `root`,
# `IO.currentDir` = repo top-level per `resolveEntryFile`) must NOT be picked when a same-named
# module also exists next to the importing file. Written under a repo-root-relative name that is
# vanishingly unlikely to collide with anything real, and torn down unconditionally on exit — this
# is the ONE check that must touch the shared tree at all (D1's search order names the root as a
# real search location, so testing it honestly requires a real file there), kept to a single
# scratch file with an EXIT trap so no other lane observes it mid-run or after.
repo_root="$(git rev-parse --show-toplevel)"
decoy="$repo_root/bang_modules_test_shadow_decoy.bang"
trap 'rm -rf "$fixdir" "$decoy"' EXIT
cat > "$decoy" <<'BANG'
pub data Wrong = W(Int)
BANG
cat > "$fixdir/bang_modules_test_shadow_decoy.bang" <<'BANG'
pub data Correct = R(Int)
BANG
cat > "$fixdir/shadow_user.bang" <<'BANG'
import bang_modules_test_shadow_decoy
match (bang_modules_test_shadow_decoy.R(9) : bang_modules_test_shadow_decoy_Correct) { R(n) -> n }
BANG
got_out="$("$bang" run "$fixdir/shadow_user.bang" 2>/dev/null)" && got_exit=0 || got_exit=$?
check "same-dir-shadows-root-stdout" "$got_out" "9"
check "same-dir-shadows-root-exit" "$got_exit" "0"

# ── ADR-0093 D5 (operator ruling): the entry-mode rule — a decl named `main` is the whole point of
# the ruling ("main is literally a let decl, no special form"). Four cases: program mode (main +
# library-mode-otherwise), script mode (unchanged corpus), both present (loud error), neither
# (loud error — a library run directly). ──
cat > "$fixdir/lib_for_main.bang" <<'BANG'
pub let rec double : Int -> Int = fun n => n + n
BANG
cat > "$fixdir/entry_program_mode.bang" <<'BANG'
use lib_for_main (double)
let main = ($double) 21
BANG
got_out="$("$bang" run "$fixdir/entry_program_mode.bang" 2>/dev/null)" && got_exit=0 || got_exit=$?
check "d5-program-mode-stdout" "$got_out" "42"
check "d5-program-mode-exit" "$got_exit" "0"

cat > "$fixdir/entry_script_mode.bang" <<'BANG'
let x = 3 in x + 1
BANG
got_out="$("$bang" run "$fixdir/entry_script_mode.bang" 2>/dev/null)" && got_exit=0 || got_exit=$?
check "d5-script-mode-stdout" "$got_out" "4"
check "d5-script-mode-exit" "$got_exit" "0"

cat > "$fixdir/entry_both.bang" <<'BANG'
let main = 42
let x = 3 in x
BANG
got_err="$("$bang" run "$fixdir/entry_both.bang" 2>&1 >/dev/null)" && got_err_exit=0 || got_err_exit=$?
check "d5-both-present-exit" "$got_err_exit" "1"
check_contains "d5-both-present-names-main" "$got_err" "main"

cat > "$fixdir/entry_library.bang" <<'BANG'
pub let x = 3
BANG
got_err="$("$bang" run "$fixdir/entry_library.bang" 2>&1 >/dev/null)" && got_err_exit=0 || got_err_exit=$?
check "d5-library-mode-exit" "$got_err_exit" "1"
check_contains "d5-library-mode-says-library" "$got_err" "library"

# ── plan 005 (symlink containment): an import-derived module whose SYMLINK resolves outside BOTH
# allowed trees (the entry file's directory subtree AND the CWD root subtree — the two probe
# locations of D1's search order) must be rejected LOUDLY, naming the resolved real path and both
# trees. `escdir` is a second mktemp dir — a SIBLING of `fixdir`, so outside the entry tree, and
# under /tmp, so outside the repo root too. The entry FILE itself is exempt by design (the user's
# explicit choice — every case in this file already runs an entry from /tmp, outside the CWD root,
# which is the standing pin of that exemption). ──
escdir="$(mktemp -d --tmpdir bang-modules-escape-XXXXXX)"
trap 'rm -rf "$fixdir" "$decoy" "$escdir"' EXIT
cat > "$escdir/escape_secret.bang" <<'BANG'
pub data Outside = O(Int)
BANG
ln -s "$escdir/escape_secret.bang" "$fixdir/outside.bang"
cat > "$fixdir/symlink_escape.bang" <<'BANG'
import outside
0
BANG
got_err="$("$bang" run "$fixdir/symlink_escape.bang" 2>&1 >/dev/null)" && got_err_exit=0 || got_err_exit=$?
check "symlink-escape-exit" "$got_err_exit" "1"
check_contains "symlink-escape-says-escapes" "$got_err" "escapes the project"
check_contains "symlink-escape-names-real-target" "$got_err" "escape_secret.bang"
check_contains "symlink-escape-names-entry-tree" "$got_err" "entry tree"
check_contains "symlink-escape-names-root" "$got_err" "the root"

# ── plan 005 green control: a symlink resolving WITHIN an allowed tree (here: the entry tree)
# still works — containment rejects only ESCAPING symlinks, not symlinks per se (pinned). ──
cat > "$fixdir/inside_real.bang" <<'BANG'
pub data In = I(Int)
BANG
ln -s "$fixdir/inside_real.bang" "$fixdir/inside.bang"
cat > "$fixdir/symlink_inside.bang" <<'BANG'
import inside
match (inside.I(5) : inside_In) { inside_I(n) -> n }
BANG
got_out="$("$bang" run "$fixdir/symlink_inside.bang" 2>/dev/null)" && got_exit=0 || got_exit=$?
check "symlink-within-tree-stdout" "$got_out" "5"
check "symlink-within-tree-exit" "$got_exit" "0"

echo "──────────────────────────────"
echo "modules: $pass passed, $fail failed"
[ "$fail" -eq 0 ]
