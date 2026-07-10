#!/usr/bin/env bash
# tool: role=test couples=examples/*/main.bang runs-in=verify
source "$(git rev-parse --show-toplevel 2>/dev/null)/tools/tool-log.sh" 2>/dev/null && tool_log "$(basename "$0")" || true
# test-fmt.sh — the non-interactive gate for `bang fmt` (issue #58's CLI half).
#
# Mirrors test-repl.sh's shape (build once, exercise the binary, diff, tally pass/fail). The
# formatter CORE's laws (idempotency/round-trip over a corpus, `Bang/Frontend/Format.lean` §6-7)
# are already gated at the Lean `#guard` level — this file gates the CLI SURFACE specifically:
# file-arg vs stdin, exit codes, and idempotency observed THROUGH the binary (not just the pure
# function), since the CLI's stdin-reading/arg-parsing is new code the `#guard`s never touch.
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"
bang=".lake/build/bin/bang"

if [ -z "${BANG_BIN_FRESH:-}" ]; then
  echo "building bang runner…" >&2
  lake build bang >&2
fi

pass=0
fail=0

# `check NAME GOT WANT` — generic string-equality tally (used for ad-hoc checks below that don't
# fit the "single command, single assertion" shape of check_cmd/check_cmd_stderr).
check() {
  local name="$1" got="$2" want="$3"
  if [ "$got" = "$want" ]; then
    echo "✓ $name"; pass=$((pass + 1))
  else
    echo "✗ $name — expected [$want], got [$got]"; fail=$((fail + 1))
  fi
}

# ── happy path: a known corpus file → its exact canonical form ──
# (examples/state/main.bang is a small fixed program; pin the LITERAL expected output so a printer
# regression shows as a diff here, not just "still parses". Canonical form since issue #71:
# sequential let-bindings collapse to ONE `;`-block, so `let c = ... in let z = ... in $c`
# prints as `let c = ...; z = ... in $c`.)
got_out="$("$bang" fmt examples/state/main.bang 2>/dev/null)" && got_exit=0 || got_exit=$?
want_out="state 0 in let c = {get}; z = put 5 in \$c"
check "happy-path-stdout" "$got_out" "$want_out"
check "happy-path-exit" "$got_exit" "0"

# ── file-arg and stdin agree on the SAME input (the two entry points must be one code path) ──
got_stdin="$(cat examples/state/main.bang | "$bang" fmt 2>/dev/null)" || true
check "file-and-stdin-agree" "$got_stdin" "$got_out"

# ── idempotency AT THE CLI: piping fmt's own output back through fmt is byte-identical ──
got_twice="$(printf '%s' "$got_out" | "$bang" fmt 2>/dev/null)" || true
check "idempotent-via-cli" "$got_twice" "$got_out"

# ── idempotency swept over every examples/*/main.bang (the corpus, not just one file) ──
idempotent_pass=0
idempotent_fail=0
for dir in examples/*/; do
  main="$dir/main.bang"
  name="$(basename "$dir")"
  [ -f "$main" ] || continue
  once="$("$bang" fmt "$main" 2>/dev/null)" || { echo "✗ idempotent-sweep-$name — fmt itself failed"; idempotent_fail=$((idempotent_fail + 1)); continue; }
  twice="$(printf '%s' "$once" | "$bang" fmt 2>/dev/null)" || true
  if [ "$once" = "$twice" ]; then
    idempotent_pass=$((idempotent_pass + 1))
  else
    echo "✗ idempotent-sweep-$name — fmt(fmt(x)) != fmt(x)"; idempotent_fail=$((idempotent_fail + 1))
  fi
done
if [ "$idempotent_fail" -eq 0 ]; then
  echo "✓ idempotent-sweep ($idempotent_pass/$idempotent_pass examples)"; pass=$((pass + 1))
else
  echo "✗ idempotent-sweep ($idempotent_fail failed)"; fail=$((fail + 1))
fi

# ── parse-error path: bad input fails loud, stdout stays EMPTY, distinct nonzero exit ──
got_err_out="$(printf 'let x 3 in x' | "$bang" fmt 2>/dev/null)" && got_err_exit=0 || got_err_exit=$?
check "parse-error-stdout-empty" "$got_err_out" ""
check "parse-error-exit" "$got_err_exit" "1"
got_stderr="$(printf 'let x 3 in x' | "$bang" fmt 2>&1 >/dev/null)" || true
if [[ "$got_stderr" == *"error:"* ]]; then
  echo "✓ parse-error-stderr-content"; pass=$((pass + 1))
else
  echo "✗ parse-error-stderr-content — expected an 'error:' line, got [$got_stderr]"; fail=$((fail + 1))
fi

# ── too many positional args is a usage error, not a silent pick-first/pick-last ──
got_argerr_exit=0
"$bang" fmt a.bang b.bang >/dev/null 2>&1 || got_argerr_exit=$?
check "too-many-args-exit" "$got_argerr_exit" "1"

# ── COMMENT metamorphic sanity (issue #62): fmt(commented) == fmt(uncommented twin) ──
# `--` line comments are lexer-stripped BEFORE parsing (documented, not silent — see the
# reference's Lexical notes section), so a commented program's canonical form must be
# byte-identical to its uncommented twin's — the comment can never leak into the printed output.
commented=$'-- leading whole-line comment\nlet x = 3 -- trailing on the binding\nin\n  -- indented whole-line comment\n  let y = 4 -- trailing again\n  in x + y -- final trailing, no newline after'
uncommented=$'\nlet x = 3 \nin\n  \n  let y = 4 \n  in x + y '
got_commented="$(printf '%s' "$commented" | "$bang" fmt 2>/dev/null)" || true
got_uncommented="$(printf '%s' "$uncommented" | "$bang" fmt 2>/dev/null)" || true
check "comment-metamorphic-fmt" "$got_commented" "$got_uncommented"
# and the commented program still RUNS to the same value the uncommented twin does (`run`
# takes a FILE arg, unlike `fmt`/`check` — no stdin form — so write it out first).
commented_tmp="$(mktemp /tmp/bang-comment-test-XXXXXX.bang)"
trap 'rm -f "$commented_tmp"' EXIT
printf '%s' "$commented" > "$commented_tmp"
got_commented_run="$("$bang" run "$commented_tmp" 2>/dev/null)" && got_commented_run_exit=0 || got_commented_run_exit=$?
check "comment-metamorphic-run" "$got_commented_run" "7"
check "comment-metamorphic-run-exit" "$got_commented_run_exit" "0"

# ── QUALIFIED FORCE `$(Mod.op)` (issue #96) — the CLI-level half of the fix's proof ──
# `Bang/Frontend/Format.lean`'s own `#guard` corpus already covers AST round-trip/idempotency
# for these shapes (pure-function level, no elaboration). This block additionally checks the
# END-TO-END claim the issue is actually about: a REAL multi-file program using `$(Mod.op)`
# still RUNS to the correct answer after `bang fmt` — the "not a value" break the finding note
# reported can ONLY be observed with a real import + `bang run`, so it belongs here, not in the
# pure-parser corpus. `main.bang` in a scratch dir mirrors the note's own 3-line `g.bang` repro.
fmt96_dir="$(mktemp -d /tmp/bang-fmt96-XXXXXX)"
trap 'rm -f "$commented_tmp"; rm -rf "$fmt96_dir"' EXIT
cat > "$fmt96_dir/g.bang" <<'BANGEOF'
pub let mk = {fun s => s + 1}
BANGEOF
cat > "$fmt96_dir/main.bang" <<'BANGEOF'
import g
let main =
  let ast = $(g.mk) 5 in ast
BANGEOF

# bug 1: fmt must not break the program — pre-fix, `bang run` on the fmt'd output errored
# ("not a value") instead of printing 6.
got_96_orig="$("$bang" run "$fmt96_dir/main.bang" 2>/dev/null)" && got_96_orig_exit=0 || got_96_orig_exit=$?
check "issue96-original-runs" "$got_96_orig" "6"
check "issue96-original-exit" "$got_96_orig_exit" "0"
got_96_fmt="$("$bang" fmt "$fmt96_dir/main.bang" 2>/dev/null)" || true
printf '%s\n' "$got_96_fmt" > "$fmt96_dir/main_fmt.bang"
got_96_fmt_run="$("$bang" run "$fmt96_dir/main_fmt.bang" 2>/dev/null)" && got_96_fmt_run_exit=0 || got_96_fmt_run_exit=$?
check "issue96-fmt-output-still-runs" "$got_96_fmt_run" "6"
check "issue96-fmt-output-exit" "$got_96_fmt_run_exit" "0"
# and fmt must PRESERVE the disambiguating parens verbatim (the direct textual falsification —
# pre-fix this was `$g.mk 5`, which mis-parses as `($g).mk 5`).
if [[ "$got_96_fmt" == *'$(g.mk)'* ]]; then
  echo "✓ issue96-parens-preserved"; pass=$((pass + 1))
else
  echo "✗ issue96-parens-preserved — expected '\$(g.mk)' in fmt output, got [$got_96_fmt]"; fail=$((fail + 1))
fi

# bug 2: `$(Mod.op) (arg)` (a parenthesized argument after a qualified force) must be a FIXED
# POINT under repeated fmt — pre-fix this oscillated `$Mod.op (arg)` ⟷ `$Mod.op(arg)` (and the
# FIRST pass already broke the program per bug 1; this checks the space-collapse specifically,
# on a two-module chain matching `examples/calc/main.bang`'s own `$(Parser.parseAll)
# ($(Lexer.lex) src)` idiom).
cat > "$fmt96_dir/g2.bang" <<'BANGEOF'
pub let mk = {fun s => s + 1}
pub let mk2 = {fun s => s + 2}
BANGEOF
cat > "$fmt96_dir/main2.bang" <<'BANGEOF'
import g2
let main =
  let ast = $(g2.mk) ($(g2.mk2) 5) in ast
BANGEOF
got_96b_once="$("$bang" fmt "$fmt96_dir/main2.bang" 2>/dev/null)" || true
mkdir -p "$fmt96_dir/pass2" && cp "$fmt96_dir/g2.bang" "$fmt96_dir/pass2/"
printf '%s\n' "$got_96b_once" > "$fmt96_dir/pass2/main.bang"
got_96b_twice="$("$bang" fmt "$fmt96_dir/pass2/main.bang" 2>/dev/null)" || true
check "issue96-spaced-arg-idempotent" "$got_96b_twice" "$got_96b_once"
got_96b_run="$("$bang" run "$fmt96_dir/main2.bang" 2>/dev/null)" && got_96b_run_exit=0 || got_96b_run_exit=$?
check "issue96-spaced-arg-original-runs" "$got_96b_run" "8"
check "issue96-spaced-arg-original-exit" "$got_96b_run_exit" "0"

echo "──────────────────────────────"
echo "fmt: $pass passed, $fail failed"
[ "$fail" -eq 0 ]
