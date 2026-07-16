#!/usr/bin/env bash
# tool: role=test couples=examples/*/main.bang,examples/*/expected.txt runs-in=verify
source "$(git rev-parse --show-toplevel 2>/dev/null)/tools/tool-log.sh" 2>/dev/null && tool_log "$(basename "$0")" || true
# check-examples.sh — the RUN-oracle gate for the bang example projects.
#
# For each examples/<project>/main.bang, run it through the `bang` runner and
# diff stdout against examples/<project>/expected.txt. A mismatch FAILS the gate.
# This is a real end-to-end check of the surface→check→lower→eval pipeline on
# whole bang PROGRAMS — it supersedes the hand-written per-example `#guard`s.
#
# UPDATE MODE (plan 013 s8): `check-examples.sh --update <NAME>` re-runs ONLY the
# named example and rewrites its expected.txt from actual output — deliberate
# snapshot acceptance. By design it is NEVER bulk (a NAME is required, no
# --update-all): the oracle change stays a small, reviewable git diff, never an
# invisible mutation of every example at once. It prints the old→new diff LOUDLY
# and relies on git for review (the byte-diff IS the acceptance record). An
# unknown NAME is a loud error, exit 1 — never a silent no-op or a new stray file.
# This lives here (the harness), not `bang test`: `bang test` reads a single .bang
# FILE, whereas an example is a DIRECTORY this run-oracle harness owns.
#
# Runs the COMPILED binary directly (.lake/build/bin/bang) for clean stdout —
# `nix develop -c …` prints a shell banner to stdout, so we build once (banner
# to stderr) then invoke the binary. Requires the dev shell for `lake` (a `just`
# recipe already provides it).
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"
bang="${BANG_BIN:-.lake/build/bin/bang}"

# ALWAYS (re)build the runner — incremental, a no-op when current. Guarding on
# "missing" let a STALE exe through: `just build` (= `lake build`, the library)
# does NOT rebuild the exe, so a present-but-stale binary produced false results
# (a new example false-failing, or an old one false-passing). Build noise → stderr.
if [ -z "${BANG_BIN_FRESH:-}" ] && [ -z "${BANG_BIN:-}" ]; then
  echo "building bang runner…" >&2
  lake build bang >&2
fi

# ── UPDATE MODE: re-bake ONE named example's expected.txt from actual output ──
if [ "${1:-}" = "--update" ]; then
  name="${2:-}"
  if [ -z "$name" ]; then
    echo "✗ --update requires an example NAME (no bulk mode by design): check-examples.sh --update <NAME>" >&2
    exit 1
  fi
  dir="examples/$name"
  main="$dir/main.bang"
  expected="$dir/expected.txt"
  if [ ! -f "$main" ]; then
    echo "✗ no such example '$name' — '$main' does not exist" >&2
    exit 1
  fi
  # Capture actual output BYTE-EXACT (println's trailing newline included), exactly
  # what the gate loop above will later diff against.
  new="$("$bang" run "$main" 2>/dev/null)" && run_ok=1 || run_ok=0
  if [ "$run_ok" -ne 1 ]; then
    echo "✗ '$name' did not run cleanly (exit nonzero) — refusing to bake a failing run as the oracle" >&2
    echo "  re-run: $bang run $main" >&2
    exit 1
  fi
  old=""
  [ -f "$expected" ] && old="$(cat "$expected")"
  if [ "$old" = "$new" ]; then
    echo "= '$name' already up to date — expected.txt unchanged ($new)"
    exit 0
  fi
  echo "updating '$name' expected.txt:"
  echo "  OLD: [$old]"
  echo "  NEW: [$new]"
  # Write byte-exact (the trailing newline println emits, matching every other expected.txt).
  "$bang" run "$main" 2>/dev/null > "$expected"
  echo "wrote $expected — review the diff with 'git diff $expected'"
  exit 0
fi

pass=0
fail=0
expected_count=0
for dir in examples/*/; do
  [ -f "$dir/main.bang" ] && expected_count=$((expected_count + 1))
done

for dir in examples/*/; do
  main="$dir/main.bang"
  expected="$dir/expected.txt"
  name="$(basename "$dir")"
  [ -f "$main" ] || continue
  if [ ! -f "$expected" ]; then
    echo "✗ $name — no expected.txt"; fail=$((fail + 1)); continue
  fi
  if got="$("$bang" run "$main" 2>/dev/null)"; then
    run_status=0
  else
    run_status=$?
  fi
  want="$(cat "$expected")"
  if [ "$run_status" -eq 0 ] && [ "$got" = "$want" ]; then
    echo "✓ $name → $got"; pass=$((pass + 1))
  else
    echo "✗ $name — expected [$want], got [$got], status [$run_status]"; fail=$((fail + 1))
  fi
done

echo "──────────────────────────────"
echo "examples: $pass passed, $fail failed"
processed=$((pass + fail))
if [ "$processed" -ne "$expected_count" ]; then
  echo "check-examples: INTERNAL ERROR — processed $processed of $expected_count examples" >&2
  exit 1
fi
[ "$fail" -eq 0 ]
