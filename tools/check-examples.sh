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
# Runs the COMPILED binary directly (.lake/build/bin/bang) for clean stdout —
# `nix develop -c …` prints a shell banner to stdout, so we build once (banner
# to stderr) then invoke the binary. Requires the dev shell for `lake` (a `just`
# recipe already provides it).
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"
bang=".lake/build/bin/bang"

# ALWAYS (re)build the runner — incremental, a no-op when current. Guarding on
# "missing" let a STALE exe through: `just build` (= `lake build`, the library)
# does NOT rebuild the exe, so a present-but-stale binary produced false results
# (a new example false-failing, or an old one false-passing). Build noise → stderr.
if [ -z "${BANG_BIN_FRESH:-}" ]; then
  echo "building bang runner…" >&2
  lake build bang >&2
fi

pass=0
fail=0
for dir in examples/*/; do
  main="$dir/main.bang"
  expected="$dir/expected.txt"
  name="$(basename "$dir")"
  [ -f "$main" ] || continue
  if [ ! -f "$expected" ]; then
    echo "✗ $name — no expected.txt"; fail=$((fail + 1)); continue
  fi
  got="$("$bang" run "$main" 2>/dev/null)" || true
  want="$(cat "$expected")"
  if [ "$got" = "$want" ]; then
    echo "✓ $name → $got"; pass=$((pass + 1))
  else
    echo "✗ $name — expected [$want], got [$got]"; fail=$((fail + 1))
  fi
done

echo "──────────────────────────────"
echo "examples: $pass passed, $fail failed"
[ "$fail" -eq 0 ]
