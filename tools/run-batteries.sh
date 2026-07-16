#!/usr/bin/env bash
# tool: role=test couples=justfile,tools/test-*.sh runs-in=verify
source "$(git rev-parse --show-toplevel 2>/dev/null)/tools/tool-log.sh" 2>/dev/null && tool_log "$(basename "$0")" || true
# run-batteries.sh — concurrent driver for the independent verify batteries (plan 004).
#
# Each tools/test-*.sh (+ check-examples.sh) is independent by construction: its own
# mktemp'd fixtures, read-only against examples/, no shared mutable state between
# scripts (test-modules.sh's repo-root decoy file is torn down via its own EXIT trap
# before this driver's next battery could observe it). That independence is what lets
# them run concurrently instead of serially.
#
# Build ONCE up front (each battery's own `lake build bang` is normally a ~1s
# incremental no-op, but eleven of them serialize to real time) and tell every battery
# via BANG_BIN_FRESH to skip its own rebuild (tools/test-*.sh honor this — see the
# conditional rebuild each carries).
#
# FALSE-GREEN DEFENSES (this script IS part of the gate, so it must not paper over a
# hung/missing battery):
#   - every battery's full output is captured to its own tmp file and printed
#     sequentially AFTER all finish — no interleaving, and nothing is silently dropped.
#   - `wait` is called on each PID INDIVIDUALLY (a bare `wait` collapses all exit
#     statuses into one and loses which battery failed).
#   - the number of captured statuses is asserted to equal the number of batteries
#     launched — a script that never launched (typo, `set -e` fallthrough) fails loud
#     instead of silently vanishing from the count.
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"

echo "building bang runner…" >&2
lake build bang >&2
export BANG_BIN_FRESH=1

batteries=(check-examples check-examples-env test-example-exit-status test-repl test-fmt test-check-json test-query \
           test-cli-exit-status test-rewrite test-annotate test-lint test-82-verbs test-cli test-cli-options test-lean-warnings test-release-version test-release-integrity test-law test-modules \
           test-explain test-hostio-seam test-host-authority test-reference-samples test-docfacts-language test-docfacts-logger test-onboarding-journey \
           test-role-lab-frontend test-compiled-dogfood test-bang-build)

workdir="$(mktemp -d --tmpdir bang-run-batteries-XXXXXX)"
trap 'rm -rf "$workdir"' EXIT

pids=()
outfiles=()
for name in "${batteries[@]}"; do
  outfile="$workdir/$name.out"
  outfiles+=("$outfile")
  bash "tools/${name}.sh" >"$outfile" 2>&1 &
  pids+=("$!")
done

statuses=()
for pid in "${pids[@]}"; do
  if wait "$pid"; then
    statuses+=("0")
  else
    statuses+=("$?")
  fi
done

# Count assertion — a false-green defense: if a battery's PID/status pair never made
# it into the array (a bug in the loops above, not a battery failure), fail loud
# instead of silently reporting a partial gate as green.
if [ "${#statuses[@]}" -ne "${#batteries[@]}" ]; then
  echo "run-batteries: INTERNAL ERROR — collected ${#statuses[@]} statuses for ${#batteries[@]} batteries. Aborting rather than reporting a partial result." >&2
  exit 1
fi

failed=()
for i in "${!batteries[@]}"; do
  name="${batteries[$i]}"
  echo "── ${name} ──"
  cat "${outfiles[$i]}"
  if [ "${statuses[$i]}" -ne 0 ]; then
    failed+=("$name")
  fi
done

echo "──────────────────────────────"
if [ "${#failed[@]}" -eq 0 ]; then
  echo "run-batteries: ${#batteries[@]}/${#batteries[@]} batteries passed."
  exit 0
else
  echo "run-batteries: ${#failed[@]} FAILED — ${failed[*]}"
  exit 1
fi
