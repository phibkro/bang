#!/usr/bin/env bash
# tool: role=test couples=justfile,tools/test-*.sh runs-in=verify
source "$(git rev-parse --show-toplevel 2>/dev/null)/tools/tool-log.sh" 2>/dev/null && tool_log "$(basename "$0")" || true
# run-batteries.sh — concurrent driver for the independent verify batteries (plan 004).
#
# Each ordinary tools/test-*.sh (+ check-examples.sh) is independent by construction: its own
# mktemp'd fixtures, read-only against examples/, no shared mutable state between
# scripts (test-modules.sh's repo-root decoy file is torn down via its own EXIT trap
# before this driver's next battery could observe it). That independence is what lets
# them run concurrently instead of serially.
#
# The four role-lab harnesses are the deliberate exception. They consume one exact-HEAD
# built template through private reflink snapshots; tools/test-role-labs.sh owns that
# fan-out and asserts a clean boundary before/after each harness. Pointing all four at
# the same writable checkout would let one observe another's root fixtures.
#
# Ensure the runner is current up front, then tell every battery via BANG_BIN_FRESH
# to skip its own rebuild (tools/test-*.sh honor this — see the conditional rebuild
# each carries). Under `just verify`, the warning-wrapped `build` recipe has already
# built this same target, so this is an incremental check rather than a second cold build.
# Role-lab standalone recipes still create/build private lanes. In this runner, the
# BANG_ROLE_LAB_LANE handoff makes all four use the one lane built below.
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

echo "building shared battery target…" >&2
lake build bang >&2
export BANG_BIN_FRESH=1

workdir="$(mktemp -d --tmpdir bang-run-batteries-XXXXXX)"
trap 'rm -rf "$workdir"' EXIT

source_head="$(git rev-parse HEAD)"
role_lab_lane="$workdir/role-lab-lane"
role_lab_branch="practice/role-labs-battery-$$-$(date +%s)"
echo "creating shared exact-HEAD role-lab lane…" >&2
tools/new-worktree.sh "$role_lab_lane" "$role_lab_branch" "$source_head" >&2
# The root target was built immediately above. Give the isolated lane a private
# reflink of those artifacts, then still run lake inside the lane below: Lake's
# trace validation rebuilds any mismatch, while the common exact-HEAD case avoids
# recompiling 1,450 jobs. The lane never writes the source checkout's .lake.
cp -r --reflink=auto .lake/build "$role_lab_lane/.lake/build"
export BANG_ROLE_LAB_LANE="$role_lab_lane"
export BANG_ROLE_LAB_HEAD="$source_head"

batteries=(check-examples check-examples-env test-example-exit-status test-repl test-fmt test-check-json test-query \
           test-cli-exit-status test-rewrite test-annotate test-lint test-82-verbs test-cli test-cli-options test-lean-warnings test-release-version test-release-integrity test-law test-modules \
           test-explain test-hostio-seam test-host-authority test-reference-samples test-docfacts-language test-docfacts-logger test-out-of-fuel-naming test-onboarding-journey \
           test-compiled-dogfood test-bang-build test-role-labs)

pids=()
outfiles=()
deferred_role_labs=0
for name in "${batteries[@]}"; do
  if [ "$name" = test-role-labs ]; then
    deferred_role_labs=$((deferred_role_labs + 1))
    continue
  fi
  outfile="$workdir/$name.out"
  outfiles+=("$outfile")
  bash "tools/${name}.sh" >"$outfile" 2>&1 &
  pids+=("$!")
done
[ "$deferred_role_labs" -eq 1 ] || {
  echo "run-batteries: INTERNAL ERROR — expected one deferred role-lab composite, found $deferred_role_labs" >&2
  exit 1
}

# Overlap the one trace-validating in-lane build with the independent batteries above. The
# composite is launched only after this PID has been collected successfully.
lane_build_out="$workdir/role-lab-lane-build.out"
(
  cd "$role_lab_lane"
  lake build bang
) >"$lane_build_out" 2>&1 &
lane_build_pid="$!"

lane_ready=1
if wait "$lane_build_pid"; then
  [ "$(git -C "$role_lab_lane" rev-parse HEAD)" = "$source_head" ] || lane_ready=0
  [ -z "$(git -C "$role_lab_lane" status --porcelain)" ] || lane_ready=0
else
  lane_ready=0
fi
echo "── shared role-lab lane build ──" >&2
cat "$lane_build_out" >&2

role_labs_out="$workdir/test-role-labs.out"
outfiles+=("$role_labs_out")
if [ "$lane_ready" -eq 1 ]; then
  bash tools/test-role-labs.sh >"$role_labs_out" 2>&1 &
else
  (
    echo "run-batteries: shared role-lab lane build/provenance failed" >&2
    git -C "$role_lab_lane" status --short >&2 || true
    exit 1
  ) >"$role_labs_out" 2>&1 &
fi
pids+=("$!")

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
