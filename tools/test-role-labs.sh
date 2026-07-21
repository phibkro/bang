#!/usr/bin/env bash
# tool: role=test couples=web/docs/role-lab-lane.mjs,web/docs/test-role-lab-lane.mjs,tools/test-role-lab-frontend.sh,tools/test-role-lab-kernel-proof.sh,tools/test-role-lab-machine-backend.sh,tools/test-role-lab-tooling-docs-examples.sh runs-in=verify
source "$(git rev-parse --show-toplevel 2>/dev/null)/tools/tool-log.sh" 2>/dev/null && tool_log "$(basename "$0")" || true
# Concurrent composite consuming one runner-owned, built exact-HEAD lane through
# private reflink snapshots. The snapshots isolate root fixtures without cloning
# or rebuilding the template.
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"

lane="${BANG_ROLE_LAB_LANE:?run-batteries must provide BANG_ROLE_LAB_LANE}"
source_head="$(git rev-parse HEAD)"
[ "${BANG_ROLE_LAB_HEAD:?run-batteries must provide BANG_ROLE_LAB_HEAD}" = "$source_head" ] || {
  echo "role-labs: shared lane handoff does not name source HEAD $source_head" >&2
  exit 1
}

assert_lane_boundary() {
  local checked_lane="$1" boundary="$2" lane_root lane_head lane_status
  lane_root="$(git -C "$checked_lane" rev-parse --show-toplevel)"
  lane_head="$(git -C "$checked_lane" rev-parse HEAD)"
  lane_status="$(git -C "$checked_lane" status --porcelain)"
  [ "$lane_root" = "$checked_lane" ] || {
    echo "role-labs: $boundary: handoff path is not the checkout root: $lane_root" >&2
    exit 1
  }
  [ "$lane_head" = "$source_head" ] || {
    echo "role-labs: $boundary: lane $lane_head is not exact source HEAD $source_head" >&2
    exit 1
  }
  [ -z "$lane_status" ] || {
    echo "role-labs: $boundary: lane is dirty" >&2
    printf '%s\n' "$lane_status" >&2
    exit 1
  }
}

node web/docs/test-role-lab-lane.mjs

role_lab_batteries=(test-role-lab-frontend test-role-lab-kernel-proof test-role-lab-machine-backend test-role-lab-tooling-docs-examples)
cold_artifacts=('' .lake/build/lib/lean/Bang/Core/Soundness.olean .lake/build/bin/bang .lake/build/bin/bang)
[ "${#cold_artifacts[@]}" -eq "${#role_lab_batteries[@]}" ] || {
  echo "role-labs: INTERNAL ERROR — cold-artifact map does not cover every enrolled harness" >&2
  exit 1
}
snapshot_root="$(mktemp -d --tmpdir bang-role-lab-snapshots-XXXXXX)"
trap 'rm -rf "$snapshot_root"' EXIT
outfiles=()
snapshots=()
assert_lane_boundary "$lane" "before snapshot fan-out (built template)"
for name in "${role_lab_batteries[@]}"; do
  snapshot="$snapshot_root/$name"
  cp -a --reflink=auto "$lane" "$snapshot"
  assert_lane_boundary "$snapshot" "before $name"
  [ -x "$snapshot/.lake/build/bin/bang" ] || {
    echo "role-labs: $name snapshot is missing the lane-built binary" >&2
    exit 1
  }
  snapshots+=("$snapshot")
done

# Falsifier pole for the concurrency design: a root fixture in one writable
# snapshot must be invisible to the built template and every sibling snapshot.
probe="${snapshots[0]}/role-lab-isolation-probe"
printf '%s\n' probe > "$probe"
[ ! -e "$lane/role-lab-isolation-probe" ] || {
  echo "role-labs: snapshot fixture leaked into the built template" >&2
  exit 1
}
for snapshot in "${snapshots[@]:1}"; do
  [ ! -e "$snapshot/role-lab-isolation-probe" ] || {
    echo "role-labs: snapshot fixture leaked into a sibling" >&2
    exit 1
  }
done
rm -f "$probe"
assert_lane_boundary "${snapshots[0]}" "after snapshot-isolation falsifier"

# Targeted cold-artifact poles preserve the displayed-build-command defense on
# warm snapshots. If one of the three clone-based pages drops or weakens its own
# first build command, its later journey cannot consume the missing output and
# this composite also requires the exact artifact to be restored.
for i in "${!cold_artifacts[@]}"; do
  artifact="${cold_artifacts[$i]}"
  [ -z "$artifact" ] && continue
  [ -s "$lane/$artifact" ] || {
    echo "role-labs: built template is missing cold-probe source $artifact" >&2
    exit 1
  }
  rm -f "${snapshots[$i]}/$artifact"
  [ ! -e "${snapshots[$i]}/$artifact" ] || {
    echo "role-labs: failed to remove cold-probe artifact for ${role_lab_batteries[$i]}" >&2
    exit 1
  }
  [ -s "$lane/$artifact" ] || {
    echo "role-labs: cold-probe removal leaked into the built template" >&2
    exit 1
  }
done

pids=()
for i in "${!role_lab_batteries[@]}"; do
  name="${role_lab_batteries[$i]}"
  outfile="$snapshot_root/$name.out"
  outfiles+=("$outfile")
  BANG_ROLE_LAB_LANE="${snapshots[$i]}" bash "tools/${name}.sh" >"$outfile" 2>&1 &
  pids+=("$!")
done

statuses=()
for pid in "${pids[@]}"; do
  if wait "$pid"; then
    statuses+=(0)
  else
    statuses+=("$?")
  fi
done

[ "${#statuses[@]}" -eq "${#role_lab_batteries[@]}" ] || {
  echo "role-labs: INTERNAL ERROR — collected ${#statuses[@]}/${#role_lab_batteries[@]} statuses" >&2
  exit 1
}
[ "${#role_lab_batteries[@]}" -eq 4 ] || {
  echo "role-labs: INTERNAL ERROR — expected four enrolled role-lab harnesses" >&2
  exit 1
}

failed=()
for i in "${!role_lab_batteries[@]}"; do
  name="${role_lab_batteries[$i]}"
  echo "── $name (shared built lane snapshot) ──"
  cat "${outfiles[$i]}"
  if [ "${statuses[$i]}" -ne 0 ]; then
    failed+=("$name")
    continue
  fi
  pass_prefix="${name#test-}: PASS"
  [ "$(grep -c "^${pass_prefix}" "${outfiles[$i]}")" -eq 1 ] || {
    echo "role-labs: $name did not emit exactly one PASS line" >&2
    exit 1
  }
  artifact="${cold_artifacts[$i]}"
  if [ -n "$artifact" ]; then
    [ -s "${snapshots[$i]}/$artifact" ] || {
      echo "role-labs: $name did not restore its displayed build output $artifact" >&2
      exit 1
    }
  fi
  assert_lane_boundary "${snapshots[$i]}" "after $name"
done

assert_lane_boundary "$lane" "after all role labs (built template)"
[ "${#failed[@]}" -eq 0 ] || {
  echo "role-labs: ${#failed[@]} FAILED — ${failed[*]}" >&2
  exit 1
}

echo "role-labs: 4/4 harnesses passed in isolated snapshots of one shared built exact-HEAD lane; 3/3 displayed-build cold-artifact poles restored."
