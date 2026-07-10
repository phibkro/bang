# Plan 004: Speed up and complete the verify loop — wire test-modules, parallelize the batteries

> **Executor instructions**: Follow this plan step by step. Run every
> verification command and confirm the expected result before moving to the
> next step. If anything in the "STOP conditions" section occurs, stop and
> report — do not improvise. When done, update the status row for this plan
> in `plans/README.md` — unless a reviewer dispatched you and told you they
> maintain the index.
>
> **Drift check (run first)**: `git diff --stat f1cb2cf..HEAD -- justfile tools/`
> If `justfile` or `tools/` changed since this plan was written, compare the
> "Current state" excerpts against the live code before proceeding; on a
> mismatch, treat it as a STOP condition.

## Status

- **Priority**: P2
- **Effort**: M
- **Risk**: MED (touches the gate itself — a bug here can produce false-greens; the design below defends against that)
- **Depends on**: none (but land AFTER plans 001–003 if executing several, so their new tests are in the measured baseline)
- **Category**: dx
- **Planned at**: commit `f1cb2cf`, 2026-07-10

## Why this matters

`just verify` is the repo's default gate: it runs on every `.lean`-touching commit via the pre-commit hook, and its wall-clock time is paid dozens of times a day in an agent-heavy workflow. Two concrete problems:

1. **A gate leg is missing.** `tools/test-modules.sh` — the non-interactive gate for the shipped file-modules feature (ADR-0093: `import`/`use`/`pub`) — has a justfile recipe but is NOT in `verify`'s leg list, while every other `test-*.sh` is. A modules regression currently passes the default gate. (`tools/README.md:70` labels it `manual`, but no rationale is recorded; the feature it gates is shipped and stable.)
2. **The batteries run serially.** After the single `build`, `verify` runs 12+ independent test scripts one after another; each also invokes `lake build bang` (incremental no-op, ~1s) before its own runs. The scripts are independent by construction (each spawns the compiled binary on its own fixture files) — they can run concurrently for a several-fold battery speedup.

## Current state

- `justfile:28` — the gate composition (verbatim):

```make
verify: selfcheck build check-examples test-repl test-fmt test-check-json test-query test-rewrite test-annotate test-lint test-cli test-law audit
```

  Note `test-modules` is absent. Its recipe exists at `justfile:124-125`:

```make
test-modules:
    bash tools/test-modules.sh
```

- The battery scripts: `tools/test-{annotate,check-json,cli,fmt,law,lint,modules,query,repl,rewrite}.sh` plus `tools/check-examples.sh`. Each begins `set -euo pipefail`, cds to the repo root, and (pattern from `check-examples.sh`) rebuilds the binary before running:

```bash
bang=".lake/build/bin/bang"
echo "building bang runner…" >&2
lake build bang >&2
```

- The pre-commit hook (`.git/hooks/pre-commit`, source `tools/` install via `tools/install-hooks.sh`): fast fitness checks always run; `nix develop --command just verify` runs iff `.lean` files are staged (hook lines 104-126). `BANGLANG_SKIP_VERIFY_REASON` is the manual skip.
- Repo bash conventions that BIND this plan (from the repo's own hard-won rules — violating them creates exactly the false-greens this gate exists to prevent):
  - Under `pipefail`, an unguarded `$(a | b)` command substitution dies silently → false-green. Guard every capture and assert expected check-counts.
  - Never gate on a piped exit code (`cmd | grep | head` returns `head`'s status). Use unpiped exits or `${PIPESTATUS[0]}`.
  - Scripts carry a `# tool:` frontmatter line (role/couples/runs-in) — see the first lines of any `tools/*.sh`.

## Commands you will need

| Purpose | Command | Expected on success |
|---|---|---|
| Enter dev shell | `nix develop` | banner |
| Time the current gate (baseline) | `nix develop --command bash -c 'time just verify'` | exit 0 + wall time |
| Run one battery | `nix develop --command just test-modules` | its pass summary, exit 0 |
| Shellcheck a new script | `nix shell nixpkgs#shellcheck -c shellcheck tools/run-batteries.sh` | no errors |
| Full gate | `nix develop --command just verify` | exit 0 |

## Scope

**In scope**:
- `justfile` — the `verify` recipe line and a new `run-batteries` recipe.
- `tools/run-batteries.sh` (create).
- `tools/README.md` — the `test-modules.sh` row's `runs-in` column, and a row for the new script.
- `plans/README.md` (status row).

**Out of scope** (do NOT touch):
- The individual `test-*.sh` scripts' test LOGIC. (Removing their redundant per-script `lake build bang` line is allowed ONLY via the env-var mechanism in Step 3 — no other edits.)
- `.git/hooks/pre-commit` / `tools/install-hooks.sh` — the hook calls `just verify` and inherits the speedup automatically. An automatic "comment-only `.lean` diff skips verify" fast-path was considered and REJECTED during planning: comment-only detection in Lean diffs is fragile (doc-strings feed diagnostics that `#guard`s assert on), and the manual `BANGLANG_SKIP_VERIFY_REASON` escape already exists. Do not implement it.
- `flake.nix`, CI workflow files.
- Any `.lean` file.

## Steps

### Step 1: Baseline + test-modules wiring

1. Record the baseline: `nix develop --command bash -c 'time just verify'` → note wall time (expect minutes).
2. Time `nix develop --command bash -c 'time just test-modules'` alone. If it completes in under ~60s with exit 0, add `test-modules` to the `verify` leg list in `justfile:28` (alphabetical position among the other `test-*` legs is fine) and update `tools/README.md:70`'s runs-in from `manual` to `verify`. If it takes longer or fails, STOP (see conditions).

**Verify**: `nix develop --command just verify` → exit 0, and its output now includes `test-modules`' pass summary.

### Step 2: Create `tools/run-batteries.sh`

A driver that runs the independent batteries concurrently. Requirements:

- Frontmatter first line: `# tool: role=test couples=justfile,tools/test-*.sh runs-in=verify`.
- `set -euo pipefail`; `cd "$(git rev-parse --show-toplevel)"`.
- Build ONCE up front: `lake build bang >&2` (same idiom as `check-examples.sh`), then `export BANG_BIN_FRESH=1` (consumed in Step 3).
- Launch each battery as a background job writing its full output to its own temp file (`mktemp -d` at start); collect PIDs in an array. Battery list is EXPLICIT in the script (not a glob) so a new script must be consciously enrolled:

```bash
batteries=(check-examples test-repl test-fmt test-check-json test-query \
           test-rewrite test-annotate test-lint test-cli test-law test-modules)
```

- `wait` on each PID INDIVIDUALLY, capturing each exit status (a bare `wait` loses statuses). Print each battery's buffered output sequentially after all finish (no interleaving), prefixed `── <name> ──`.
- **Count assertion (false-green defense)**: after the loop, assert the number of collected statuses equals `${#batteries[@]}`; exit 1 with a loud message otherwise.
- Exit nonzero if ANY battery failed, listing the failures by name.

**Verify**: `nix shell nixpkgs#shellcheck -c shellcheck tools/run-batteries.sh` → clean. Then `nix develop --command bash tools/run-batteries.sh` → all batteries pass, per-battery output visible, exit 0. Break one battery deliberately (e.g. `BANG_FORCE_FAIL=1` — or temporarily corrupt one fixture, then restore it) and confirm the driver exits nonzero naming it — **a gate change must be tested red, not just green**. Restore before proceeding; `git status --porcelain` must show only in-scope files.

### Step 3: Skip redundant per-script rebuilds

In each battery script, the existing `lake build bang >&2` line becomes conditional — replace it (and only it) with:

```bash
if [ -z "${BANG_BIN_FRESH:-}" ]; then
  echo "building bang runner…" >&2
  lake build bang >&2
fi
```

Standalone invocation (`just test-fmt`) still rebuilds; under the driver the single up-front build is reused. This also removes the race of 11 concurrent `lake build` invocations (see STOP conditions).

**Verify**: `nix develop --command just test-fmt` alone still passes (rebuild path). `nix develop --command bash tools/run-batteries.sh` passes (skip path).

### Step 4: Rewire `verify` and measure

Change `justfile:28` to:

```make
verify: selfcheck build run-batteries audit
```

with a new recipe:

```make
# All independent test batteries, concurrently (single up-front binary build).
run-batteries:
    bash tools/run-batteries.sh
```

Keep the individual `test-*` recipes untouched (developers use them singly).

**Verify**: `nix develop --command bash -c 'time just verify'` → exit 0; wall time strictly below the Step-1 baseline (record both numbers in the commit message). Then make a trivial whitespace commit touching a `.lean` file comment to confirm the pre-commit hook path runs the new gate end-to-end (then `git reset` if you don't want to keep it — or fold it into this plan's commit).

## Test plan

- The red-path test in Step 2 (driver exits nonzero on a failing battery) is the critical test — a parallel driver that swallows failures is worse than the serial gate.
- Both invocation modes of each battery verified: standalone (`just test-X`) and driven.
- Baseline vs. final timing recorded in the commit message.

## Done criteria

- [ ] `test-modules` runs inside `just verify` (or a STOP report explains why not)
- [ ] `tools/run-batteries.sh` exists, shellcheck-clean, with individual `wait` statuses + count assertion
- [ ] Red-path verified: one deliberately failing battery → driver exit nonzero naming it (then restored)
- [ ] `nix develop --command just verify` exits 0 and is measurably faster than baseline
- [ ] Standalone `just test-fmt` (any single battery) still passes
- [ ] No files outside the in-scope list modified (`git status --porcelain`)
- [ ] `plans/README.md` status row updated

## STOP conditions

Stop and report back (do not improvise) if:

- `test-modules` FAILS at Step 1 — the manual-only status may have been hiding a red gate; that's a finding, report the failure output. Do not wire a red leg into `verify`.
- `test-modules` takes >60s — report the timing; wiring it in needs an operator call on gate-time budget.
- Any battery behaves differently under the driver than standalone (fixture collisions, shared temp paths, stdout-dependence) — report which script and the difference; do NOT patch its logic.
- Concurrent batteries corrupt `.lake/` state (build errors mentioning locks or truncated oleans) — the single-up-front-build design should prevent this; if it appears anyway, report rather than adding retries.
- The parallel gate is NOT faster than baseline — the serialization assumption was wrong; report the timings and revert the `verify` line (keep Step 1's test-modules wiring).

## Maintenance notes

- New test batteries must be enrolled in `tools/run-batteries.sh`'s explicit `batteries` array — adding only a justfile recipe silently leaves them out of the gate (this is the same class of gap as the `test-modules` finding that motivated Step 1). A reviewer checking a new `tools/test-*.sh` should demand the array entry.
- If a future battery genuinely can't run concurrently (e.g. it mutates a shared fixture), give it a `# tool: … concurrency=exclusive` marker and run it after the `wait` in the driver — don't quietly reorder the array.
- Deferred out of this plan: CI-side parallelization (the GitHub workflow calls `just verify` and inherits this), and the rejected pre-commit comment-only fast-path (see Scope).
