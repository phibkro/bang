# Plan 012: Tooling-stratum governance — invocation telemetry, runs-in validation, deprecation, convention injection

> **Executor instructions**: Follow this plan step by step; run every verification
> command. STOP conditions binding. The reviewer maintains the index. Reply in the
> standard report format (STATUS / STEPS / FILES CHANGED / NOTES).
>
> **Drift check (run first)**: `git log --oneline -2 -- tools/gen-tools-index.py .claude/agents/ .claude/lane-discipline.md`
> and compare "Current state" below against the live tree.

## Status

- **Priority**: P2
- **Effort**: M (four slices, each independently bankable)
- **Risk**: LOW (additive telemetry + checks + generated blocks; one behavioral change: every tool logs a line)
- **Depends on**: none (collision note: `tools/gen-tools-index.py` and the batteries scripts are
  touched by no in-flight lane; `justfile` appends at the END as usual)
- **Category**: dx / governance
- **Planned at**: main @ `de681fc9`, 2026-07-10 (operator-commissioned: the tooling-overview conversation)

## Why this matters

The tooling stratum (Lean exes/witnesses · python gens/checks · bash batteries/gates · the Node
selfcheck) is inventoried on the generate rung (the tools README is generated from `# tool:`
frontmatter and fitness-gated) but has three governance gaps, each demonstrated by a real incident:
(1) **`runs-in=` claims aren't validated** — a script claimed `runs-in=verify` for weeks while wired
to nothing (found by reading, fixed in plan 009's lane); (2) **no usage data** — deprecation
candidates are guesswork because nothing records invocations; (3) **conventions reach agents
nondeterministically** — lane briefs hand-copy rules that `.claude/lane-discipline.md` already
holds, and `.claude/agents/*.md` role files don't carry them at all. This plan closes all three
with the repo's own moves: telemetry → generated columns → fitness legs → injected packs.

## Current state

- `tools/gen-tools-index.py` — generates the tools README from each script's `# tool:` frontmatter
  line (`role=`, `couples=`, `runs-in=`). The fitness gate (`just tools-index --check` leg or
  equivalent — read the justfile) fails on staleness.
- `tools/run-batteries.sh` — the gate driver; its explicit `batteries=(…)` array is the ENROLLMENT
  point for `runs-in=verify` test batteries.
- `.claude/lane-discipline.md` — the standing IC rules (committed 2026-07-09, extracted from
  dispatch briefs). `.claude/agents/{kernel,proof,compiler,surface}-engineer.md` +
  `lean-proof-auditor.md` — the subagent system prompts (frontmatter + body).
- `justfile` — recipes append at the very end; the `verify:` line is out of scope.
- Repo bash rules: `set -euo pipefail`; no unguarded `$(a | b)` captures; scripts carry the
  `# tool:` frontmatter; `python3 tools/gen-tools-index.py` regenerates after frontmatter changes.

## Scope

**In scope**: `tools/gen-tools-index.py` + the generated tools README; a new tiny logging helper
under `tools/` (create); ONE added line near the top of each `tools/*.sh` (the telemetry call) and
the equivalent one-liner in the python entry points; a new fitness check script under `tools/`
(create) + its justfile recipe + enrollment in the `fitness` chain (read how the existing fitness
legs are chained — follow that pattern, NOT the verify line); `.claude/agents/*.md` (the injection
blocks); `.claude/lane-discipline.md` (consolidation edits); `.gitignore` (the log file).
**Out of scope**: the `verify:` recipe line; any `.lean` file; deleting any tool (deprecation
CANDIDATES are this plan's output, deletions are operator calls); the pre-commit hook.

## Steps

### Slice 1: invocation telemetry (the operator's ask — "even just appending to a log file on exec")

A helper (suggest a two-line sourceable snippet or a function in a new small script under `tools/`)
that appends `<ISO-timestamp> <script-basename>` to a repo-local log at the path
`.claude/tool-invocations.log` (gitignore it — telemetry is per-machine data, not repo content).
MUST be failure-proof: the append is `|| true`-guarded and writes nothing outside the repo; a
read-only checkout must not break tools. Add the call as ONE line immediately after the frontmatter
in every `tools/*.sh`, and a mirrored one-liner (guarded `try`) at the entry of the python tools'
`main()`. Lean exes: SKIP (their invocations go through just recipes — cover them by adding the
log line to the wrapping recipes instead, e.g. `pole`, `lint-lean`).
**Verify**: run three different tools; the log gains three correctly-formatted lines; `just verify`
exit 0 (the telemetry must not change any gate's output or exit codes — diff a battery's output
before/after).

### Slice 2: runs-in validation (drift → unrepresentable)

New check script (follow an existing fitness leg's shape): (a) every script whose frontmatter says
`runs-in=verify` is reachable from the gate — present in `run-batteries.sh`'s `batteries` array OR
invoked by a recipe in the `verify` dependency chain (parse the justfile); (b) every `batteries`
array entry has a matching script with `runs-in=verify`; (c) every `runs-in=hook` script is
referenced by the pre-commit hook source. Wire it as a fitness leg.
**Verify**: the leg passes on the current tree; then TEST IT RED — temporarily flip one script's
`runs-in` to a lie, confirm the leg fails naming it, restore. (A gate change must be tested red.)

### Slice 3: last-invoked + status columns (deprecation candidates from data)

Extend `gen-tools-index.py`: a `status=` frontmatter field (default `active`; `deprecated` allowed)
and, when the telemetry log exists, a "last invoked" column rendered from it (absent log → column
shows `n/a`; the README must be deterministic for CI, so the column is included ONLY when the
generator is run with an explicit flag — default output stays log-independent to keep the
fitness `--check` stable). Add a `deprecated`-status rule to the slice-2 checker: a deprecated
tool may not appear in any gate chain. Do NOT mark anything deprecated in this plan.
**Verify**: regen is byte-stable across two runs without the flag; with the flag, the column
renders from your slice-1 log entries.

### Slice 4: convention injection into the agent role files

Goal: the standing rules reach subagents DETERMINISTICALLY instead of by hoping they read docs.
First, EMPIRICALLY test whether `.claude/agents/*.md` bodies support dynamic file inclusion (the
operator suggests `$`-style injection; also try the `@path` reference form slash-commands support):
create a scratch agent file with the candidate syntax, and determine — via Claude Code docs
(`claude --help`, the docs site via WebFetch if available) or by inspection of how the role files
are consumed — whether the content is expanded at spawn time. **If native injection works**: add
one line to each role file injecting `.claude/lane-discipline.md`. **If it does NOT** (likely):
fall back to the repo's generate rung — a marked generated block (`<!-- BEGIN GENERATED
lane-discipline -->…<!-- END -->`) spliced into each `.claude/agents/*.md` by a small generator
(extend `gen-tools-index.py` or a sibling script), with a fitness staleness check like the other
generated derivations. Either way: consolidate into `.claude/lane-discipline.md` the rules current
briefs hand-copy (seed-lake before first build · never cache-get · pathspec commits · reserved
words `get put raise new read write resume with` · gate-traps: unpiped exits, axioms-not-grep ·
ghost-signature → stop · push nothing, the manager lands · full report, never idle silently).
**Verify**: state which mechanism landed (native vs generated) with the evidence; the role files
carry the pack; `just fitness` exit 0 (including your new staleness leg if the generated route).

## Done criteria

- [ ] Telemetry: 3+ logged invocations shown; gates' outputs unchanged; log gitignored
- [ ] runs-in leg: green on the tree AND demonstrated red on a planted lie (then restored)
- [ ] Index: `status=` supported; default regen byte-stable; flagged regen renders last-invoked
- [ ] Role files carry the lane-discipline pack (mechanism named + evidenced)
- [ ] `just verify` + `just fitness` exit 0 on the final committed sha

## STOP conditions

- The telemetry line changes any battery's stdout/exit (the diff test) — report, don't ship.
- The justfile-chain parse for slice 2 turns fragile (recipes too dynamic to parse reliably) —
  report the parsing wall; a conservative subset check (batteries array + hook only) is an
  acceptable fallback, SAY SO.
- Agent-file injection: if NEITHER native nor generated splice can work without breaking how the
  harness consumes the role files, report the finding — do not restructure the agents dir.
- Anything requires touching the `verify:` line, a `.lean` file, or deleting a tool.

## Maintenance notes

- Follow-ups this enables (operator calls): first data-driven deprecation sweep after ~a week of
  telemetry; a "stratum map" section (layer × language × lifecycle) in the codebase-maintenance
  doc once the status/last-invoked columns exist to derive it from.
- New tools inherit the governance automatically ONLY if they carry the telemetry line + frontmatter
  — the slice-2 checker should flag a `tools/*.sh` missing either (add that as a sub-check if cheap).
