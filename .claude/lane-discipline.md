# Lane discipline — the standing rules for IC lanes

> Extracted 2026-07-09 from a day of briefs that each restated this block (SSoT move: briefs
> now CITE this doc and add only unit-specific scope). Every rule below was load-bearing in a
> real incident; none is ceremony. The manager's briefs may tighten these per-unit, never
> loosen them.

<!-- BEGIN PACK lane-discipline (the injectable core — tools/gen-agent-pack.py splices this
     verbatim into each .claude/agents/*.md; keep it terse, it rides into every subagent) -->
**Lane-discipline pack** (the non-negotiables, injected into every subagent):

- **Build**: `bash tools/seed-lake.sh` before your FIRST build in a linked worktree — never
  `lake exe cache get` in any form (the seeded `.lake` is your olean source; missing oleans →
  report, don't fetch). All `lake`/`just`/`node` run inside `nix develop`.
- **Commit**: by PATHSPEC (`git commit <path>`), never `-A`/bare — a bare commit on a shared
  tree sweeps another lane's staged hunks into yours. Push nothing to `main`; the MANAGER lands.
- **Gate-traps** (cause false-greens): read Lean errors via `lake build` exit code or
  `grep -E "error"` (plain `grep "error:"` MISSES `error(lean.unknownIdentifier):`); gate
  sorries via `#print axioms`/`just axioms`, NEVER `grep sorry`. Gate the COMMITTED sha on a
  clean tree, never a summary or a dirty worktree.
- **Reserved words** (not identifiers): `get put raise new read write resume with`.
- **Ghost-signature commit failure → STOP and report** (do not retry, do not `--no-verify`
  around it).
- **Report, never idle silently**: end every turn with a pushed slice or a one-line status;
  a wall outside your brief → STOP-and-SHOW (the obligation, options, your recommendation).
<!-- END PACK lane-discipline -->

## Setup & writing

- Work ONLY in your assigned full clone (`tools/new-worktree.sh` clone mode — own git store).
  `nix develop` for all lake/just. NEVER `lake exe cache get`, in any form (the seeded
  `.lake/packages` is your olean source; missing oleans → report, don't fetch).
- **One writer per file.** Your brief names your files; another lane's files are read-only.
  Needing an export from a file you don't own → implement against what IS public and REPORT
  the exact missing signature (the manager lands one-line `public` markers, or grants a
  surgical markers-only commit).
- Commit by PATHSPEC, never `-A`. Push every green slice to your origin branch — pushed WIP
  is the safety net; unpushed work dies with sessions.
- **Verify sole-writer before your first edit**: clean tree, HEAD == the brief's base sha ==
  origin; note a key file's md5, wait 60s, re-check. Movement → STOP and report.

## Gates & evidence

- `lake build` EXIT 0, unpiped, per slice. Sorries gate via `#print axioms`/`just axioms` on
  force-rebuilt oleans — NEVER grep-for-sorry. Kernel census untouchable unless your brief
  says otherwise; `check-primitives.sh` = 26 ctors.
- **Falsify every new guard/test**: break the mechanism (stash-revert, flipped expected,
  broken comparator), confirm the failure names the right thing AND the run reaches
  completion (a truncated test run reads as green — guard `$(cmd|cmd)` captures under
  pipefail; assert the final check count).
- Gate claims on the CLEAN COMMITTED sha, timestamped, re-verified within a minute of
  reporting. The manager re-gates on a fresh clone; your evidence is the first gate, not
  the last.
- Pipe long command output to files and read/grep those — never `| tail`/`| head` an
  expensive run's output away.

## Documentation responsibility (who writes what)

- **You write point-of-WORK truth**: inline doc-comments at definition sites (entry gates,
  deferral notes, invariant framings — to the shape the brief specifies), design/findings
  notes, commit messages carrying your evidence, issue findings-comments.
- **You never write point-of-DECISION truth**: ADR statuses/amendments, CONTEXT.md's lead,
  PATH banked-item ledgers, issue lifecycle (close/re-scope), loop-audit — manager-only.
  Flag what belongs there; don't write it.
- **Product docs ride the feature slice**: if your change alters user-visible behavior
  (syntax, CLI, errors), the corresponding product doc/example/reference change lands IN THE
  SAME SLICE, gated — docs-after-code is how references rot.
- **Generated files** (CHANGELOG, core-overview, notes/README, llms.txt, …): regen only what
  YOUR branch's fitness requires to stay green, in SEPARATE clearly-labeled commits (never
  mixed with content) — the manager drops/replaces them at landing, where all derived docs
  regenerate once against main.

## Communication (the durable-channel protocol)

- **Rulings live on your TASK's description** (TaskGet it) — inboxes drop and reorder
  messages; the board re-delivers. Waiting on a ruling → check the task first, then ask.
- Timestamp claims; report per pushed slice (one line is fine mid-grind); NEVER end a turn
  without a pushed slice or a one-line status. Received an instruction that seems stale or
  contradicts a newer one? Say so — don't silently execute the older.
- STOP-and-SHOW within ~30min of a wall outside your brief's characterization: the exact
  obligation, the options you see, your recommendation. A refutation or a
  premise-that-won't-hold is a first-class deliverable.

## Handoff (the atomic protocol)

- A lane transfer is a transaction: (1) all outstanding instructions settled, (2) the
  predecessor sends the LITERAL phrase "RELEASED — will not touch the tree again", (3) only
  then does a successor exist, with the base sha pinned in its founding brief and a
  base-moved resync procedure.
- Self-monitored stop criterion on long grinds: continue while region-commits land clean;
  on CHURN (re-doing a region, thrashing), stop AT A REGION BOUNDARY, push, update the PATH
  resume-point to the exact next step, send the release phrase.
- Atomic re-threads may push RED WIP (label it, use the sanctioned skip-verify reason);
  atomicity governs what may LAND, not what may reach origin. Never end a session on an
  unpushed red spine.

## Landing-flow gates (manager-side — added 2026-07-10 after the lettMulti false-green)

- **Landing builds run VISIBLE and rc-checked.** Never `just build > /dev/null` inside an
  rc-summarized chain at a landing — the lettMulti missing-cases break rode exactly that
  pattern onto main. Pipe to a file, grep it, check the exit.
- **Background scripts must PROPAGATE the commit's rc** — a trailing `echo`/`tail` launders
  a failed commit into a green task exit (`set -e` or explicit `exit $rc`).
- **Watch every landing push's CI run to its VERDICT.** CI is the backstop that catches
  what local flows mask (it caught lettMulti); a push without a watched verdict is an
  unverified claim. `gh run watch <id> --exit-status`.
- **Cross-branch constructor skew is a landing hazard**: a lane's exhaustive matches over a
  type that gained constructors on main AFTER its clone was cut will pick cleanly as text
  and break only at recompile. At landing, any pick touching files that match over
  Surf/Comp/Val/Handler gets its build re-verified — the gate clone of the LANE's branch
  cannot see this class.
