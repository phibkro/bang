# Plan 008: Sanitize git environment in the pre-commit hook's nix/lake invocations — kill the index-corruption vector

> **Executor instructions**: Follow this plan step by step. Run every
> verification command and confirm the expected result before moving to the
> next step. If anything in the "STOP conditions" section occurs, stop and
> report — do not improvise. When done, update the status row for this plan
> in `plans/README.md` — unless a reviewer dispatched you and told you they
> maintain the index.
>
> **Drift check (run first)**: `git log --oneline -1 -- tools/git-hooks/pre-commit`
> then compare the excerpts below against the live file. This plan was written
> against the post-merge main of 2026-07-10; the hook's section numbers (§3b,
> §4, §5) are the anchors, not line numbers.

## Status

- **Priority**: P1 (it protects every future commit in every worktree)
- **Effort**: S
- **Risk**: LOW-MED (touches the gate hook; the pathspec-commit subtlety below is the one way to get it wrong)
- **Depends on**: none
- **Category**: bug
- **Planned at**: post-merge main, 2026-07-10

## Why this matters

Eleven documented incidents of worktree-index corruption on this repo (the `.devcontainer/Dockerfile` "ghost", ~8950 phantom index entries, `Error building trees` at commit time) trace to one mechanism, captured live on 2026-07-10: **`git commit` exports `GIT_INDEX_FILE` (and can export `GIT_DIR`) into the pre-commit hook's environment. The hook runs `nix develop --command just verify` → `lake` → git operations inside `.lake/packages/mathlib`. Those inner git invocations inherit `GIT_INDEX_FILE` — an absolute path to the committing worktree's index — and write MATHLIB's tree through it, over the bang worktree's index.** The ~8950 entries are mathlib's file count; `.devcontainer/Dockerfile` is a mathlib file.

The fix: the hook's nix/lake invocations must run with the git-context variables removed, so any git operation lake performs in another repo resolves its own context instead of inheriting ours.

## Current state

- `tools/git-hooks/pre-commit` — the hook SOURCE. `.git/hooks/pre-commit` is the installed copy (via `tools/install-hooks.sh`); Step 1 determines whether it's a symlink (edit propagates automatically) or a copy (needs reinstall).
- The hook has THREE invocations that reach nix/lake (section anchors and verbatim current lines):
  - **§3b** (changelog auto-regen): `nix develop --command just changelog > /dev/null 2>&1 || true`
  - **§4** (fitness): `if ! nix develop --command just fitness > /tmp/bang-fitness.log 2>&1; then`
  - **§5** (verify): `if ! nix develop --command just verify > /tmp/bang-precommit.log 2>&1; then`
- The hook's OWN git commands (`git diff --cached --name-only …` etc.) must be left untouched — see the constraint below.

### The load-bearing constraint — do NOT global-unset

This repo commits by **pathspec** (`git commit <path> -m …`) as standing discipline. For a pathspec commit, git builds a **temporary index** and points `GIT_INDEX_FILE` at it; the hook's `git diff --cached` reads that temp index to see what is *actually* being committed. A global `unset GIT_INDEX_FILE` at the top of the hook would make the hook's own checks read the WRONG staged set (the real index instead of the temp one) — admit/axiom/statement checks would run against files that aren't in the commit and miss files that are.

Therefore: sanitize **only the three nix invocations**, via `env -u`, leaving the hook's own environment intact.

## Commands you will need

| Purpose | Command | Expected on success |
|---|---|---|
| Enter dev shell | `nix develop` | banner |
| Shellcheck the hook | `nix shell nixpkgs#shellcheck -c shellcheck tools/git-hooks/pre-commit` | no new errors vs pre-edit baseline |
| Exercise the hook end-to-end | a real pathspec commit (Step 3) | hook output, commit lands |

## Scope

**In scope**:
- `tools/git-hooks/pre-commit` — the three `env -u` wrappers only.
- `.git/hooks/pre-commit` — ONLY IF Step 1 shows it's a copy, and ONLY by re-running `bash tools/install-hooks.sh` (never hand-edit the installed copy).
- `plans/README.md` (status row — skip if the reviewer maintains the index).

**Out of scope**:
- Any other hook logic (the admit/axiom/statement checks, the skip mechanism, the fitness/verify decision tree stay byte-identical).
- `tools/install-hooks.sh`, `justfile`, any `.lean` file, lake configuration.
- Do NOT add a global `unset` (see the constraint above).

## Git workflow

- Branch: `advisor/008-hook-env-sanitization`. Conventional commit, e.g. `fix(hooks): sanitize GIT_INDEX_FILE/GIT_DIR from the hook's nix invocations — the worktree index-corruption vector (plan 008)`.
- Do NOT push.

## Steps

### Step 1: Determine the install mode

`ls -la .git/hooks/pre-commit` — symlink into `tools/git-hooks/` means source edits are live immediately; a regular file means Step 4 must reinstall. Also record `diff tools/git-hooks/pre-commit .git/hooks/pre-commit` — if they already differ, STOP (drift between source and installed copy is a separate problem; report it).

**Verify**: you know the mode and the two files are currently identical (or symlinked).

### Step 2: Apply the three wrappers

In `tools/git-hooks/pre-commit`, change exactly three lines:

§3b: `nix develop --command just changelog > /dev/null 2>&1 || true`
→ `env -u GIT_INDEX_FILE -u GIT_DIR -u GIT_WORK_TREE nix develop --command just changelog > /dev/null 2>&1 || true`

§4: `if ! nix develop --command just fitness > /tmp/bang-fitness.log 2>&1; then`
→ `if ! env -u GIT_INDEX_FILE -u GIT_DIR -u GIT_WORK_TREE nix develop --command just fitness > /tmp/bang-fitness.log 2>&1; then`

§5: `if ! nix develop --command just verify > /tmp/bang-precommit.log 2>&1; then`
→ `if ! env -u GIT_INDEX_FILE -u GIT_DIR -u GIT_WORK_TREE nix develop --command just verify > /tmp/bang-precommit.log 2>&1; then`

Add one comment block above §3b explaining WHY (2–4 lines): git exports GIT_INDEX_FILE to hooks; lake's git ops in `.lake/packages/*` must not inherit our index path (the 11-incident `.devcontainer` ghost, plan 008); hook-own git commands intentionally keep the env for pathspec-commit temp indices.

**Verify**: `grep -c "env -u GIT_INDEX_FILE" tools/git-hooks/pre-commit` → `3`. Shellcheck: no new findings vs the baseline you took in Step 1.

### Step 3: Exercise the hook — both commit shapes

1. **Docs pathspec commit (temp-index shape)**: make a trivial whitespace-only edit to this plan file (`plans/008-hook-env-sanitization.md` is in your worktree — if `plans/` doesn't exist in the worktree, use any tracked `.md` and revert after). `git commit <that-file> -m "test: hook exercise (will be dropped)"`. The hook must run fitness and *correctly skip verify* (no `.lean` staged) — confirming the staged-set detection still reads the temp index.
2. Note the §3b changelog step still works (its output line appears, no error).
3. `git reset --soft HEAD~1` to drop the test commit if it was a throwaway (keep the tree state you want to commit for real).

**Verify**: the test commit's hook output shows `passed (no .lean changes; skipping the verify build)` — proving staged-set detection is intact under a pathspec commit.

### Step 4: Install + commit

If Step 1 said "copy": `bash tools/install-hooks.sh` and re-diff source vs installed (must be identical). Commit the source change by pathspec.

**Verify**: `diff tools/git-hooks/pre-commit .git/hooks/pre-commit` → empty (or symlink). Final commit present on the branch with only the in-scope file(s).

## Test plan

Step 3 IS the test: one pathspec commit exercising the temp-index path with the sanitized hook, confirming (a) hook-own git checks still see the right staged set, (b) the nix steps run clean without the git context.

## Done criteria

- [ ] Exactly 3 `env -u GIT_INDEX_FILE -u GIT_DIR -u GIT_WORK_TREE nix develop` occurrences in the hook source
- [ ] No global `unset` of git vars anywhere in the hook
- [ ] Hook-exercise commit showed correct staged-set detection (fitness ran, verify correctly skipped for a docs-only pathspec commit)
- [ ] Installed copy identical to source (or symlinked)
- [ ] Only in-scope files in the final commit

## STOP conditions

- Source and installed hook ALREADY differ at Step 1 — report the diff, don't reconcile unilaterally.
- The Step-3 exercise shows the hook mis-detecting the staged set (e.g. verify runs for a docs-only commit, or the admit-check scans unstaged files) — the env interaction is different than this plan assumed; report exactly what the hook printed.
- Your own commit fails with the `.devcontainer` / `Error building trees` signature — that's the very vector this plan fixes, striking before the fix protects you. Do NOT retry with `--no-verify` more than once; report and let the reviewer land via plumbing.

## Maintenance notes

- Any FUTURE hook step that shells into nix/lake/another-repo-git must get the same `env -u` wrapper — reviewers should demand it on hook PRs (that's the durable lesson of the 11 incidents).
- If this fix holds, the historical mitigations (gc.pruneExpire=never, worktree bans for writers) become belt-and-suspenders rather than load-bearing; do not remove them until several corruption-free weeks confirm the vector is dead.
