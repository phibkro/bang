# Plan 011: Public-early plumbing — release battery, site CI, flake-check + shake riders

> **Executor instructions**: Follow this plan step by step. Run every verification
> command and confirm the expected result before moving on. If a STOP condition
> occurs, stop and report — do not improvise. The reviewer maintains the index.
>
> **Drift check (run first)**: `git log --oneline -2 -- justfile .github/ site/ flake.nix`
> and compare "Current state" below against the live tree.

## Status

- **Priority**: P2
- **Effort**: M (four small items, one lane)
- **Risk**: LOW-MED (item 1 automates an OUTWARD action — the plan builds the machinery but publishes NOTHING; see the hard rule)
- **Depends on**: none (justfile items append at the END; a parallel lane W6 also appends recipes — trivial merge)
- **Category**: dx / release
- **Planned at**: main @ `d65bd0ed`, 2026-07-10

## Why this matters

The ROADMAP's public-early policy (adopted 2026-07-10) makes a public v0.x tag + post a
per-checkpoint obligation starting at ◊5.25 — weeks away. Today releasing is manual (v0.1.0 was
hand-rolled) and the vocs site (`site/`) builds only on someone's machine. This plan builds the
release battery and puts the site under CI so the policy costs one command per checkpoint, plus
two one-recipe riders (flake-check parity, shake) from the tooling survey.

**HARD RULE for this plan: publish NOTHING.** No tag pushes, no `gh release create` against the
real repo, no Pages deployment. The deliverable is machinery, exercised in dry/local form only.

## Current state

- `CHANGELOG.md` is GENERATED from conventional commits (`just changelog`, `tools/gen-changelog.py`)
  with version sections; the hook keeps it current. Release notes are therefore an EXTRACTION.
- Existing release: tag `v0.1.0` exists (created manually). `gh` CLI is authenticated; repo
  `github.com/phibkro/bang`.
- `site/` — vocs docs site: `package.json` (vocs/waku/vite, `^` ranges), tracked `bun.lock`,
  `sync-docs.mjs` (read it — it syncs repo docs into the site), `vocs.config.ts`. No CI builds it.
  KNOWN GOTCHA (from the sibling TS project's memory, verify if it applies here): mermaid is
  pre-rendered to static SVG and mermaid-cli needs chromium in CI — check whether `sync-docs.mjs`
  or the build invokes `mmdc`; if it does, the CI job needs a chromium step or must skip
  re-rendering (prefer: committed SVGs are the artifacts, CI only builds the site around them).
- `.github/workflows/verify.yml` — the existing CI (the Lean gate). Add a SEPARATE workflow for
  the site; do not touch verify.yml.
- `flake.nix` — the dev shell. Issue #63 landed a pure-nix FOD build for the Lean exe (see the
  repo's nix packaging work) — the FULL verify-as-flake-check is heavier than this plan (network
  sandbox vs `lake exe cache get`); the rider here is the CHEAP static check only.
- `justfile` — recipes append at the very END (after plan 004/007 additions). The `verify:` line
  is out of scope.

## Scope

**In scope**: `justfile` (recipes: `release`, `shake`), a new `release.sh` under `tools/`
(create), a new `site.yml` workflow under `.github/workflows/` (create), `flake.nix` (one
`checks` attribute), `site/` ONLY if the CI job needs a script tweak to run headless (prefer not).
**Out of scope**: `verify.yml`; the `verify:` recipe line; any `.lean`; any actual publishing
(tags on origin, GitHub releases, Pages); `site/` content/design.

## Steps

### Step 1: The release battery

Create `release.sh` in `tools/` (frontmatter `# tool: role=release couples=CHANGELOG.md,justfile runs-in=manual`):
takes `vX.Y.Z`; asserts clean tree + on `main` + `just verify` green (or accepts a
`--skip-verify` flag with a loud warning); extracts the version's section from `CHANGELOG.md`
(the section for the NEW tag = everything since the previous tag — derive from the changelog
structure after reading `tools/gen-changelog.py` to learn the exact section format); creates an
ANNOTATED local tag with the notes; prints the exact `git push origin vX.Y.Z` +
`gh release create vX.Y.Z --notes-file …` commands WITHOUT running them (the operator's finger
stays on the publish button). Recipe: `release VERSION: bash tools/release.sh {{VERSION}}`.
**Verify**: run against a throwaway version (`v0.0.0-test`): tag created locally with the right
notes body (`git tag -l --format='%(contents)' v0.0.0-test`), publish commands printed not run,
then `git tag -d v0.0.0-test`. Shellcheck clean. Confirm `git ls-remote --tags origin` shows NO
new tag.

### Step 2: Site CI (build-only)

Create the workflow `site.yml` under `.github/workflows/`: on PRs/pushes touching `site/**` or `docs/**`; steps: checkout,
setup bun (`oven-sh/setup-bun`), `bun install --frozen-lockfile` in `site/`, run the sync script
if the build needs it, `bun run build` (read `site/package.json` scripts for the real name).
Handle the mermaid/chromium question per Current-state (prefer committed-SVG passthrough).
**Verify**: you cannot run Actions locally — validate the workflow with
`nix shell nixpkgs#actionlint -c actionlint .github/workflows/site.yml` (clean) AND prove the
build path works by running the same commands locally: `cd site && bun install --frozen-lockfile
&& bun run build` → exit 0, `dist/` (or the build output dir) produced. If bun is not on PATH,
`nix shell nixpkgs#bun -c …`.

### Step 3: Riders

1. `flake.nix` checks attribute: `checks.<system>.static` running the NO-NETWORK static legs
   (the Node selfcheck + the pure-python fitness scripts — inspect `justfile`'s `selfcheck` and
   `fitness` to pick the legs that need no lake/network; wrap as a derivation). `nix flake check`
   must pass. Do NOT attempt verify-as-flake-check (network wall; note it as the #63-FOD
   follow-up in the recipe comment).
2. `justfile` recipe `shake`: `lake exe shake -- <the 19 root modules — copy the list from the
   lint-lean recipe>` in report mode with a comment (advisory; 26 files had removable imports at
   the last run). NO `--fix`.
**Verify**: `nix flake check` exit 0; `nix develop --command just shake` produces the report,
exit code noted (shake exits nonzero when findings exist — the recipe should tolerate/report,
not mask; `|| true` with a printed count is acceptable ONLY if the count is asserted non-empty
output).

### Step 4: Gate + commit

`just verify` exit 0 (nothing in the gate should have changed); `just fitness` exit 0 (the new
tools script needs its `# tool:` frontmatter for the tools-index regen — run
`python3 tools/gen-tools-index.py` if the fitness leg demands it). Commit by pathspec on branch
`feat-public-plumbing-011`. Do NOT push.

## Done criteria

- [ ] `just release v0.0.0-test` produced a correct local annotated tag + printed (not ran) publish commands; tag deleted; origin tag-list unchanged
- [ ] `actionlint` clean AND the site builds locally with `--frozen-lockfile`
- [ ] `nix flake check` exit 0
- [ ] `just shake` reports without `--fix`
- [ ] `just verify` + `just fitness` exit 0; no publishing side effects anywhere

## STOP conditions

- The CHANGELOG's section format can't be extracted reliably (ambiguous version boundaries) —
  report the format; the extraction may need `gen-changelog.py` support (out of scope).
- The site build fails locally for a pre-existing reason (broken sync, missing chromium for a
  REQUIRED mermaid step) — report it as a finding; do not refactor `site/` to fix it.
- `nix flake check` wants network for anything — restructure the check to pure-static only or
  report which leg can't be purified.
- Anything would push a tag, create a release, or deploy — that's the hard rule.

## Maintenance notes

- Follow-ups (operator calls): Pages/host deployment for the site (visibility decision);
  verify-as-flake-check via the #63 FOD pattern; wiring `shake` as an advisory fitness leg;
  linking doc-gen4 output (plan 010) from the site once both exist.
- The release script's verify-gate assertion means a checkpoint release is: `just release vX.Y.Z`
  → read the printed commands → run them. Keep it that way — the human-on-the-button is the
  design, not a limitation.
