# Plan 010: Wire doc-gen4 — generated API docs from the docstring convention

> **Executor instructions**: Follow this plan step by step. Run every verification
> command and confirm the expected result before moving on. If a STOP condition
> occurs, stop and report — do not improvise. Update this plan's status row in
> `plans/README.md` unless your reviewer maintains the index.
>
> **Drift check (run first)**: `git log --oneline -3 -- lakefile.toml docs/notes/lean-comment-style.md`
> and confirm the "Current state" facts below still hold.

## Status

- **Priority**: P3
- **Effort**: M
- **Risk**: LOW (additive subproject; main build untouched)
- **Depends on**: the census unit landing (task #37 / lane w2census) — Step 1's banner sweep
  touches every `Bang/*.lean` top-of-file banner and must not collide with in-flight proof edits
  (this is the exact deferral recorded in `docs/notes/lean-comment-style.md` §Adoption status).
- **Category**: dx / docs
- **Planned at**: main @ `b0e7b6a6`, 2026-07-10

## Why this matters

The repo's comment convention (`docs/notes/lean-comment-style.md`, Mathlib-grounded, operator
policy in `CONTRIBUTING.md` §5) exists to make `/--` docstrings and `/-!` section maps consumable
by generated tooling — but nothing generates from them yet: doc-gen4 is not wired (verified: no
require in `lakefile.toml`, no `docbuild/`, no docs recipe). Wiring it (a) turns 661 docstrings
into a browsable API site, (b) gives the agent-ergonomics story its hover-equivalent web face,
(c) makes the docstring convention *observable* — an undocumented public decl is visible as a
gap in the output, which is the soft pressure that precedes any docBlame enforcement.

## Current state

- `lakefile.toml` — TOML config (no conditional requires possible in TOML), requires only
  `mathlib` @ `v4.30.0`. Do NOT add doc-gen4 here (dependency-ring bloat; it would churn
  `lake-manifest.json` and the nix FOD packaging).
- The Mathlib-ecosystem pattern for exactly this situation: a **separate `docbuild/` subproject**
  — its own `lakefile.toml` (or `.lean`) that requires `doc-gen4` (pin the tag matching the
  toolchain: `v4.30.0`; doc-gen4 tags track Lean releases) AND requires the parent `bang-lang`
  package by path (`../`). Docs build from inside `docbuild/`; the main project's manifest and
  builds are untouched. Mathlib itself uses this shape.
- The banner gap: top-of-file banners in ~20 modules are plain `/- … -/`, which doc-gen4 and
  hover IGNORE — the §-maps (the richest orientation content) would be invisible in the output.
  `lean-comment-style.md` defers this sweep with the trigger "once the LR re-index settles."
- Toolchain: `leanprover/lean4:v4.30.0`.

## Scope

**In scope**: every `Bang/**/*.lean` top-of-file banner (delimiter-only change, Step 1);
`docbuild/` (new subproject); `justfile` (one `docs` recipe appended at the end);
`.gitignore` if docbuild's build dir needs it; `docs/notes/lean-comment-style.md` (flip the
"DEFERRED" banner-sweep status to done).

**Out of scope**: docstring CONTENT (no new docstrings — that's the docBlame backlog, separate);
any `def`/`theorem`; the main `lakefile.toml` / `lake-manifest.json`; CI publishing (a follow-up
once the local build works); the `verify:` gate (docs builds are slow — never in the default gate).

## Steps

### Step 1: The banner sweep (`/-` → `/-!`)

Mechanical: for each `Bang/**/*.lean` whose top-of-file banner block opens with `/-` (not `/-!`
and not a `/--` docstring), change the opener to `/-!`. Delimiter only — zero content changes.
Check each changed file compiles: banners with lines starting `-`/`*` can change meaning under
markdown rendering, but must not change ELABORATION.
**Verify**: `nix develop --command lake build` exit 0; `git diff --stat` shows banner files with
±1 line each; `just verify` exit 0. Commit separately (`style(docs): promote module banners to /-!
— the lean-comment-style deferred sweep`). Update the note's Adoption-status line in the same
commit.

### Step 2: The docbuild subproject

Create the subproject: a new `docbuild/` directory holding its own lakefile (TOML): package `docbuild`; `[[require]] doc-gen4` from
`https://github.com/leanprover/doc-gen4` rev/tag matching `v4.30.0`; `[[require]] bang-lang`
with `path = ".."`. Copy the parent `lean-toolchain` into `docbuild/`.
**Verify**: `cd docbuild && nix develop --command lake build Bang:docs` completes (FIRST run is
long — doc-gen4 + dependencies compile, and pages generate for the import closure; expect tens of
minutes cold). Output exists under `docbuild/.lake/build/doc/` with `Bang/` module pages; open one
generated page and confirm a `/-!` §-map from Step 1 renders in it (the point of the sweep).

### Step 3: Recipe + housekeeping

Append to `justfile`:

```make
# Generated API docs (doc-gen4, docbuild/ subproject — NOT in verify; slow).
docs:
    cd docbuild && lake build Bang:docs && echo "→ docbuild/.lake/build/doc/index.html"
```

Gitignore `docbuild/.lake/` if the root `.gitignore` doesn't already cover nested `.lake/`.
**Verify**: `nix develop --command just docs` reproduces Step 2; `just fitness` exit 0;
`just verify` exit 0 (must be unaffected — docs are outside the gate).

## Done criteria

- [ ] All Bang module banners are `/-!`; `lean-comment-style.md` deferral flipped
- [ ] `just docs` builds a browsable site; a §-map visibly renders in a generated page
- [ ] Main `lakefile.toml` + `lake-manifest.json` byte-identical to base
- [ ] `just verify` exit 0 and its wall time unchanged (docs not in the gate)

## STOP conditions

- doc-gen4 has no tag/rev compatible with `v4.30.0`, or the docbuild resolve wants a different
  toolchain — report the exact resolution error; do not bump `lean-toolchain` to make docs work.
- The banner sweep changes any file's elaboration (build error after a delimiter-only change) —
  report the file; its banner content is load-bearing in a way the plan didn't anticipate.
- The docs build wants to regenerate Mathlib's full doc set and exceeds ~90 min — report; scoping
  options (doc-gen4 facet configs) need investigation before burning more time.
- Anything requires touching the parent manifest or a `def`/`theorem`.

## Maintenance notes

- Follow-up (not this plan): CI job publishing the site (GitHub Pages), and revisiting docBlame
  enforcement for Tier-1 public API once gaps are visible in the generated output.
- The docbuild subproject needs its `lean-toolchain` bumped in lockstep whenever the root one
  moves — note this in any future toolchain-bump plan.
