# Plan 007: Wire the Batteries lint driver + shake + import-graph tooling; produce the first triage report

> **Executor instructions**: Follow this plan step by step. Run every
> verification command and confirm the expected result before moving to the
> next step. If anything in the "STOP conditions" section occurs, stop and
> report — do not improvise. When done, update the status row for this plan
> in `plans/README.md` — unless a reviewer dispatched you and told you they
> maintain the index.
>
> **Drift check (run first)**: `git diff --stat f1cb2cf..HEAD -- lakefile.toml justfile`
> If either file changed since this plan was written, compare the "Current
> state" excerpts against the live code before proceeding; on a mismatch,
> treat it as a STOP condition.

## Status

- **Priority**: P2
- **Effort**: S–M
- **Risk**: LOW (config + a new recipe + reports; zero `.lean` edits, nothing wired into the default gate yet)
- **Depends on**: none hard. Plan 004 also edits `justfile` (the `verify:` line and a `run-batteries` recipe) — this plan must NOT touch the `verify:` line, and appends its recipe at the END of the justfile to keep the eventual merge trivial.
- **Category**: dx
- **Planned at**: commit `f1cb2cf`, 2026-07-10; **REVISED post-merge (main @ 60c98ac8)** after exec007's BLOCK: the repo deliberately has NO `Bang.lean` root barrel (retired by #81; `lakefile.toml` uses `globs = ["Bang.+"]`), so bare `lake lint` fails with `unknown module Bang`. **Operator ruling: module-ENUMERATION recipe is primary; a lint-only barrel is authorized as fallback if enumeration proves brittle** — but a barrel only counts as "better" if it demonstrably lints the imported modules' declarations (verify empirically; if runLinter only lints a module's OWN decls, a barrel lints nothing and must be rejected). Note: `justfile` gained recipes at the end (plan 004) — append after them; `verify:` line still out of scope.

## Why this matters

The project's dependency tree already contains the Lean ecosystem's code-hygiene tooling — `batteries` (environment linters: unused arguments, malformed simp lemmas, doc gaps, def-vs-lemma misuse), and `importGraph` (`lake exe graph`, `lake exe pole`, unused-import analysis) — but none of it is wired: `lakefile.toml` has no `lintDriver`, and the repo's import graph is a custom Python script. Wiring the driver converts "clean Lean" from convention to a runnable check (the repo's own derivation-strength ladder: a check that fails beats a style rule someone remembers). This plan does the wiring and produces the **first triage report** — it deliberately fixes nothing, because the first run on a ~30k-line codebase will have a backlog whose disposition (fix / nolint / disable-linter) is an operator decision, not an executor improvisation.

## Current state

- `lakefile.toml:1` begins (verbatim):

```toml
name = "bang-lang"
```

  There is no `lintDriver` key anywhere in the file. The mathlib requirement is at lines 26-27 (`[[require]] name = "mathlib"`).
- `lake-manifest.json` pins (among others): `mathlib`, `batteries`, `importGraph`, `LeanSearchClient`, `aesop` — all transitively available; **no new dependency is needed**.
- `justfile:28` is the `verify:` leg list — **do not modify it** (plan 004's territory).
- Toolchain: `leanprover/lean4:v4.30.0` (`lean-toolchain`).
- The repo convention for tools: recipes live in `justfile` with a one-line comment; heavier logic goes in `tools/*.sh` with a `# tool:` frontmatter line. This plan needs only recipes.
- Repo gate-trap rules: read errors via exit codes or `grep -E "error"`; pipe exit codes lie (`cmd | grep | head` returns `head`'s status).

## Commands you will need

| Purpose | Command | Expected on success |
|---|---|---|
| Enter dev shell (bare `lake`/`just` not on PATH) | `nix develop` | banner |
| Build (needed before linting; cold: minutes) | `nix develop --command just build` | exit 0 |
| Run the lint driver | `nix develop --command lake lint` | linter output (findings expected — nonzero exit is FINE on first run) |
| Unused-import report | `nix develop --command lake exe shake Bang` | report (do NOT pass `--fix`) |
| Import graph | `nix develop --command lake exe graph import-graph.dot` | dot file written |
| Build critical path | `nix develop --command lake exe pole` | table of files on the longest path |

## Scope

**In scope** (the only files you may modify/create):
- `lakefile.toml` — add the `lintDriver` line.
- `justfile` — append TWO new recipes at the very END of the file: `lint-lean` and `pole`.
- `plans/007-lint-triage.md` (create — the triage report deliverable; lives in `plans/` so it needs NO docs/notes frontmatter and doesn't touch the fitness-gated doc system).
- `plans/README.md` (status row — SKIP if your reviewer said they maintain the index).

**Out of scope** (do NOT touch):
- **Any `.lean` file — fix NOTHING the linters report.** No `@[nolint]` attributes, no deleted imports, no doc strings. The triage report is the deliverable; fixes are follow-up plans.
- The `verify:` line in `justfile` and anything in `tools/` (plan 004 owns both).
- `lake-manifest.json`, `lean-toolchain` — no dependency or toolchain changes.
- Do NOT run `lake exe shake --fix` (report mode only).

## Git workflow

- Branch: `advisor/007-wire-lean-linters`.
- Conventional commits, e.g. `dx(lint): wire batteries lint driver + shake/pole recipes; first triage report (plan 007)`.
- No `.lean` files change, so the pre-commit hook's verify leg won't trigger; fitness legs will.
- Do NOT push.

## Steps

### Step 1: Wire the lint driver

Add to `lakefile.toml`, immediately after the `name = "bang-lang"` line (package-level key, before any `[[…]]` block):

```toml
lintDriver = "batteries/runLinter"
```

**Verify (revised)**: bare `lake lint` is KNOWN to fail (`unknown module Bang` — no root barrel, by design). The wiring check is: (1) multi-module invocation works — `nix develop --command lake lint -- Bang.Core.EffectRow Bang.Frontend.Diagnostics` runs the 16-linter suite over both modules (findings + nonzero exit = success); (2) full enumeration works — `nix develop --command bash -c 'lake lint -- $(find Bang -name "*.lean" | sed "s|/|.|g; s|\.lean$||" | sort | tr "\n" " ")' > /tmp/lint-out.txt 2>&1; echo "exit: $?"` completes (findings expected). If multi-module invocation itself is rejected by runLinter's CLI, fall back to a per-module loop appending to `/tmp/lint-out.txt`; if THAT also fails structurally, try the barrel fallback (see revised Step 4) before stopping.

### Step 2: Triage the lint output

Read `/tmp/lint-out.txt`. Produce `plans/007-lint-triage.md` with:
1. A count table: findings per linter (e.g. `unusedArguments: N`, `simpNF: N`, `docBlame: N`, …).
2. Per linter: 3 representative examples (decl name + one-line finding), and a one-line disposition RECOMMENDATION — one of `fix-wave` (mechanical, worth a follow-up plan), `nolint-candidates` (intentional per repo conventions — e.g. `docBlame` on internal helpers if the repo's comment convention deliberately skips them; cite `docs/notes/lean-comment-style.md` if relevant), or `operator-call`.
3. A note of which linters found NOTHING (they're free to keep on).

No opinions beyond disposition tags; no fixes.

**Verify**: the report file exists and its per-linter counts sum to the total in `/tmp/lint-out.txt` (state both numbers in the report).

### Step 3: Shake + pole reports

1. `nix develop --command lake exe shake Bang > /tmp/shake-out.txt 2>&1; echo "exit: $?"` — unused-import report. If `shake Bang` errors on argument shape, try bare `lake exe shake`; record which form worked.
2. `nix develop --command lake exe pole > /tmp/pole-out.txt 2>&1; echo "exit: $?"` — build critical path. If `pole` is not an available executable in this dependency ring, note it in the report and continue (it is NOT a STOP).

Append to `plans/007-lint-triage.md`: shake's summary (how many files have removable imports, total lines removable — counts + 5 examples, not the full dump) and pole's top-10 critical-path files with their cumulative times. Add one cross-reference line: "pole data is input to the god-file seam map (plan 006) — the split that shortens this path buys build parallelism."

**Verify**: both sections present in the report with counts traceable to the tmp files.

### Step 4: Add the recipes

Append at the very END of `justfile` (after plan 004's recipes):

```make
# Batteries environment linters over every Bang module (plan 007; NOT in verify yet —
# first-run backlog is triaged in plans/007-lint-triage.md, wiring is an operator call).
# Module ENUMERATION because the repo has no Bang.lean barrel (retired, #81).
lint-lean:
    lake lint -- $(find Bang -name '*.lean' | sed 's|/|.|g; s|\.lean$||' | sort | tr '\n' ' ')

# Build critical path (importGraph's pole) — which files serialize the build.
pole:
    lake exe pole
```

(Adjust the recipe body to whichever invocation form Step 1 proved: multi-module args, a per-module loop, or — LAST resort, operator-authorized fallback — a generated lint-only barrel `BangLint.lean` importing all modules, declared as its own `lean_lib`, ONLY if you empirically confirmed runLinter lints imported modules' decls through it. Whichever form lands, the recipe must lint every `Bang/**/*.lean` module and fail on findings.)

**Verify**: `nix develop --command just lint-lean` runs the same suite as Step 1; `nix develop --command just --list` shows both new recipes. `nix develop --command just fitness` → exit 0 (no doc refs broken).

### Step 5: Commit

Commit `lakefile.toml`, `justfile`, `plans/007-lint-triage.md` by pathspec.

**Verify**: `git status --porcelain` clean apart from untracked files that pre-existed; `git show --stat HEAD` lists exactly the three files.

## Test plan

The deliverable is wiring + a report, so the tests are the verify lines above: the driver runs, the recipes exist, fitness stays green, and the report's counts reconcile with the raw outputs. No new automated tests (nothing is wired into the gate yet — deliberately).

## Done criteria

- [ ] `lakefile.toml` contains `lintDriver = "batteries/runLinter"`
- [ ] `nix develop --command just lint-lean` runs the linter suite end-to-end
- [ ] `plans/007-lint-triage.md` exists: per-linter counts + examples + disposition tags, shake summary, pole top-10 (or a note that pole is unavailable)
- [ ] Zero `.lean` files modified (`git diff --stat f1cb2cf..HEAD -- '*.lean'` → empty)
- [ ] `justfile`'s `verify:` line is byte-identical to `f1cb2cf`'s
- [ ] `nix develop --command just fitness` exits 0
- [ ] `plans/README.md` status row updated (unless the reviewer maintains the index)

## STOP conditions

Stop and report back (do not improvise) if:

- `lake lint` fails with a CONFIGURATION error (unknown `lintDriver` key, driver not found, or a toolchain/Batteries version incompatibility under `v4.30.0`) — the wiring recipe may differ on this pin; report the exact error. Do not vendor a lint driver or edit the manifest.
- `lake lint` runs but takes >30 minutes — report the timing; a slow linter changes the wiring calculus.
- The lint output is so large the triage would exceed ~200 findings in a single linter — report the count table only and flag that linter for an operator decision on whether to disable it before full triage.
- Anything requires editing a `.lean` file or the `verify:` line.

## Maintenance notes

- Follow-ups this report feeds (each an operator call, none started here): (1) fix-wave plans per linter disposition; (2) wiring `lint-lean` into `verify` once the backlog is zero or nolint-annotated — sequence AFTER plan 004's verify rewiring lands to avoid recipe-line conflicts; (3) replacing/augmenting `tools/gen-import-graph.py` with `lake exe graph` output (check what the custom script provides that graph doesn't before deleting anything); (4) handing the pole data to plan 006's follow-up ADR.
- Reviewer should scrutinize: that NO `.lean` file changed, and that the report's disposition tags cite repo conventions (e.g. the comment-style note) rather than generic Lean taste.
