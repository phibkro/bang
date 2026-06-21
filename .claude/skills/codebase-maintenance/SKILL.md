---
name: codebase-maintenance
description: Keep a software repository healthy and maintainable — really green, its docs and decisions true rather than drifted, its entropy (cruft, debt, deps, secrets) in check. Use before committing, when wrapping a session, or when the user says "checkpoint", "is this clean / ready", "wrap up", or "stale". Surveys only the blast radius of what changed, graded by the seam.
---

# Codebase maintenance

A repo rots two ways: **broken** (the build or tests are untrue) and **drifted**
(its derived descriptions — docs, decisions, status — no longer match reality).
Maintenance keeps every *derived fact* true, scoped to the **blast radius** of what
changed, at a **grade** the seam picks.

## The one idea: climb the derivation ladder

For every fact a repo derives from its code, the question is *which rung enforces it*:

```
GENERATE   drift is unrepresentable     generated reference, llms.txt — leaves the survey
   ▲
TEST       drift caught at CI           doctests · link-check · AST-anchors · doc-gating ·
   ▲                                    secret-scan · lockfile-CI · architecture fitness functions
SURVEY     drift judged by hand (hope)  the blast-radius survey — the LAST resort, for the
                                        residue that can't be generated or tested
```

This *is* the machine/judgment split: generate+test are machine; survey is judgment.
The maintenance instinct is to **climb** — pull each fact to the strongest rung the
toolchain allows, so the hand-survey shrinks to only what's irreducibly semantic.

## Routing

Look for this repo's instance. It lives **in the project repo** — `.claude/codebase-maintenance.md`,
or wherever the project's `CLAUDE.md` points — *not* beside this skill (a globally-installed
skill is read-only, so it can't host a writable per-project instance). **It exists →** load it
(gate command, artifact map, guards, which surfaces sit on which rung) and run the maintenance
pass below. **It doesn't →** generate it first: `BOOTSTRAP.md` analyses the codebase, documents
its maintenance practices, and flags where it's stuck on *survey* that could be *test*/*generate*.

## Run — grade by seam, then gate then survey

**Grade** (the seam chooses it, not feel): per-edit **G0** (per-file check) · per-commit
**G1** (dep-aware build + diff-scoped lint + guards + tree-clean) · feature/wrap **G2**
(G1 + blast-radius survey) · release **G3** (full sweep + cold-agent dogfood). Most are G1/G2.

1. **Classify** — `git diff <last-green>..` for the changed *surface* + the *work-type*.
   **Discover the repo's actual work-type vocabulary from `git log`** — don't assume
   `feat`/`fix`/`chore`; many repos use domain scopes (`kernel:`, `feat(worker)`), and the
   *scope* often routes the survey more than the type. Renames carry no content debt.
   *Done when* you can name the changed surface and its work-type **in the repo's own vocabulary**.

2. **Gate — machine (every grade).** Run the instance's gate and read its **real exit
   code**. Three traps the gate can hide:
   - a *piped* exit (`cmd | head` returns head's exit, always 0) — *the* classic false-green;
   - an *orchestrator* gate (a wrapper script) whose interpreter may not be provisioned, or
     that `exit(0)`s regardless — **parse its output, don't trust the exit**; decompose into
     sub-checks if it won't run as-is;
   - a gate that **splits by grade into verify vs apply** — a safe *verify* gate runs at the
     checkpoint; a *mutating* apply/deploy step (rebuilds a machine, ships a release) is
     **operator-gated and NEVER auto-run** — identify it, don't run it.

   The verify gate bundles the repo's *test*-rung checks: build+tests pass *deterministically*
   (not flaky/retry-green), tree committed, secret-scan clean, lockfile matches manifest, plus
   its own guards. *Done when* the verify gate passes on a real (or parsed) result — **or you
   stop and report**.

3. **Survey the blast radius — judgment (G2+).** From `work-type × volatility`, derive the
   *shortlist* of facts the change could have falsified — docs, ADRs, status, the debt
   census — and **confirm-current or update each** (autofix the generated ones). This is the
   residue the ladder couldn't mechanize. *Done when* every implicated artifact is
   confirmed-or-updated, named one by one — not "checked the docs."

4. **Honest handoff.** Every claim you leave (commit message, status doc, any "done") points
   at a **real artifact** and separates *done* from *deferred*. *Done when* claims are
   evidence-bound.

## The maintenance surface

What a pass covers, beyond build+docs (full menu + sources in `REFERENCE.md`):

`build · test (flaky/stale-skip) · docs (rung-by-Diátaxis) · deps (lockfile/unused) · cruft (dead code) · debt (SATD census, health-over-debt) · security (secrets/SCA) · architecture (cycles/layering as fitness functions) · decisions (ADR currency & supersede-integrity)`

The instance records which of these *this* repo has, and on which rung.

## Anti-triggers

A pure rename, a comment typo, a `chore` with no interface or doc surface → G0/G1 only;
skip the survey. Scale the pass to the change — surveying nothing is correct when the blast
radius is empty.
