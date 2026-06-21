# Checkpoint — why the blast-radius selection works

Disclosed from `SKILL.md`. Read when you want the reasoning behind the volatility
gradient and the work-type scoping, or when adapting the procedure to a new repo.

## Why Diátaxis predicts volatility

[Diátaxis](https://diataxis.fr) splits documentation into four modes by two axes
(action↔cognition, acquisition↔application). For *checkpoint* purposes the useful
consequence is a third property the modes differ on: **coupling to code**, which
*is* volatility — how often the artifact goes stale per unit of code change.

```
Reference     describes WHAT IS (signatures, flags, options) — moves with every
              interface change. Tightest coupling ⇒ highest volatility. This is
              why Reference should sit on the strongest derivation rung
              (generate > test > hand): a generated reference cannot drift, so it
              leaves the survey entirely. Hand-maintained Reference is the most
              dangerous doc you own.
How-to        describes a TASK PATH — moves when the workflow/commands move, not
              when internals change. Medium coupling. Runnable examples convert it
              to a test (it fails when it lies).
Explanation   describes WHY — rationale, architecture, trade-offs (ADRs). Loosely
              coupled: a bug fix doesn't change why you chose an architecture. Low
              rate, but HIGH stakes when it does move (a design pivot), so it's
              append-mostly: add a new ADR, rarely edit an old one.
Tutorial      a LEARNING path — changes slowly; survey rarely.
```

The **volatile-state doc** (here `CONTEXT.md`) is *not* Diátaxis documentation —
it is live project state (current position, active path, blockers). It is
designed to change every session, so it is always in the blast radius.

## The linter lessons, mapped

A checkpoint *is* a linter whose lint target is the repo's truthfulness. The
mature ideas from static analysis transfer directly:

| linter idea | checkpoint use |
|---|---|
| rule-selection (rules per file type) | survey-selection (artifacts per **work-type**) |
| severity (error / warning / info) | block-commit / warn / note |
| incremental lint (`lint-staged`) | diff-scope file-local checks to `git diff --name-only` |
| autofix | regenerate derived docs — fix, don't just flag |
| baseline / suppression | pre-existing-red is baselined; gate on **new** violations only |
| result cache keyed by file hash | git's content addressing *is* the cache; checkpoint = "since last green" (`git diff <last-good>..`) |
| AST over regex | prefer structural cross-refs ("exported symbol lacks a doc entry") over text vibes |

## Incremental vs full sweep — the decision rule

Two axes people conflate:

```
git diff  ──►  the change-set      (what changed)
dep graph ──►  the blast radius    (what that can break)

incremental is SOUND  ⟺  the check is file-local
                          OR the dependency-aware tool covers the blast radius
```

- **file-local** checks (format, lint, doc-survey of *implicated* artifacts) →
  scope to the diff. Sound and cheap.
- **dependency-coupled** checks (a type change breaks callers) → *don't* hand-roll
  incrementality; the build tool already rebuilds only changed + dependents. A
  "full" build is mostly incremental under the hood after the first cold build.
- git is the **checkpoint ledger**: each commit is a known-good marker, so the
  unit of work is "what changed since the last green checkpoint," never "the
  whole universe."

## The tool worth building

A `checkpoint` command that:

1. classifies `git diff <last-green>..` → work-type + changed surface,
2. runs the machine gate (real exit code),
3. **emits the scoped survey worklist** — the shortlist of artifacts to read,
   derived from work-type × volatility (e.g. "touched the CLI surface → re-read
   README §usage + the command reference").

Output is part pass/fail (the gate) and part targeted to-review list (the
survey). The *principle* is general; the *gate command* and *artifact map* are
per-repo config (see `instances/`). This keeps the machine/judgment split honest:
the tool does all the mechanizable work and never pretends to judge fidelity — it
hands the agent the smallest possible thing to judge.

> **Epistemic note on Diátaxis.** [diataxis.fr](https://diataxis.fr) gives *no*
> guidance on volatility or generate-vs-handwrite — it classifies docs by *purpose*,
> not by coupling-to-code. The "Reference is most volatile, so generate it" mapping
> here is *our* layer on top, derived from the SOUL derivation ladder. And real
> content resists clean quadrant assignment (a doc can serve two needs) — so treat
> the Diátaxis classification as a *predictive heuristic for where to look*, not
> ground truth, and pair it with the mechanical checks below.

## The full maintenance surface (researched 2026-06-21)

Build + docs are two of *nine* surfaces. Each check is tagged by its **rung**
(generate/test/survey) and **cadence** (G1 commit / G2 feature / G3 release). The
reframe that matters: most of these are mechanizable — they belong on the *test*
rung, not the hand-survey.

**test-truth ≠ build-truth.** "Really green" must also mean *deterministically* green
(not flaky/retry-green) and *completely* green (no stale `skip`/`xfail`/`sorry`
silently dropping coverage). Census the skips; require each carry a live linked reason
— the discipline a Lean repo already runs for `sorry`/axiom burndown.
[Google flaky tests](https://testing.googleblog.com/2016/05/flaky-tests-at-google-and-how-we.html) · test · G2.

**security — secret scan.** `gitleaks` as pre-commit + CI. A checkpoint *is* "before
commit"; a leaked secret is permanent (removal cosmetic, rotation mandatory). Cheapest,
highest-consequence missing gate. [gitleaks](https://github.com/gitleaks/gitleaks) ·
test/gate · G1. Plus SCA vuln scan; [OpenSSF Scorecard](https://github.com/ossf/scorecard)
composes repo-health checks · G3.

**deps — lockfile-CI + unused.** Install frozen (`--frozen-lockfile`/`npm ci`) so
lockfile↔manifest drift *errors* — drift can make a *cached* build falsely green. `Knip`
reports unused deps + dead exports + orphan files. [Knip](https://knip.dev/) · test · G2.

**cruft — dead code.** Mark-and-sweep unused exports/files from entry points (Knip);
commented-out code belongs in git history, not source. test · G2.

**debt — make it visible; track health not debt.** Diff the SATD census
(`TODO`/`FIXME`/`HACK`); flag bare/orphaned markers (each should carry an owner or
issue link). Reframe "no new debt" → *health held as an SLO*
([ThoughtWorks](https://www.thoughtworks.com/radar/techniques/tracking-health-over-debt)).
**Cognitive debt** — the gap between code and shared understanding, widening as AI
generates more code ([TW Radar](https://www.thoughtworks.com/radar/techniques/codebase-cognitive-debt))
— uniquely sharp for an agent-authored repo. survey (+ census) · G2.

**architecture — invariants as fitness functions.** Promote prose invariants (no import
cycles, layering, "only X is privileged") to *enforced* checks (ArchUnit-style
`beFreeOfCycles`, boundary rules that break the build) — strongest rung vs hand-checking.
[InfoQ fitness functions](https://www.infoq.com/articles/fitness-functions-architecture/) · test · G2.

**decisions — ADR currency + supersede-integrity.** ADRs are append-only: supersede
(status → Superseded, bidirectional link), **don't delete** (deletion loses the
rejected-alternative trail the format exists to preserve). Lint orphaned supersede links;
periodically check surviving ADRs still describe reality. [adr.github.io](https://adr.github.io/)
· survey (+ link lint) · G2/G3.

## Docs surface — climbing prose off the survey rung

The highest-leverage doc finds pull *hand-written prose tied to code* from *survey* up
to *test*:

- **AST-fingerprint anchoring** (the standout) — a doc anchors a code symbol + provenance
  SHA (`auth.ts#AuthConfig@a1b2c3d`); CI re-parses, hashes the symbol's normalized AST,
  flags the doc stale when the AST changed (ignores reformatting). Mechanizable freshness
  for prose that *can't* be generated. [Fiberplane Drift](https://fiberplane.com/blog/drift-documentation-linter/).
- **Doc-gating at the PR** — `CODEOWNERS`/branch-protection require that when source X
  changes, its doc Y is touched in the same PR. *Detect-after → unrepresentable-at-merge.*
  [Write the Docs](https://www.writethedocs.org/guide/docs-as-code/).
- **Doctests** — examples *in* narrative docs compiled+run by the suite; they fail when
  they lie. Caveat (invariant #1): a tested doc still lies about a dimension the test
  doesn't exercise — run examples against the *real* path.
  [rustdoc tests](https://doc.rust-lang.org/rustdoc/documentation-tests.html).
- **Link-check** (`lychee`) + a **last-reviewed** metric for long-lived Explanation docs
  no test covers. [lychee](https://github.com/lycheeverse/lychee).
- **Agent-doc hygiene** — CLAUDE.md/AGENTS.md obey the same ladder: enforce a line/token
  budget (>~500 lines → mostly ignored), generate `llms.txt`, reference-don't-copy across
  configs. [llms.txt](https://llms-txt.io/).
