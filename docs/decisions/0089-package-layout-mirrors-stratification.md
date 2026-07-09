# ADR-0089 · Package layout mirrors the stratification — multi-package Lake workspace

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: The repo has outgrown "one lib + a CLI": the tested superset now spans a parser/elaborator/formatter frontend, a REPL-bearing CLI, a witness layer (differential fuzz #14, outcome-oracle #54), and non-Lean tooling — while the verified spine stays the proof-budget core. The stratification seam (verified core / tested superset, ADR-0026/0028) is currently enforced one rung DOWN the derivation ladder: `tools/arch-check.sh` **tests** that `Bang/Frontend` has fan-in 0 from the spine. **Decision: restructure into a multi-package Lake workspace whose dependency arrows ARE the stratification — `bang-spine` (Core+Backend+Meta+Spec+Audit, the only Mathlib consumer) ← `bang-frontend` ← `bang-witness`, with the `bang` exe atop frontend — so a spine module importing the frontend becomes UNBUILDABLE (a require-cycle error), not merely a red script.** Module NAMES do not change (imports stay `Bang.Core.…`/`Bang.Frontend.…`), so the churn is lakefile surgery + CI/cache plumbing, not an import rewrite. Crucially rejected as insufficient: splitting into multiple `[[lean_lib]]`s **inside one package** — Lake resolves imports package-wide regardless of lib membership, so that split is organizational cosmetics at the same enforcement rung we already occupy. Also rejected: multi-REPO split (kills the shared proof context, atomic cross-strata commits, and the single `just verify` gate for zero added enforcement over a workspace). **Timing: entry-gated on the #44 rung-2 landing** — the spine is mid-surgery (`feat-44-rung2`); restructuring under it would force a rebase across a package boundary.
- **Depends-on**: 0026, 0028, 0016
- **Relates-to**: the stratification principle (CLAUDE.md), `tools/arch-check.sh` (the check this supersedes-in-part), #58/#59 (the tool growth that motivates it)

## Status

Accepted (2026-07-09, operator ruling same day). **Entry gate: #44 rung-2 landed on main** (one
spine-surgery at a time; the workspace cut is a whole-tree refactor) — the gate OPENED the same
day (rung-2 landed at the census-clean gate); execution is a dedicated unit, not started yet.

- **Layer:** build/tooling only. No Lean statement changes; the axiom gate and census are
  unaffected (Audit stays in the spine package, gating the same theorems).

## Context

The derivation-strength ladder (CLAUDE.md) ranks enforcement: **generate/structural**
(violation unrepresentable) > **test** (violation caught) > **convention** (hope). The
stratification seam — the project's load-bearing shape — sits at the *test* rung:
`arch-check.sh` greps the import graph and fails fitness on a spine→frontend edge. That check
has worked, but it is a script someone could weaken, skip (`--no-verify`), or mis-regex — and
the tool stratum keeps growing (Format.lean, the REPL, `bang check --json` (#59), witness
modules), each addition widening the surface the script must police.

Lake's actual semantics decide the design space:
- **Libs within one package do NOT gate imports.** Any module may import any module in the
  same package; `[[lean_lib]]` membership only groups build targets. A within-package split
  would LOOK stratified while enforcing nothing — a representable illegal state with better
  branding, i.e. worse than the honest script.
- **Packages DO gate imports.** A module can only import modules of packages its own package
  `require`s. With `bang-spine ← bang-frontend ← bang-witness`, a spine module importing
  `Bang.Frontend.…` is a build error (unknown module), and making it buildable would need a
  `require` cycle, which Lake rejects. The seam becomes structural.

## Decision

### D1 — workspace shape (dependency arrows = the strata)

```
bang-spine      Bang/{Core,Backend,Meta,Spec,Audit}.lean + Bang/Spec/…      requires: mathlib
   ▲            the verified core — proof budget, axiom gate, frozen statements
bang-frontend   Bang/Frontend/…                                             requires: bang-spine
   ▲            tested leaf: parser · TypeCheck · Format · prelude
bang-witness    Bang/Witness/…                                              requires: bang-spine, bang-frontend
                observation layer: fuzz · outcome-oracle · regressions
bang (exe)      Main.lean                                                   requires: bang-frontend
```

Module names are unchanged — the packages partition the existing `Bang.*` namespace, so no
`import` line in any `.lean` file moves. `just verify` drives the workspace root and behaves
identically.

### D2 — what arch-check.sh becomes

The spine→frontend leg of `arch-check.sh` is DELETED (superseded by structure — keeping it
would be a second copy of a fact). Legs the workspace cannot express (e.g. per-module fan-in
reporting, doc-graph sync) stay.

### D3 — cache and CI

`lake exe cache get` (Mathlib) concerns only `bang-spine`; the seeded-clone tooling
(`tools/new-worktree.sh`) seeds the same `.lake/packages` path and is unaffected. CI's single
`just verify` stays the gate; a follow-up MAY add a frontend-only fast path (build
`bang-frontend` without re-elaborating the spine) — an optimization, not part of this decision.

### D4 — non-Lean tools stay put

`tools/` (python/bash gates), the tree-sitter grammar, and docs generators are not Lake
packages and gain nothing from being one. They remain repo-level, indexed where they already
are.

## Considered options

- **Multi-package Lake workspace — CHOSEN.** The only option that moves the seam to the
  structural rung. Cost: one-time lakefile surgery, CI/cache plumbing, contributor
  re-orientation (three lakefiles instead of one), and slightly slower whole-tree cold builds
  (per-package manifests). No import churn.
- **Multiple `[[lean_lib]]`s in one package — REJECTED.** Lake does not gate imports by lib;
  this is the same enforcement rung as today with an appearance of more — strictly worse than
  the honest script.
- **Status quo (arch-check.sh) — REJECTED as endpoint, kept as fallback.** It works today; it
  is the fallback if the workspace cut surfaces an unforeseen Lake limitation. But it is a
  *test* of a property the build system can make *unrepresentable*, and the tool stratum's
  growth keeps raising the script's maintenance burden.
- **Multi-repo split — REJECTED.** Kills atomic cross-strata commits (a kernel rename + its
  frontend ripple become a two-repo dance), fragments the proof context and the single verify
  gate, adds versioning ceremony — for zero enforcement gain over a workspace.

## Invariant compliance

- **Axiom gate / census**: unchanged — `Bang/Audit.lean` lives in `bang-spine` and gates the
  same theorem set; `just axioms` unchanged.
- **Stratification (ADR-0026/0028)**: strengthened — the seam moves from tested to structural,
  the same move the language itself makes with the effect row.
- **#7 (performance second-class)**: the cold-build cost is accepted; the fast-path split in
  D3 is optional future work.

## Revisit if

- Lake workspace tooling fights the two-hop build in a way a spike can't resolve → fall back
  to status quo + arch-check, record the wall here.
- The tool stratum grows a genuinely independent artifact (e.g. an LSP server with its own
  release cadence) → that artifact MAY warrant its own repo then; re-open with evidence.

## Evidence

`lakefile.toml` (current single-lib glob + the `bang` exe), `tools/arch-check.sh` (the tested
seam), `docs/architecture/core-overview.md` (fan-in table showing Frontend/Witness fan-in 0),
ADR-0026/0028 (the stratification this mirrors), Lake docs on package `require` semantics
(import visibility is package-scoped, lib-scoped only for target grouping).
