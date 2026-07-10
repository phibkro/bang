# Plan 007 — Batteries lint driver: first triage report

Generated 2026-07-10 by wiring `lintDriver = "batteries/runLinter"` (lakefile.toml) and
running `just lint-lean` over the module set proven in Step 1 below. This report fixes
NOTHING — disposition of each backlog item is an operator call. See `docs/notes/lean-comment-style.md`
for the project's adopted doc convention (relevant to the docBlame disposition).

## Invocation form (what actually works, and the trap the plan's rungs (a)/(b) hid)

`lake lint -- Bang.Core.EffectRow` runs all 16 linters and reports findings for
`Bang.Core.EffectRow`'s **entire transitive import closure**, not just its own
declarations (confirmed: the same `EffectRow.lean:26:1` docBlame finding shows up
whether you lint `Bang.Core.EffectRow` alone or `Bang.Frontend.Diagnostics` alone,
since Diagnostics transitively imports EffectRow).

**Multi-module args do NOT union.** `lake lint -- A B` scopes to the import closure of
the **last** argument only — verified by reversing the two-module probe from the plan
(`Bang.Core.EffectRow Bang.Frontend.Diagnostics` vs `Bang.Frontend.Diagnostics
Bang.Core.EffectRow`: the "Found N errors ... in `<lastArg>`" summary line and the full
finding set track whichever module is passed last; the earlier arg is inert). So the
plan's rung (a) "multi-module args" does not do what it sounds like — it is a
single-effective-scope invocation, same as passing one module.

**"Enumerate every `.lean` file" (the plan's rung (b)/the STOPPED prior attempt's `lint-lean`
draft) is neither necessary nor correct**: since each module-arg pulls in its whole closure,
passing all 49 files as 49 separate scopes reports the same declaration's finding once per
scope that transitively contains it — massive duplicate counts, and no way to read off a
clean per-linter total.

**What actually works and is used by `just lint-lean`**: enumerate the **root modules**
(files nothing else in `Bang/` imports — 19 of them) and lint each as its own single-arg
invocation. Every one of the 49 `Bang/**/*.lean` files is transitively reachable from at
least one of the 19 roots (verified by a BFS over the import graph — see the Coverage
section). This is both complete and non-redundant at the *scope* level (dedup across the
19 runs' overlapping closures is still needed for an accurate per-linter count, which is
what this report's counts already do).

The barrel fallback (rung (d)) was **not needed** — rung (a)'s premise ("multi-module args
work") turned out subtly false, but the underlying single-module invocation form scales via
root-enumeration without a hand-maintained barrel file. No `.lean` file was added.

## Coverage

19 root modules × 1 `lake lint` invocation each. Verified complete via a Python BFS over
the import edges (import graph, not `lake`'s own): starting from the 19 roots and following
`import Bang.*` / `public import Bang.*` edges, **all 49 `Bang/**/*.lean` files are reached**
— zero coverage gap.

Roots (never imported by anything else under `Bang/`):
`Bang.Audit`, `Bang.Backend.EnvMachine`, `Bang.Distribution`, `Bang.Examples`,
`Bang.Frontend.Lint`, `Bang.Frontend.NamedCore`, `Bang.Frontend.Rewrite`,
`Bang.Frontend.Surface.PropTest`, `Bang.Frontend.Surface.Trait`, `Bang.Reify.CalcReifySim`,
`Bang.Witness.BinopTyping`, `Bang.Witness.BoccRegress`, `Bang.Witness.CapEscapeWitness`,
`Bang.Witness.CustomStage1Refute`, `Bang.Witness.ElabFuzz`, `Bang.Witness.ProofExport`,
`Bang.Witness.ReturnEscapeReach`, `Bang.Witness.StateEscapeWitness`, `Bang.Witness.VcapFreeRefute`.

## Linter roster (16 total: 12 batteries + 4 mathlib)

batteries (`.lake/packages/batteries/Batteries/Tactic/Lint/{Misc,Simp,TypeClass}.lean`):
`dupNamespace`, `unusedArguments`, `docBlame`, `defLemma`, `checkUnivs`, `synTaut`,
`unusedHavesSuffices`, `simpNF`, `simpVarHead`, `simpComm`, `impossibleInstance`,
`nonClassInstance`.

mathlib (`Mathlib/Tactic/Linter/{Lint,Style,TacticDocumentation}.lean`):
`structureInType`, `deprecatedNoSince`, `tacticDocs`, `defsWithUnderscore`.

## Per-linter count table

| Linter | Findings (deduped) | Files touched | Disposition |
|---|---:|---:|---|
| `docBlame` | 310 | 21 | **count-table only** (exceeds ~200; see below) |
| `unusedArguments` | 22 | 8 | `operator-call` |
| `defsWithUnderscore` | 17 | 2 | `nolint-candidates` |
| `dupNamespace` | 0 | — | clean |
| `defLemma` | 0 | — | clean |
| `checkUnivs` | 0 | — | clean |
| `synTaut` | 0 | — | clean |
| `unusedHavesSuffices` | 0 | — | clean |
| `simpNF` | 0 | — | clean |
| `simpVarHead` | 0 | — | clean |
| `simpComm` | 0 | — | clean |
| `impossibleInstance` | 0 | — | clean |
| `nonClassInstance` | 0 | — | clean |
| `structureInType` | 0 | — | clean |
| `deprecatedNoSince` | 0 | — | clean |
| `tacticDocs` | 0 | — | clean |

**349 total unique findings across 3 active linters; 13 of 16 linters are fully clean.**
Counts sum-check: 310 + 22 + 17 = 349, matching the total unique-finding count across
the 19 root-module `lake lint` invocations (deduped by (linter, file, line, col, message)
to correct for the overlapping-closure double-count `just lint-lean`'s per-module loop
otherwise produces — see the invocation-form note above).

## docBlame — count-table only (310 findings, 21 files; exceeds the ~200 flag threshold)

Top files by finding count:

| File | Findings |
|---|---:|
| `Bang/Frontend/Surface.lean` | 62 |
| `Bang/Frontend/TypeCheck.lean` | 46 |
| `Bang/Backend/Wasm.lean` | 28 |
| `Bang/Meta/LR.lean` | 24 |
| `Bang/Witness/ProofExport.lean` | 24 |
| `Bang/Witness/LawTest.lean` | 20 |
| `Bang/Backend/EnvMachine.lean` | 19 |
| `Bang/Backend/AbstractMachine.lean` | 13 |
| `Bang/Core/IR.lean` | 13 |
| `Bang/Frontend/Query.lean` | 11 |
| `Bang/Reify/CalcReify.lean` | 11 |
| `Bang/Core/EffectRow.lean` | 7 |
| `Bang/Core/Typing.lean` | 7 |
| `Bang/Core/Freshness.lean` | 6 |
| `Bang/Core/Semantics/Subst.lean` | 6 |
| `Bang/Frontend/Lint.lean` | 5 |
| `Bang/Core/Semantics/Eval.lean` | 4 |
| `Bang/Core/Soundness.lean` | 1 |
| `Bang/Core/Grade.lean` | 1 |
| `Bang/Frontend/Surface/PropTest.lean` | 1 |
| `Bang/Reify/CalcReifyRef.lean` | 1 |

Representative examples:
- `Bang/Core/EffectRow.lean:26:1` — `Bang.EffectRow.Label definition missing documentation string`
- `Bang/Backend/AbstractMachine.lean:116:1` — `Bang.CalcVM.SStore definition missing documentation string`
- `Bang/Core/Typing.lean:357:1` — `Bang.HasClauses inductive missing documentation string`

**Disposition: `fix-wave`, gated by `docs/notes/lean-comment-style.md`.** That doc already
adopted the Mathlib-grounded docstring convention (rule 1: `/-- … -/` on every def/theorem
with a contract-first first sentence) and named `docBlame` as the "optional enforcement
later" mechanism for exactly this gap. This IS that enforcement landing — the 310 findings
are the doc's already-acknowledged backlog, not a new discovery. A fix-wave should follow
that doc's rule 1 (contract sentence, not restating the code) rather than boilerplate
one-liners.

## unusedArguments (22 findings, 8 files) — `operator-call`

Examples:
- `Bang/Backend/Wasm.lean:228:1` — `Bang.compileHandler argument 1 x✝ : Bang.Handler`
- `Bang/Backend/Wasm.lean:2117:1` — `Bang.Wasmfx.HandlerEquiv argument 1 x✝¹ : Bang.Wasmfx.Module, argument 2 x✝ : Bang.Handler`
- `Bang/Core/Typing.lean:482:1` — `@Bang.WfInst argument 5 _q : Eff → Bang.CTy Eff Mult`

Mixed shape: several are typeclass-interface arguments (`Repr.repr`'s `prec` argument,
`Handler`-typed args on relation/equivalence definitions) that are structurally required by
the interface even when unused in the body — a common, often-correct pattern the linter
can't distinguish from a genuine dead parameter. Needs a human per-declaration call on
whether each is `@[nolint unusedArguments]`-worthy (interface shape) vs. an actual smell.

## defsWithUnderscore (17 findings, 2 files) — `nolint-candidates`

All examples are `deriving DecidableEq`-generated names (`decEq_3`, `decEq_4`, `decEq_5`)
on `Bang/Frontend/Surface.lean:316` (15 findings) and `Bang/Meta/LR.lean` (2 findings) —
compiler-synthesized declarations from a `deriving` clause, not hand-written identifiers.
These can't be renamed without touching the derive-generated naming scheme; the standard
disposition for this pattern is a `nolint` on the linter for the containing declaration
(or accept as a known false-positive class), not a rename.

## Linters with zero findings (13 of 16)

`dupNamespace`, `defLemma`, `checkUnivs`, `synTaut`, `unusedHavesSuffices`, `simpNF`,
`simpVarHead`, `simpComm`, `impossibleInstance`, `nonClassInstance`, `structureInType`,
`deprecatedNoSince`, `tacticDocs` — fully clean across all 49 modules.

## Shake (removable-import scan)

**Command note**: `lake exe shake Bang` (the plan's literal command) fails —
`Bang` is not a buildable module (no `Bang.lean` root barrel, retired #81; same reason
`bare lake lint` fails). `shake`'s CLI takes real module path(s) and (unlike `lake lint`)
genuinely unions multiple modules' closures — so it was run over the same 19-root set
proven in Step 1: `lake exe shake -- <19 root modules>` (the space-separated list `lint-lean`
carries in justfile). Rerun that command to reproduce the full findings below.

**26 files flagged** with a removable, replaceable, or re-homeable import. Representative
examples:

- `Bang/Core/EffectRow.lean`: remove `Mathlib.Data.Finset.Basic`, `Mathlib.Data.Finset.Sort`; add `Mathlib.Data.Finset.SDiff`
- `Bang/Meta/LR.lean`: remove `Bang.Core.Semantics`; add `Bang.Core.Semantics.Eval` (a more specific import than the umbrella module)
- `Bang/Frontend/TypeCheck.lean`: remove a duplicate `Bang.Frontend.Format` import (listed twice)
- `Bang/Frontend/Diagnostics.lean`, `Bang/Frontend/Query.lean`, `Bang/Frontend/Lint.lean`, `Bang/Frontend/Annotate.lean`, `Bang/Frontend/Rewrite.lean`: all show the same shape — a duplicate import of an already-covered Frontend module, replaceable by `Bang.Frontend.Surface` directly
- `Bang/Backend/Wasm.lean`: remove `Bang.Backend.U5bComplete` (no `add`, i.e. genuinely unused)

Pattern: many findings are **duplicate imports** (module listed twice) or an **umbrella
import where a narrower submodule import would do** (`Bang.Core.Semantics` →
`Bang.Core.Semantics.Eval`), not dead weight outright. Disposition: `fix-wave`, low risk
(mechanical import-line edits), but out of scope for this plan (`--fix` not run, per the
plan's explicit exclusion).

## Pole (build critical path) — UNAVAILABLE, not a STOP

`lake exe pole` fails: `error: unknown executable pole`. The pinned `importGraph` package
version only exposes two executables — `graph` (import-graph visualization: `.dot`/`.gexf`/
`.html`) and `unused_transitive_imports` — neither produces a per-file build-time critical-path
table. `pole` (the timing tool the plan expected) does not exist in this dependency pin.
Per the plan's own STOP conditions, absence is explicitly not a STOP; noted and moving on.

pole data would have been input to the god-file seam map (docs/notes/god-file-seams.md) —
the split that shortens the critical path buys build parallelism. Without `pole`, that
input is unavailable this round; `lake exe graph --to Bang.Audit` (already-wired) gives the
import *shape* but not per-file timing, and is a reasonable substitute if the operator wants
a fan-in view without a build-time signal. Getting real timing would need either a newer
`importGraph` pin (the tool exists in the upstream repo's later history, per plan's expected
command) or a hand-rolled parse of `lake build`'s per-file timing already visible in the raw
build log (`✔ [N/761] Built <module> (Xs)` lines) — both out of scope here.
