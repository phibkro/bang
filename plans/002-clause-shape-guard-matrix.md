# Plan 002: Build a systematic clause-shape #guard matrix over the handler-elaboration gate

> **Executor instructions**: Follow this plan step by step. Run every
> verification command and confirm the expected result before moving to the
> next step. If anything in the "STOP conditions" section occurs, stop and
> report — do not improvise. When done, update the status row for this plan
> in `plans/README.md` — unless a reviewer dispatched you and told you they
> maintain the index.
>
> **Drift check (run first)**: `git diff --stat f1cb2cf..HEAD -- Bang/Frontend/TypeCheck.lean`
> If the file changed since this plan was written, compare the "Current state"
> excerpts against the live code before proceeding; on a mismatch, treat it as
> a STOP condition.

## Status

- **Priority**: P1
- **Effort**: M
- **Risk**: LOW (purely additive `#guard`s)
- **Depends on**: plans/001-nested-same-effect-handler-oracle.md (soft — 001's example is a useful pattern; not a hard blocker)
- **Category**: tests
- **Planned at**: commit `f1cb2cf`, 2026-07-10

## Why this matters

Four elaborator bugs of one family have been found and fixed in this codebase (issues #85/#86 plus two siblings): an inner elaboration ran **without threading the binder/effects context** (`Γ` or the `effects` table), and the failure was *silent* — hidden whenever the tested input was atomic enough to short-circuit the broken path. Each was found by accident (a user program one step past the examples), and each cost real debugging time.

The existing `#guard` corpus for the `handle … with` surface (ADR-0095) pins a handful of specific programs — three clause-body shapes. It is spot coverage. The bug family predicts where the next member hides: at some untested combination of *nesting depth × operation position × clause/handler configuration*. This plan replaces spot coverage with a small systematic matrix (~30 guards), so a context-threading regression fails the compiled-guard gate at `lake build` speed instead of surviving to a user report.

## Current state

- `Bang/Frontend/TypeCheck.lean` (5740 lines at `f1cb2cf`) — the checker + elaborator. The `#guard` corpora live near the bottom of the file.
- The Stage-7 surface corpus starts at the section header at **line 5319** (verbatim excerpt so you can locate it after drift):

```lean
/-! ### ADR-0095 D1 (RULED) `handle e with Name as h { … }` — the REAL SURFACE corpus (#21
s7probe/#44 Stage 7 e2e battery). Kernel-adjacent complement to `examples/handle-custom-*`
(the run-oracle gate, `tools/check-examples.sh`): these `#guard`s pin the TYPE-CHECK verdicts and
the D4 teaching diagnostic, catching a regression at `just check`/compiled-`#guard` speed rather
than only at the slower example-run gate. `checkProg`/`checkAndLower` are the SAME production
pipeline `bang check`/`bang run` use (no separate test-only path). -/
```

- Guard idiom used throughout that region (model yours on the guards you find below line 5319; a parse-level specimen from line 5303):

```lean
#guard (match Bang.Surface.parseProg "let resume = 5 in resume" with
        | .error _ => true | .ok _ => false)
```

  Type-level guards in the 5319+ corpus go through `checkProg`/`checkAndLower` on the parsed program — read that corpus before writing anything; reuse its exact helper calls and its comment style (each guard prefixed by a `--` comment naming WHAT semantic fact it pins, not what the code does).

- The known bug family, so the matrix targets the right axes (this is the intelligence of the plan — keep it):
  1. `elabBind` — ran an inner inference with an empty `effects` table; fired on A-normalized user-effect performs like `net.fetch(1) + 1` (a *compound* operand — atomic operands short-circuited the bug).
  2. `anfSplit`/`zonkInferC` — same class; fixed by adding an `effects` parameter (see the doc comment at `TypeCheck.lean:890-897`).
  3. `elabHClauses` (issues #85/#86) — clause bodies elaborated without the clause parameter in `Γ` at certain shapes; single-op effects worked, multi-op broke.
  4. `curryBind` — curried parameters past the first lost context.
- Language gotchas for authoring matrix programs:
  - Reserved op names/binders (rejected at parse/buildEnv): `get`, `put`, `raise`, `new`, `read`, `write`, `resume`, `with`. Use names like `fetch`, `send`, `poll`.
  - Clause bodies are BARE expressions: `fetch(n) => n * 10` — no braces.
  - Effect decls: `effect Net { fetch : Int -> Int, send : Int -> Int }`.
  - Compiled `#guard`s (via `lake build`) are the reliable check; `lake env lean` `#eval` output is NOT reliable in this repo — never gate on it.

## Commands you will need

| Purpose | Command | Expected on success |
|---|---|---|
| Enter dev shell | `nix develop` | banner |
| Fast single-file check (seconds–minutes) | `nix develop --command just check Bang/Frontend/TypeCheck.lean` | `✓ no errors or warnings` |
| Compiled guard gate | `nix develop --command lake build` | exit 0 (a failing `#guard` is a compile error) |
| Full gate | `nix develop --command just verify` | exit 0 |

Gate-trap (repo rule): read errors via the exit code or `grep -E "error"` — plain `grep "error:"` misses `error(lean.unknownIdentifier):`.

## Scope

**In scope**:
- `Bang/Frontend/TypeCheck.lean` — **additive `#guard`s and `--` comments only**, appended inside/after the ADR-0095 D1 corpus section (below line 5319). No changes to any `def`, `theorem`, or existing guard.
- `plans/README.md` (status row)

**Out of scope** (do NOT touch):
- Any elaborator/checker `def` — if a matrix cell FAILS, that's a discovered bug: STOP and report (see below), do not fix it inline.
- Any file under `Bang/Core/`, `Bang/Spec.lean`, `Bang/Meta/`, `Bang/Backend/` (kernel/proof strata — invariant: kernel untouched by surface work).
- `examples/` (run-oracle coverage is plan 001's lane).

## Steps

### Step 1: Read the existing corpus

Read `Bang/Frontend/TypeCheck.lean` from line 5319 to the end of file. Note: (a) the exact `checkProg`/`checkAndLower` invocation shape used for *typing* verdicts (vs. the parse-only `parseProg` shape), (b) the comment convention, (c) which shapes are ALREADY pinned so the matrix doesn't duplicate them (at minimum: bodies `n * 10`, `n * 3 + 1`, `(n * 3) + 1` and the resume-reservation guards).

**Verify**: you can state the helper used for a "this program TYPES successfully" guard before writing any new guard.

### Step 2: Author the matrix

Append a new subsection after the existing corpus:

```lean
/-! ### Clause-shape MATRIX (plan 002) — systematic coverage of the silently-missing-binder
family's predicted hiding places: nesting depth × op position × clause/handler configuration.
Each axis value appears in at least one ACCEPTED program; the matrix is a regression net for
context-threading (Γ / effects-table) in clause elaboration, not a semantics spec. -/
```

Then guards covering the cross-product, ~30 cells. Axes and required values:

| Axis | Values to cover |
|---|---|
| ops per effect | 1, 2, 3 |
| clause-body payload | bare binop (`n * 10`); nested binop depth 3 (`((n + 1) * 2) + (n * 3)`); `let … in` body; body calling the *other* op's result position (2-op effect where clause for `a` has body using its param inside a compound: `a(n) => (n * 2) + 1` while `b(m) => m`); a body containing a lambda applied immediately |
| perform-site position | atomic operand (`h.fetch(1)`); compound left operand (`h.fetch(1) + 2`); compound right operand (`2 + h.fetch(1)`); nested in `let` RHS; inside a thunk that is forced (`$({h.fetch(1)})` — if this shape is v1-expressible; drop the cell if parse fails and note it) |
| handler config | single handler; two clauses in decl order; two clauses in REVERSE decl order (the #86 shape); handler param used at binder position 1 and position 2 of a 2-arg op if multi-arg ops are v1-expressible — if `fetch : Int -> Int -> Int` fails to parse or elaborate, record the cell as N/A in a comment instead |

Every cell: one `#guard`, one preceding `--` comment naming the cell (e.g. `-- matrix: 2-op effect, reverse clause order, compound-left perform site`). Expected verdict for all cells is ACCEPT (types + lowers) unless the cell exercises a documented rejection (the D4 ret-shape restriction, ADR-0095 — if a cell trips D4, pin it as a *rejection with the teaching diagnostic* instead, modeling on the D4 guards already in the corpus).

**Verify** after every ~8 guards: `nix develop --command just check Bang/Frontend/TypeCheck.lean` → `✓ no errors or warnings`. (Incremental verification localizes a failing cell immediately.)

### Step 3: Count and gate

Add a final comment stating the matrix size (e.g. `-- matrix: 32 cells, all compiled`). Run the compiled gate.

**Verify**: `nix develop --command lake build` → exit 0. Then `nix develop --command just verify` → exit 0.

## Test plan

The guards ARE the tests. Coverage target: every axis value above appears in ≥1 guard; the #86 regression shape (multi-op, reverse clause order) and the elabBind regression shape (compound operand around a perform) each have a dedicated named cell.

## Done criteria

- [ ] ≥25 new `#guard`s in the matrix subsection, each with a naming comment
- [ ] The #86 shape (multi-op + reverse clause order) and the elabBind shape (compound operand) are present and named
- [ ] `nix develop --command lake build` exits 0
- [ ] `nix develop --command just verify` exits 0
- [ ] `git diff` touches only the guard section of `Bang/Frontend/TypeCheck.lean` (no `def`/`theorem` lines — the pre-commit statement-change detector must NOT fire)
- [ ] `plans/README.md` status row updated

## STOP conditions

Stop and report back (do not improvise) if:

- **Any matrix cell fails that you expected to ACCEPT.** That is a live bug of the target family — the whole point of the matrix. Report: the exact program string, the diagnostic, and which axes the cell sits at. Do NOT delete the cell, mark it "expected-fail", or fix elaborator code.
- More than 3 cells hit parse errors on syntax this plan assumed expressible — the plan's syntax assumptions have drifted; report which.
- `just check` on the file starts taking dramatically longer (>5 min) — guard-count may be hitting an elaboration cliff; report before adding more.
- Anything requires touching a `def` or a file outside scope.

## Maintenance notes

- When the explicit `resume(w)` form lands (issue #93 reservation), extend the matrix with resume-position cells rather than starting a new corpus.
- The generative complement (mutation-based fuzzing via `Bang/Witness/ElabFuzz.lean`, 462 lines, already in-tree) was deliberately deferred: the matrix gives named, debuggable cells first; wire fuzz mutations over the same axes as a follow-up once the matrix is green.
- Reviewer should scrutinize: that failed cells were reported, not silently dropped — the matrix's value is exactly the cells that DON'T pass.
