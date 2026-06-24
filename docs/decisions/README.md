# Architecture Decision Records

Each ADR records a decision a future session could otherwise reverse or relitigate: the **rationale**, the **rejected alternatives**, and a **"Revisit if"** clause that distinguishes legitimate reconsideration from drift. Read the relevant ADR before changing anything it covers.

## Layer taxonomy

ADRs are tagged by layer (see `../../ROADMAP.md`):
- **K** — kernel (semantic); near-permanent; deep review required to change
- **C** — compiler / methodology; stable statements, evolving implementations
- **S** — surface (liquid); experimental; cheap to write/delete

> **Recent culls:**
> - **ADR-0003** (own-the-runtime) and **ADR-0004** (calculated-VM-canonical) → deleted, subsumed by **ADR-0016** (two-hop architecture). See 0016 for the current position.
> - **ADRs 0010–0014** (per-machine K3 calculations) → collapsed into **ADR-0017** (K3 retrospective). The five were execution records; the retrospective preserves the load-bearing insights (composition map, methodology, shared-Value equality). The proofs themselves remain in `effectrow-oracle/oracle-lean/Bang/Calc*.lean`.
> - **ADRs 0005 and 0007** → rewritten as kernel-layer semantic principles (glyph specifics moved to the liquid surface layer; filenames refreshed).

> **The index below is GENERATED** from each ADR's frontmatter by
> `tools/gen-adr-index.py` (run `just adr-index`). Do not hand-edit between the
> markers — edit the ADR's frontmatter and regenerate. `just adr-check` fails the
> build if it drifts. Layer tags (K/C/P) live in each ADR's `**Layer**` bullet,
> not this table. Format: lightweight MADR; Status ∈ {Proposed, Accepted,
> Superseded, Deprecated}.

<!-- BEGIN GENERATED ADR INDEX — do not edit; run `just adr-index` -->

| # | Status | Title | Summary | Supersedes / Superseded-by | Amends / Amended-by | Resolves | Depends-on |
|---|---|---|---|---|---|---|---|
| [0001](0001-effect-rows-as-finset-semilattice.md) | Accepted | Effect rows are idempotent sets (a join-semilattice), modeled as `Finset` | Effect rows are idempotent sets (a join-semilattice), modeled as `Finset`. | — / — | — / — | — | — |
| [0002](0002-lean-over-fstar-for-the-oracle.md) | Accepted | Verify the reference in Lean 4 + Mathlib, not F\* | Verify the reference in Lean 4 + Mathlib, not F\* (agent-maintainable proofs). | — / — | — / — | — | — |
| [0005](0005-reactivity-as-operator-not-keyword.md) | Accepted | Reactivity is an operator distinction, not a separate kernel form | Reactivity is an operator distinction, not a separate kernel form (semantic; surface glyph liquid). | — / — | — / — | — | — |
| [0006](0006-explicit-tracked-capture.md) | Accepted | Capture is explicit and tracked; no implicit lexical closure | Capture is explicit and tracked; no implicit lexical closure. | — / — | — / — | — | — |
| [0007](0007-explicit-force-and-fixed-precedence.md) | Accepted | Force is always explicit; grouping ≠ forcing; operator precedence is global | Force is always explicit; grouping ≠ forcing; operator precedence is global (semantic; glyph liquid). | — / — | — / — | — | — |
| [0008](0008-eval-free-monad-handler-fold.md) | Accepted | The definitional `eval` is a fuel-bounded free-monad interpreter; handlers are a deep fold | The definitional `eval` is a fuel-bounded free-monad interpreter; handlers are a deep fold. | — / — | — / — | — | — |
| [0009](0009-calculated-vm-extrinsic-staged.md) | Accepted | The calculated VM is extrinsic and grown one constructor at a time, starting from an arithmetic kernel | The calculated VM is extrinsic and grown one constructor at a time, from an arithmetic kernel. | — / — | — / — | — | — |
| [0015](0015-continuation-reification-generalised-continuation-machine.md) | Accepted | Continuation reification — a flat generalised-continuation machine (`CalcReify`); multi-shot / non-tail handlers | Continuation reification — a flat generalised-continuation machine (`CalcReify`); CalcReifySim bisimulation paused per 0016 (the LR subsumes the goal). | — / — | — / — | — | — |
| [0016](0016-two-hop-architecture-calcvm-and-wasmfx.md) | Accepted | Two-hop architecture: graded-CBPV reference, CalcVM as executable spec, WasmFX as verified compiler target | Two-hop architecture: graded-CBPV reference, CalcVM as executable spec, WasmFX as verified compiler target. | 0003, 0004 / — | — / — | — | [0001](0001-effect-rows-as-finset-semilattice.md), [0002](0002-lean-over-fstar-for-the-oracle.md), [0015](0015-continuation-reification-generalised-continuation-machine.md) |
| [0017](0017-k3-calculated-machine-retrospective.md) | Accepted | K3 calculated-machine retrospective (supersedes ADRs 0010–0014) | K3 calculated-machine retrospective — composition-mechanism map + methodology; replaces the five per-machine ADRs. | 0010, 0011, 0012, 0013, 0014 / — | — / — | — | [0009](0009-calculated-vm-extrinsic-staged.md), [0008](0008-eval-free-monad-handler-fold.md) |
| [0018](0018-effect-row-lacks-constraints.md) | Accepted | Effect-row algebra — lacks-constrained row quantifiers (set discipline) | Effect-row algebra extended with lacks-constrained row quantifiers (set discipline); enables `no_accidental_handling`. | — / — | — / — | — | [0001](0001-effect-rows-as-finset-semilattice.md), [0016](0016-two-hop-architecture-calcvm-and-wasmfx.md) |
| [0019](0019-typing-context-split-gradevec-and-types.md) | Accepted | Typing context split — Finsupp grade-vector + ambient type context | Typing context split into a Finsupp grade-vector + ambient type context; enables the resource-enforcing rules. | — / — | — / [0020](0020-de-bruijn-representation.md) | Q3, Q10 | [0001](0001-effect-rows-as-finset-semilattice.md), [0016](0016-two-hop-architecture-calcvm-and-wasmfx.md) |
| [0020](0020-de-bruijn-representation.md) | Accepted | De Bruijn indices for the term representation | De Bruijn indices for the term representation — dissolves the named-encoding side-conditions; amends 0019's context split. | — / — | [0019](0019-typing-context-split-gradevec-and-types.md) / — | Q10, Q11 | [0019](0019-typing-context-split-gradevec-and-types.md) |
| [0021](0021-std-block-typing-corrections.md) | Accepted | Effect/grade typing corrections surfaced by the STD block | Effect/grade typing corrections surfaced by the STD block — makes preservation/progress/type_safety provable; advances Q4. | — / — | — / — | — | [0019](0019-typing-context-split-gradevec-and-types.md), [0020](0020-de-bruijn-representation.md) |
| [0022](0022-effect-operations-up-rule-and-handler-discharge.md) | Proposed | Effect operations: the `up` rule, operation signatures, and label-discharging `handle` | Effect operations: `up` rule + `EffSig` signatures + label-discharging `handle`; makes effect-soundness non-vacuous (D3 superseded by 0023). | — / — | — / — | Q4, Q5 | [0018](0018-effect-row-lacks-constraints.md), [0019](0019-typing-context-split-gradevec-and-types.md), [0020](0020-de-bruijn-representation.md), [0021](0021-std-block-typing-corrections.md) |
| [0023](0023-ck-machine-deep-handlers.md) | Accepted | The CK machine: deep handlers, and why `progress` needs a stack | CK machine for deep handlers — `Source.step` becomes config-level (`EvalCtx × Comp`); throws discards the captured continuation. | — / — | — / — | Q4, Q5, Q6, Q13 | [0020](0020-de-bruijn-representation.md), [0021](0021-std-block-typing-corrections.md), [0022](0022-effect-operations-up-rule-and-handler-discharge.md) |
| [0024](0024-abstraction-safety-monomorphic.md) | Accepted | Abstraction-safety: `no_accidental_handling` is correct-by-construction in a label-indexed machine | Abstraction-safety: `no_accidental_handling` restated faithfully + proven — correct-by-construction in the label-indexed machine. Closes the ◊2 gate. | — / — | — / — | — | [0018](0018-effect-row-lacks-constraints.md), [0023](0023-ck-machine-deep-handlers.md) |
| [0025](0025-resumptive-state-handler.md) | Accepted | Resumptive state handlers: the CK machine keeps the continuation, and the closed focus dissolves the grade tension | Resumptive state handler: `dispatch` keeps the captured continuation + reinstalls a deep `state ℓ s'` frame; the closed focus dissolves the grade tension. | — / — | — / — | Q12 | [0023](0023-ck-machine-deep-handlers.md), [0020](0020-de-bruijn-representation.md) |
| [0026](0026-correctness-ladder-and-checker-boundary.md) | Accepted | Correctness is a dispatched ladder; the kernel defines semantics, checkers are a pluggable layer | Correctness is a dispatched ladder (verified > tested > unsafe); the kernel defines semantics, checkers are a pluggable layer. Resolves the proof-power dial. | — / — | — / [0040](0040-laws-as-algebraic-interfaces-proof-first.md) | — | [0016](0016-two-hop-architecture-calcvm-and-wasmfx.md), [0024](0024-abstraction-safety-monomorphic.md) |
| [0027](0027-polymorphism-staged-monomorphic-v1.md) | Accepted | Polymorphism is staged: monomorphic v1 → Hindley-Milner → System F (+ effect-row + grade) | Polymorphism is staged: monomorphic v1 → Hindley-Milner → System F + effect-row + grade variables. | — / — | — / — | Q17 | [0026](0026-correctness-ladder-and-checker-boundary.md), [0001](0001-effect-rows-as-finset-semilattice.md) |
| [0028](0028-verified-core-tested-superset-stratification.md) | Accepted | Verified core + tested superset: the stratification principle (tooling · language · the meta-circular evaluator) | Verified core + tested superset, separated by an explicit seam — at three levels (correctness · tooling · language total/partial). | — / — | — / — | — | [0026](0026-correctness-ladder-and-checker-boundary.md), [0027](0027-polymorphism-staged-monomorphic-v1.md), [0002](0002-lean-over-fstar-for-the-oracle.md) |
| [0029](0029-iso-recursive-adts.md) | Accepted | Iso-recursive ADTs (sum + product + μ) for the data layer | Iso-recursive ADTs (sum + product + μ with `fold`/`unfold`); inductive only; μ-vars ≠ polymorphism. | — / — | — / — | Q18 | [0027](0027-polymorphism-staged-monomorphic-v1.md), [0026](0026-correctness-ladder-and-checker-boundary.md), [0028](0028-verified-core-tested-superset-stratification.md) |
| [0030](0030-stm-as-transactional-handler.md) | Accepted | STM enters as a transactional handler in v1; privilege is concurrency-only | STM enters v1 as a transactional handler — NO new kernel primitive; privilege (shared heap) is concurrency-only and deferred. | — / — | — / — | — | [0025](0025-resumptive-state-handler.md), [0023](0023-ck-machine-deep-handlers.md), [0001](0001-effect-rows-as-finset-semilattice.md), [0018](0018-effect-row-lacks-constraints.md), [0026](0026-correctness-ladder-and-checker-boundary.md), [0016](0016-two-hop-architecture-calcvm-and-wasmfx.md) |
| [0031](0031-calcvm-resumptive-state.md) | Accepted | CalcVM resumptive state: `evalD` threads a store and services ops inline; the machine RESUMES with a non-discarding `OP` (shape A stays, one-shot) | CalcVM resumptive state: `evalD` threads a label-keyed store servicing ops inline; the machine RESUMES with a non-discarding `OP` (shape A stays). | — / — | — / — | — | [0025](0025-resumptive-state-handler.md), [0030](0030-stm-as-transactional-handler.md), [0023](0023-ck-machine-deep-handlers.md), [0016](0016-two-hop-architecture-calcvm-and-wasmfx.md) |
| [0032](0032-group-recovers-retired.md) | Accepted | `group_recovers` RETIRED — rollback is a handler mechanism, not an effect-algebra inverse | `group_recovers` RETIRED — the rollback law is false-as-`≈`, vacuous, and redundant; v1 rollback is the txn handler. Supersedes 0018's group-row. | — / — | — / — | Q8 | [0018](0018-effect-row-lacks-constraints.md), [0030](0030-stm-as-transactional-handler.md), [0031](0031-calcvm-resumptive-state.md), [0001](0001-effect-rows-as-finset-semilattice.md) |
| [0033](0033-lr-relations-row-indexed.md) | Accepted | The LR relations are indexed by the effect row ε (faithful Biernacki τ/ε) | The LR relations are indexed by the effect row ε (faithful Biernacki τ/ε); a faithful tightening of the Phase-A stub. | — / — | — / — | — | [0021](0021-std-block-typing-corrections.md), [0023](0023-ck-machine-deep-handlers.md), [0016](0016-two-hop-architecture-calcvm-and-wasmfx.md) |
| [0034](0034-lr-fundamental-env-closed.md) | Accepted | `lr_fundamental` is the env-closed (open-term) fundamental theorem; the bare `c c` is its `Γ=[]` corollary | `lr_fundamental` amended to the env-closed (open-term) form; the bare `c c` becomes its `Γ=[]` corollary `lr_fundamental_closed`. | — / — | — / — | — | [0033](0033-lr-relations-row-indexed.md), [0023](0023-ck-machine-deep-handlers.md), [0016](0016-two-hop-architecture-calcvm-and-wasmfx.md) |
| [0035](0035-lr-for-equivalence-simulation-for-compilation.md) | Accepted | Biorthogonal LR for equivalence (◊4); annotated simulation for compilation (◊5) | Biorthogonal LR proves ◊4's contextual-equivalence theorems; AsmFX-style annotated simulation is the method for ◊5's `compile_forward_sim`. | — / — | — / — | — | [0016](0016-two-hop-architecture-calcvm-and-wasmfx.md), [0033](0033-lr-relations-row-indexed.md), [0034](0034-lr-fundamental-env-closed.md) |
| [0036](0036-lr-closed-value-carrier.md) | Accepted | LR closed-value carrier: enforced at Krel/Srel quantification, not EnvRel alone | LR closed-value carrier enforced at `Krel`/`Srel` quantification (not `EnvRel` alone); unblocks `closeC_subst_comm` + the binder cases. | — / — | — / — | — | [0034](0034-lr-fundamental-env-closed.md), [0033](0033-lr-relations-row-indexed.md), [0025](0025-resumptive-state-handler.md), [0030](0030-stm-as-transactional-handler.md), [0016](0016-two-hop-architecture-calcvm-and-wasmfx.md) |
| [0037](0037-abstract-correctness-implementation-performance.md) | Accepted | Abstract model fights for correctness; implementation fights for performance under contract (+ the shared-nothing concurrency invariant) | Abstract model fights for correctness; implementation for performance under contract; the concurrency runtime is shared-nothing. | — / — | — / — | — | [0016](0016-two-hop-architecture-calcvm-and-wasmfx.md), [0035](0035-lr-for-equivalence-simulation-for-compilation.md), [0030](0030-stm-as-transactional-handler.md), [0026](0026-correctness-ladder-and-checker-boundary.md), [0028](0028-verified-core-tested-superset-stratification.md) |
| [0038](0038-cbpv-arrow-observation-peeling-krel.md) | Accepted | CBPV arrow observation in the biorthogonal LR: peeling `Krel(arr)` + returner-restricted empty-stack adequacy | CBPV computation-typed arrows in the LR: a PEELING/existential `Krel` arrow clause + returner-restricted empty-stack adequacy. | — / — | — / — | — | [0034](0034-lr-fundamental-env-closed.md), [0036](0036-lr-closed-value-carrier.md), [0033](0033-lr-relations-row-indexed.md), [0035](0035-lr-for-equivalence-simulation-for-compilation.md), [0016](0016-two-hop-architecture-calcvm-and-wasmfx.md) |
| [0039](0039-cap4-non-triangleright-split.md) | Accepted | ◊4 split: LR foundation lands for the non-▷ fragment; the ▷-subsystem (μ + resumptive handlers) → ◊4.5 | ◊4 split — the LR foundation lands sorry-free for the non-▷ fragment; the cohesive ▷-subsystem (μ · `up` · resumptive handlers) defers to ◊4.5. | — / — | — / [0041](0041-cap45-recursive-fragment-needs-later-modality.md) | — | [0038](0038-cbpv-arrow-observation-peeling-krel.md), [0036](0036-lr-closed-value-carrier.md), [0034](0034-lr-fundamental-env-closed.md), [0033](0033-lr-relations-row-indexed.md), [0035](0035-lr-for-equivalence-simulation-for-compilation.md), [0030](0030-stm-as-transactional-handler.md), [0016](0016-two-hop-architecture-calcvm-and-wasmfx.md) |
| [0040](0040-laws-as-algebraic-interfaces-proof-first.md) | Accepted | Laws as first-class algebraic interfaces; proof-first discharge (amends ADR-0026) | Surface laws are first-class, enforced algebraic interfaces; discharge is proof-first → test → assert. Amends 0026's test-default. | — / — | [0026](0026-correctness-ladder-and-checker-boundary.md) / — | Q19 | [0026](0026-correctness-ladder-and-checker-boundary.md), [0027](0027-polymorphism-staged-monomorphic-v1.md), [0029](0029-iso-recursive-adts.md), [0016](0016-two-hop-architecture-calcvm-and-wasmfx.md) |
| [0041](0041-cap45-recursive-fragment-needs-later-modality.md) | Accepted | ◊4.5: the LR's recursive fragment requires a `▷` (later) modality | ◊4.5 — the LR's recursive fragment (μ · `up` · resumptive handlers) requires a ▷ (later) modality; build-proven + literature-confirmed. | — / — | [0039](0039-cap4-non-triangleright-split.md) / — | — | [0039](0039-cap4-non-triangleright-split.md), [0038](0038-cbpv-arrow-observation-peeling-krel.md), [0036](0036-lr-closed-value-carrier.md), [0035](0035-lr-for-equivalence-simulation-for-compilation.md), [0034](0034-lr-fundamental-env-closed.md), [0033](0033-lr-relations-row-indexed.md) |
| [0042](0042-adr-currency-generated.md) | Accepted | The ADR decided-ledger is generated from frontmatter (drift unrepresentable) | The ADR index + resolved-questions ledger is GENERATED from per-ADR frontmatter; onboarding consults the generated ledger before opening a design question. | — / — | — / — | — | [0026](0026-correctness-ladder-and-checker-boundary.md) |

### Resolved questions (derived from ADR `Resolves:` fields)

| Question | Resolved by |
|---|---|
| Q3 | [0019](0019-typing-context-split-gradevec-and-types.md) |
| Q4 | [0022](0022-effect-operations-up-rule-and-handler-discharge.md), [0023](0023-ck-machine-deep-handlers.md) |
| Q5 | [0022](0022-effect-operations-up-rule-and-handler-discharge.md), [0023](0023-ck-machine-deep-handlers.md) |
| Q6 | [0023](0023-ck-machine-deep-handlers.md) |
| Q8 | [0032](0032-group-recovers-retired.md) |
| Q10 | [0019](0019-typing-context-split-gradevec-and-types.md), [0020](0020-de-bruijn-representation.md) |
| Q11 | [0020](0020-de-bruijn-representation.md) |
| Q12 | [0025](0025-resumptive-state-handler.md) |
| Q13 | [0023](0023-ck-machine-deep-handlers.md) |
| Q17 | [0027](0027-polymorphism-staged-monomorphic-v1.md) |
| Q18 | [0029](0029-iso-recursive-adts.md) |
| Q19 | [0040](0040-laws-as-algebraic-interfaces-proof-first.md) |

<!-- END GENERATED ADR INDEX -->

## Canonical exemplar

**Read `0016-two-hop-architecture-calcvm-and-wasmfx.md` first when writing
a new ADR.** It exhibits the format we want: Context (1-3 paragraphs),
Decision (concrete + actionable), Why this model (numbered list of
reasons), What it commits to (the consequences), Consequences for other
ADRs (subsumptions/deletions), Rejected alternatives (each with "why
not"), Revisit if (the legitimate reconsideration triggers).

Template stub: `adr-template.md` in this directory (or copy 0016 and edit).

## When to write an ADR

- The choice is reversible by a future session — without an ADR, they
  WILL reverse it.
- The "why" is non-obvious from the code alone.
- Rejected alternatives are worth recording (saves re-thinking).
- The decision spans multiple files / subsystems.

Skip ADRs for: bug fixes, refactors that don't change semantics, formatting,
typo fixes. Those go in commit messages.
