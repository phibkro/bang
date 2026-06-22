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

| # | layer | decision | status | depends on |
|---|---|----------|--------|------------|
| [0001](0001-effect-rows-as-finset-semilattice.md) | K | Effect rows are idempotent sets (join-semilattice), modeled as `Finset` | Accepted | — |
| [0002](0002-lean-over-fstar-for-the-oracle.md) | C | Verify the reference in Lean 4 + Mathlib, not F\* | Accepted | 0001 |
| [0005](0005-reactivity-as-operator-not-keyword.md) | K | Reactivity is an operator distinction, not a separate kernel form (semantic; surface glyph liquid) | Accepted | — |
| [0006](0006-explicit-tracked-capture.md) | K | Capture is explicit and tracked; no implicit lexical closure | Accepted | 0016 |
| [0007](0007-explicit-force-and-fixed-precedence.md) | K | Force is always explicit; grouping ≠ forcing; precedence is global (semantic; surface glyph liquid) | Accepted | 0005, 0006 |
| [0008](0008-eval-free-monad-handler-fold.md) | K | Definitional `eval` is a fuel-bounded free-monad interpreter; handlers are a deep fold | Accepted | 0016, 0001, 0006, 0007 |
| [0009](0009-calculated-vm-extrinsic-staged.md) | C | Calculated VM is extrinsic and grown one constructor at a time, from an arithmetic kernel | Accepted | 0016, 0008 |
| [0015](0015-continuation-reification-generalised-continuation-machine.md) | C | Continuation reification — flat generalised-continuation machine (`CalcReify`); CalcReifySim bisimulation **paused** per ADR-0016 (LR subsumes the goal) | Accepted | 0017, 0009 |
| [0016](0016-two-hop-architecture-calcvm-and-wasmfx.md) | K+C | Two-hop architecture: graded-CBPV reference, CalcVM as executable spec, WasmFX as verified compiler target (subsumes 0003 + 0004) | Accepted | 0001, 0002, 0015 |
| [0017](0017-k3-calculated-machine-retrospective.md) | C | K3 calculated-machine retrospective — preserves composition-mechanism map and methodology insights; replaces 0010–0014 | Accepted | 0009, 0008 |
| [0018](0018-effect-row-lacks-constraints.md) | K | Effect-row algebra extended with lacks-constrained quantifiers (set discipline); enables `no_accidental_handling` | Accepted | 0001, 0016 |
| [0019](0019-typing-context-split-gradevec-and-types.md) | K | Typing context split into a Finsupp grade-vector + ambient type context (resolves Q3, enables the Q10 resource-enforcing rules) | Accepted (partially superseded by 0020) | 0001, 0016 |
| [0020](0020-de-bruijn-representation.md) | K | De Bruijn indices for the term representation — dissolves 5 named-encoding side-conditions (4 machine-checked falsities); resolves Q11 | Accepted | 0019, Torczon OOPSLA'24 |
| [0021](0021-std-block-typing-corrections.md) | K | Effect/grade typing corrections surfaced by the STD block — lam carries body effect, handle restricted to F-bodies, Mult→CommSemiring, progress at F-type; makes preservation/progress/type_safety provable; advances Q4 | Accepted | 0019, 0020, Torczon OOPSLA'24 |
| [0022](0022-effect-operations-up-rule-and-handler-discharge.md) | K | Effect operations: `up` typing rule + `EffSig` operation signatures + label-discharging `handle` + progress/type_safety at `⊥`; makes effect-soundness non-vacuous. Resolves Q5, completes Q4. Unit 1 landed; Units 2–3 staged. **D3 superseded by 0023** | Proposed | 0018, 0019, 0020, 0021 |
| [0023](0023-ck-machine-deep-handlers.md) | K | CK machine for deep handlers — `Source.step` becomes config-level (`EvalCtx × Comp`); throws discards the captured continuation. Supersedes ADR-0022 D3 (progress-at-`⊥` under the shallow substitution step was machine-checked false); resolves Q6 (throws case). Corrects the `handleThrows` answer-type premise | Accepted | 0020, 0021, 0022, Levy CBPV |
| [0024](0024-abstraction-safety-monomorphic.md) | K | Abstraction-safety: `no_accidental_handling` restated faithfully (the ∀-`h` placeholder was vacuous) + proven — correct-by-construction in the label-indexed machine; `WfInst` concretized to carry the lacks-constraint (`rowinst_requires_disjoint` proven). Closes the ◊2 gate. `effect_sound` deferred (trace-semantics Q14) | Accepted | 0018, 0023 |

Format: lightweight MADR. Status ∈ {Proposed, Accepted, Superseded by NNNN, Deprecated}.

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
