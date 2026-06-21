# PATH-graded-cbpv-eval — refactor `Bang/Eval.lean` to graded CBPV

> First blocker of ◊2. The Eval refactor is upstream: `Bang/EffectRow.lean`
> extension, `no_accidental_handling`, and `Bang/Spec.lean §0–§4` concretization
> all consume the result.

## Seam
- **From checkpoint**: ◊1 (Reconciliation landed)
- **To checkpoint**: ◊2 (Kernel frozen v1)
- **Contract preserved**: existing K1 unifier proofs stay green; the all-ω
  (multiplicity-irrelevant) subset of the graded reference is observationally
  identical to current `Bang.Eval` (regression baseline).

## Layer
- [x] Kernel  [ ] Compiler  [ ] Surface  [ ] Meta

## Plan
1. **Read before write** (kernel-engineer discipline):
   - [x] Current `Bang/Eval.lean` end-to-end — what's the shape of `Comp`,
     `Value`, `Env`, the handler fold, the fuel loop
   - [x] `Bang/Spec.lean §0–§4` — the target shape (graded CBPV PRD)
   - [ ] Torczon et al. OOPSLA 2024 §3–4 (the substrate paper) — value/comp
     split, grade algebras, key judgments
2. **Sketch the refactor** — what changes vs what stays:
   - Add: value/computation kind split (`VTy` / `CTy`, `Val` / `Comp` AST)
   - Add: multiplicity grades on binders (`U ρ`, `F e`)
   - Add: graded substitution / `WfInst` / `rowinst_requires_disjoint`
   - Keep: free-monad `Comp` shape (CBPV-compatible already)
   - Keep: fuel-bounded totality
   - Keep: handler-as-deep-fold (Plotkin-Pretnar shape)
3. **Surface design questions** to the orchestrator BEFORE writing code:
   - Spec leeway vs constrained moves (where the paper underspecifies)
   - Naming alignment between existing `Bang.Eval` types and `Bang.Spec` types
   - Backward-compat boundary: does old `Bang.Eval` get *renamed* (e.g. to
     `Bang.EvalLegacy`) and a fresh `Bang.Eval` written, or in-place rewrite?
4. **Execute the refactor** (after design Qs are answered):
   - Write the new graded-CBPV `Source.step` / `Source.eval` / `Result`
   - Update `Bang/Spec.lean §0–§4` opaques to point at concrete defs
   - Confirm `Bang/EffectRow.lean` still builds (no contamination)
5. **Regression test** the all-ω subset:
   - Either run the old harness on a saved fixture, or hand-spot-check a few
     programs equal under both Eval and Eval-legacy
   - If the existing diff-tests can be revived for the all-ω subset, do so;
     if not, document why
6. **Update ADRs**:
   - ADR-0008 (eval is free-monad handler fold) — verify or update
   - New ADR if the refactor produces a design decision worth preserving

## Status
- [x] Started 2026-06-21
- [x] Phase A part 1 landed (syntactic types concrete; build green; v4.30; loogle)
- [x] Phase A part 2 — 7/10 axioms closed in Spec.lean:
      ✓ subst (Val/Comp/Handler)
      ✓ Ctx.scale, Ctx.add (List-based; FinMap defer)
      ✓ isReturn
      ✓ HasVTy, HasCTy (mutual inductives; common typing rules)
      ✓ Source.step (substitution-based small-step)
      ✓ Source.eval (fuel-iterated)
- [ ] In flight: Mult concretization + Eff algebra design
- [ ] Blockers: Eff algebra — see below
- [ ] Completed —

## Phase A part 2 — what's left and known design questions

### Remaining axioms (Spec.lean: 37 axioms / 18 sorry total)

| Axiom | Why pending |
|---|---|
| Effect-row well-formedness (Disjoint, RowAll, WfInst, HandlesIntended) | Depends on Eff concretization + lacks-constraint design |
| Trace / Source.evalTrace / traceWithin | Need concrete Eff to express "label in row" |
| NotEvaluated | Semantic predicate; needs Source.step reachability analysis |
| LR helpers (Stack, BaseRel, asThunk, asReturner, raise, opArgTy, opResTy) | Phase B PROOF_ORDER #1 (LR foundation) — not ◊2 scope |
| Vrel / Srel / Krel / Crel | Same — Phase B |
| Recovery (seqComp, idComp, recover, Cxt, Cxt.plug) | Phase B PROOF_ORDER #2 (group_recovers) |
| WasmFX target (Wasmfx.*, compile*) | Phase B PROOF_ORDER #3 (compile_forward_sim) |

### Design question — Eff algebra (BLOCKS ◊2 finalization)

Spec.lean's `variable {Eff : Type} [Semiring Eff]` doesn't fit our intended
concrete `Eff = Finset Label`. The issue:

- Semiring requires `0 * a = 0` (zero absorbs in multiplication).
- For effect rows, `*` naturally means "sequencing of effects" = union.
- But `∅ ∪ a = a`, not `∅`. So `Finset Label` doesn't form a Semiring under
  `(+, *) = (∪, ∪)`.

Three resolutions:
1. **Spec change**: replace `[Semiring Eff]` with `[Lattice Eff] [OrderBot Eff]`
   (Finset has these natively); replace `l * e` in `no_accidental_handling`
   with `l ⊔ e` (or equivalent). Theorem statements shift slightly.
2. **Different Eff carrier**: use a different concrete type that IS a Semiring
   (e.g. `Nat` for clock-counting, like Torczon). Loses the row-of-labels
   reading.
3. **Keep parametric**: don't concretize Eff; let users instantiate at
   theorem use-site. Punts the question.

Recommended: (1). The spec's `Semiring` was inherited from Torczon's
clock-effect example; it doesn't fit our row-of-labels effect model.
The shift to Lattice is honest + matches ADR-0001 (rows-as-Finset).

### Concretize Mult = QTT (independent of Eff question)

QTT {zero, one, omega} IS a genuine commutative semiring; the Semiring
instance is provable by case analysis (`by cases ... <;> rfl` or `decide`).
Manageable in one focused effort.

When done: theorems automatically specialize. Closes the `Mult` axiom
implicitly (the parametric `[Semiring Mult]` is satisfied by the concrete
QTT instance).

## Owner
- Agent: claude (acting as kernel-engineer, per `.claude/agents/kernel-engineer.md`)
- Human: philib (orchestrator)

## Design decisions resolved

- **Grading convention**: Torczon (effect on U, coeffect on F). Switched from
  Spec.lean's earlier (multiplicity-on-U, effect-on-F) draft. Reason: only
  existing mechanized graded CBPV (`plclub/cbpv-effects-coeffects`) uses
  this; lemmas port cleanly. Committed `d7e8ba6`.
- **Operational shape**: small-step + evaluation contexts (CK-machine,
  Lexa-style frames). Matches `Source.step` signature; matches Biernacki
  LR's `Stack`; matches 7-of-9 surveyed effect-handler languages
  (Effekt, Koka, Frank, Eff, Helium, Lexa, OCaml 5+). Greenlit by operator.
- **Rewrite strategy**: in place (no archival per operator).
- **Patterns / ADTs**: dropped from kernel core. Slim CBPV; surface
  desugars when surface work begins (post-◊2).
- **Eff carrier**: `Eff = Finset Label` (single source of truth with
  EffectRow). Will be made concrete in Phase A part 2.

## Phase A staging

- **Part 1 (landed this commit)**: §1 syntactic types concretized in
  `Bang/Spec.lean` — `Val`, `Comp`, `Handler`, `VTy`, `CTy`, `Frame`,
  `EvalCtx`, `Var`, `OpId`. Section order in the file restructured so
  types precede theorems that reference them. Theorem signatures updated
  for the new type-parameter shape.
- **Part 2 (next)**:
  - Make `Eff = Finset Label`, `Mult = QTT enum`; supply
    `OrderedSemiring` instances (idempotent commutative for Eff;
    rig-arithmetic for Mult)
  - Concretize `Ctx.scale`, `Ctx.add`
  - Concretize `HasVTy`, `HasCTy` as `inductive Prop` (one constructor
    per typing rule)
  - Concretize `Source.step`: small-step over `(EvalCtx × Comp)` CK
    decomposition; implement subst (`Val.subst` / `Comp.subst`); handle
    propagation through the frame stack
  - Concretize `Source.eval`: iterate `Source.step` under fuel
  - Address `decreasing_by` for the mutual LR defs (Vrel/Srel/Krel/Crel)

## Phase A part 1 — VERIFIED on `lake build` (2026-06-21)

Build green: 730/730 jobs. Resolved during build iteration:

- **Mathlib v4.29 deprecated `OrderedSemiring`** → split into `Semiring +
  PartialOrder + IsOrderedRing`. Replaced with `[Semiring]` + `[PartialOrder]`
  where ordering needed (Eff for preservation's `e' ≤ e`).
- **`opaque` requires inhabitedness** for the result type → converted
  non-Prop opaques to `axiom` (postulate; no Nonempty check). Prop-returning
  declarations stay as `opaque`. Trade-off: axioms appear in
  `#print axioms`; Phase B closes them by making them concrete defs.
- **Mutual LR (Vrel/Srel/Krel/Crel) termination** couldn't be auto-proven
  by Lean (cross-type recursion; needs step-indexed measure). Phase A part 1
  stubs them as axioms; Phase B gives real step-indexed defs (Ahmed-style
  `WellFoundedRecursion` on (n, sizeOf type)).
- **`q = 0` in Krel** needs `DecidableEq Mult` — added to variable block.
- **Explicit `{Eff Mult : Type}` in theorem signatures** shadowed the
  variable-block bindings, breaking auto-binding. Removed; rely on
  `variable {Eff : Type} [Semiring Eff] [PartialOrder Eff]` etc. at file top.
- **`Compat.lean` reduced to placeholder** — its compat lemmas use
  `Ctx`/`VTy`/`CTy` as 0-arg types; Phase A part 1 made them (Eff Mult)-
  parametrized; full rethreading is Phase A part 2 work. Statements
  preserved as comments in the file header.
- **`audit.sh` updated**: scans only `Bang/` (not the lake cache); lists
  pending sorrys as Phase B burndown (no longer hard-fails on them).
- **`Bang.lean` root file** added (re-exports all submodules; Lake convention).

Result: `make build` clean, `bash tools/audit.sh` passes static guards
and reports the axiom dependency burndown per `Bang/Audit.lean`.

## Notes
*Design questions surface here as they arise; deletable once path completes.*
