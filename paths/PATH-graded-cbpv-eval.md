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
- [ ] In flight: Phase A part 2 (typing judgments, Ctx ops, Source.step concretization)
- [ ] Blockers: none yet
- [ ] Completed —

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

## Phase A part 1 — uncertainties to verify on first `lake build`

- `mutual` block for `Vrel/Srel/Krel/Crel` may need explicit
  `termination_by` hints (already noted as a comment in §5)
- `opaque` declarations with implicit-parameter-before-colon syntax
  (e.g. `opaque Disjoint {Eff : Type} : Eff → Eff → Prop`) — Lean 4
  syntax I'm fairly sure about, but unverified
- `VTy Eff Mult` and `CTy Eff Mult` parameter threading downstream;
  every theorem signature explicitly names them but Lean's elaborator
  may have inference quirks
- `Ctx` as a `List (Var × Mult × VTy Eff Mult)` abbrev — pattern matching
  on this in theorems may need `[(x, ρ, A)]`-style sugar
- `Source.step` references `Comp` not `(EvalCtx × Comp)` per Spec.lean's
  signature — Phase A part 2 will need to either change the signature
  or define a decomposition pass that splits/recombines

## Notes
*Design questions surface here as they arise; deletable once path completes.*
