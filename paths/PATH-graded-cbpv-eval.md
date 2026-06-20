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
- [ ] In flight: reading current Eval + Spec, then surfacing design Qs
- [ ] Blockers: none yet
- [ ] Completed —

## Owner
- Agent: claude (acting as kernel-engineer, per `.claude/agents/kernel-engineer.md`)
- Human: philib (orchestrator)

## Notes
*Design questions surface here as they arise; deletable once path completes.*
