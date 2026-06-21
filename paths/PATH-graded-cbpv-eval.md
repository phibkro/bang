# PATH-graded-cbpv-eval — concretize Bang/Spec.lean to graded CBPV

> First blocker of ◊2. The path's original framing was "refactor Bang/Eval.lean",
> but reality diverged: `Bang/Eval.lean` (legacy K2 untyped CBN) stays as
> historical reference; the graded-CBPV definitions live in the new `Bang/Core`,
> `Bang/Syntax`, `Bang/Operational` modules instead.

## Seam
- **From checkpoint**: ◊1 (Reconciliation landed)
- **To checkpoint**: ◊2 (Kernel frozen v1)
- **Contract preserved**: existing K1 unifier proofs stay green; the legacy
  K2 reference (`Bang/Eval.lean`) and K3 calc machines stay green (they live
  in `Bang.Eval` namespace — no clash with new `Bang.*` modules).

## Layer
- [x] Kernel  [ ] Compiler  [ ] Surface  [ ] Meta

## Status

- [x] Started 2026-06-21
- [x] **Phase A part 1** landed: syntactic types (Val/Comp/Handler/VTy/CTy/Frame)
      concrete; build green; Lean v4.30; loogle wired.
- [x] **Phase A part 2** substantially complete:
      - Substitution helpers: Val.subst / Comp.subst / Handler.subst (mutual structural)
      - Ctx ops: Ctx.scale, Ctx.add (List-based)
      - isReturn
      - HasVTy + HasCTy (mutual inductive Props; 4 + 6 typing rules)
      - Source.step (substitution-based small-step, sizeOf-terminating)
      - Source.eval (fuel-iterated)
      - Q1 resolved: Eff algebra switched to `[Lattice Eff] [OrderBot Eff]`
      - Q2 resolved: Mult concretized as `Bang.QTT` with `CommSemiring` instance
      - Disjoint concretized via Mathlib's `_root_.Disjoint`
      - **8 axioms closed in Spec.lean (44 → 36)**
      - **Module split**: Spec.lean → Core / Mult / Syntax / Operational / LR /
        Compile / Spec (PRD)
- [ ] **In flight**: nothing — Phase A part 2 at a clean checkpoint
- [ ] **Blockers for full ◊2**: theorem PROOFS (defs done; bodies still `sorry`)

## Design decisions resolved this path

- **Grading convention**: Torczon (effect on U, coeffect on F). Switched from
  the wasmfx draft's inverted convention. Reason: only existing mechanized
  graded CBPV (plclub/cbpv-effects-coeffects) uses this; lemmas port cleanly.
- **Operational shape**: small-step + evaluation contexts (CK frames; Lexa
  OOPSLA'24 style). 7-of-9 surveyed effect-handler languages use this.
- **Eff algebra**: `[Lattice Eff] [OrderBot Eff]` (Q1 option a; resolved).
  Concrete: `Bang.EffRow := Finset Label`. Operators: `⊥`, `⊔`, `≤`.
- **Mult algebra**: `[Semiring Mult]`; concrete `Bang.QTT` (Q2 resolved).
- **Patterns / ADTs**: dropped from kernel core (surface concern, liquid).
- **Rewrite strategy**: in-place (no archival); legacy Eval kept as `Bang.Eval`
  namespace.

## What's still pending for full ◊2

Definitions are done. Theorem PROOFS are the remaining gap → Phase B
PROOF_ORDER #4 (STD block):

```
[ ] subst_value    proof body (currently sorry; axiom set already clean)
[ ] preservation   proof body
[ ] progress       proof body
[ ] type_safety    proof body  (uses Source.eval — concrete now)
[ ] no_accidental_handling   proof body + RowAll/WfInst/HandlesIntended
                             concretization (lacks-quantifier mechanism)
[ ] Concretize Trace = List Label, traceWithin = ⊆ semantics
                             (now possible with Lattice Eff)
[ ] Concretize NotEvaluated via Source.step reachability
                             (semantic predicate)
```

The STD block (preservation/progress/type_safety/subst_value) is the natural
next session — those theorems have CLEAN axiom sets (only `sorryAx` + the
trusted three kernel axioms). The Phase B `proof-engineer` subagent owns them.

## Notes (free-form working notes; deletable once path completes)

*Path doc cleared at session-end 2026-06-21; Phase A part 2 at clean
checkpoint. Resume with Phase B PROOF_ORDER #4 (STD block) — see
`docs/notes/spec-proof-discipline.md` for proof discipline.*
