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
- [x] **SOTA sweep landed (2026-06-21)**: literature reconciled; library
      reorganized; confirmations cited; WasmFX drift → Q9. Commit `d1aff27`.
- [x] **`subst_value` reframed (2026-06-21)**: the prior statement was vacuous
      (conclusion = hypothesis). Now states the real graded lemma (`Γ + ρ·Δ`,
      `c[v/x]`), sorry-backed. This exposed that the typing rules are
      grade-insensitive.
- [ ] **In flight — Phase B, Path B (resource-enforcing rules)**:
      - [ ] Q3-a: ADR — context rep → Finsupp grade-vec + type ctx
      - [ ] Re-shape `HasVTy`/`HasCTy` to thread + enforce grades
      - [ ] Prove `subst_value` → preservation/progress/type_safety
- [ ] **Blocker for full ◊2**: Q10 — typing rules carry grades but don't
      enforce them; `HasCTy` is grade-insensitive. Until upgraded, the graded
      `subst_value`, `zero_usage_erasable`, and `effect_sound` are unprovable.

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

⚠ **Correction (2026-06-21)**: the STD block is NOT "mechanical." The theorems
have clean axiom sets, but their proofs are blocked on Q10 — the typing rules
don't enforce grades, so `subst_value` (graded) and the grade-soundness
theorems are unprovable until the resource-enforcing rule upgrade lands. The
real PROOF_ORDER is: Q3-a (context rep) → rule upgrade → STD block.

## Notes (free-form working notes; deletable once path completes)

*2026-06-21 (later session): SOTA sweep landed + `subst_value` reframed.
Phase B started on Path B (resource-enforcing rules). Resume at the Q3-a ADR
(context rep → Finsupp grade-vec + type ctx), then re-shape the typing
judgments — see OPEN_QUESTIONS Q10 for the full plan, and the port source
`plclub/cbpv-effects-coeffects` → `resource/CBPV/typing.v` (Torczon Coq;
re-clone — see `references/README.md` → External resources).*
