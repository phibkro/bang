# 0105 — effect_sound trace semantics: the runtime live-bound (Q14 ruling)

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: `effect_sound` (`Bang/Spec.lean:191`, a ◊2-block soundness theorem) was flagged with three
  BARE `axiom`s — `Trace`, `Source.evalTrace`, `traceWithin` (`Bang/Core/Semantics/Eval.lean`) — parked on
  Q1 (a concrete `Eff`). Q1 is RESOLVED (`[Lattice Eff] [OrderBot Eff]`, ADR-0018), so the axioms become
  concrete DEFINITIONS. But concretizing them forces the still-open **Q14** (what trace semantics makes
  `effect_sound` both TRUE and non-vacuous). DECISION (operator-sanctioned, 2026-07-12): adopt Q14
  **option (1)** — the informative per-dispatch bound — realized via the **runtime live-bound**
  `liveBound K e := e ⊔ ⨆{labelEff h.label | handleF h ∈ K}` (config-side, no preservation/LR). The trace
  records `(label, liveBound K e)` at each DISPATCH; `traceWithin t := ∀ (ℓ,φ) ∈ t, labelEff ℓ ≤ φ`. This
  is a **frozen-statement change** (evalTrace gains the residual arg; traceWithin drops its Eff arg).
- **Date**: 2026-07-12
- **Deciders**: operator (H3 lane)
- **Ties**: ADR-0018 (Q1 resolved), ADR-0023/0024 (deep-handler discharge), Q14 (`docs/notes/questions/Q14-effect-sound-trace-observation.md`)
- **Supersedes**: the three bare `axiom`s (retired)

## Context

`effect_sound` states: `HasCTy [] [] c e (F q A) → evalTrace fuel c = done (v,t) → traceWithin t e`
— the static effect `e` over-approximates the observed effect trace. The three trace symbols were
`axiom`s because a concrete `Eff` was needed to express "label in row". That blocker (Q1) is gone,
but the semantics of `t`/`traceWithin` (Q14) was never decided.

## The decision

Concretize the three axioms as defs and take Q14 option (1) via the runtime bound. Four defs replace
the three axioms (`Bang/Core/Semantics/Eval.lean` §effect-trace):

```
abbrev Trace (Eff)     := List (Label × Eff)          -- (dispatched label, runtime live bound)
def liveBound          : EvalCtx → Eff → Eff          -- e ⊔ ⨆{labelEff h.label | handleF h ∈ K}
def Config.runTrace    := Config.run + a passenger    -- appends (ℓ, liveBound K e) at DISPATCH
def Source.evalTrace fuel c e := Config.runTrace fuel (0,[],c) e []
def traceWithin t      := ∀ (ℓ,φ) ∈ t, labelEff ℓ ≤ φ
```

`Source.eval`/`Config.run` are BYTE-IDENTICAL (the invariant-#1 oracle is untouched; `runTrace` is a
sibling). Frozen-statement change on `Spec.lean:191`: `evalTrace fuel c` → `evalTrace fuel c e` (the
whole-program residual seeds the bound); `traceWithin t e` → `traceWithin t` (the per-dispatch Eff
now lives inside each trace entry).

## Rejected alternatives (both machine-refuted — do-not-weaken witnesses)

The two obvious semantics fail. Both refutations are runnable in `Bang/Witness/EffectTraceWitness.lean`
(`Eff = Finset Label`, `labelEff ℓ = {ℓ}`):

- **(A) naive `trace = all dispatched labels`, `traceWithin t e := ∀ ℓ ∈ t, labelEff ℓ ≤ e`** — **FALSE**.
  The `handleThrows`/`handleState` typing rules DISCHARGE a handled label from the residual `e` (body at
  `e ≤ labelEff ℓ ⊔ φ`, block residual `φ` with `ℓ` removed). Witness: `handle (throws 1) (raise 1)` at
  top-level `e = ∅` runs to `done`, dispatches label 1, yet `labelEff 1 = {1} ⊄ ∅`. The witness records
  `(1, {1} ⊔ ∅)` and machine-checks `¬ ({1} ≤ ∅)`.
- **(B) `trace = escaping labels only`, `t ⊆ e`** — **VACUOUS**. An escaping op (`idDispatch = none`) runs
  to `escapedCap`, NOT `done`; so on a `done` run the escaping trace is empty and the theorem is trivially
  true but says nothing.

Option (1) via the runtime bound is TRUE and non-vacuous: the nested witness
`handle (throws 1) (handle (throws 2) (raise 1))` at `∅` records `(1, {2} ⊔ {1} ⊔ ∅)` — the bound tracks
EVERY live handler frame, so each internal dispatch is a real checked obligation.

## Why the runtime bound (not preservation-threading)

The performed-at effect looks like a TYPING fact (the stack carries no effect annotations). It is NOT
needed: handler frames carry their labels at runtime (`handleF n h`, `h.label` — dispatch reads them;
the typing-by-label / dispatch-by-identity split guarantees labels are runtime-present). So the live
bound `e ⊔ {live handler labels}` is computed purely config-side by the passenger — a SUPERSET of the
true focus residual, and exactly what `traceWithin` needs. The discharge is then a machine induction
(a dispatched `ℓ` resolves to a `handleF` frame on `K` with label `ℓ`, so `labelEff ℓ ≤ liveBound K e`)
with NO preservation and NO logical relation — it never approaches the parked `lr_*` territory.

### What the theorem GUARDS (its refutation content — not true-by-construction)

`effect_sound` couples two INDEPENDENTLY-computed things: `runTrace` records the label `ℓ` from the
CAPABILITY (`perform (vcap n ℓ)` — the label the cap *claims*), while `liveBound` folds labels from the
HANDLER FRAMES (`handleF n h` — via `h.label`). These agree only because dispatch is FAIL-LOUD:
`idDispatch` fires iff `handlesOp h ℓ op = true`, which forces `h.label = ℓ` (`handlesOp_label`). So the
theorem certifies **dispatch/liveBound coherence — a recorded label is always the label of a LIVE frame
that actually handled it.** The `HasCTy` premise is unused because this coherence is an operational
property of the fail-loud dispatcher, not of the static type.

**The falsifying bug-shape** (machine-witnessed, `Bang/Witness/EffectTraceWitness.lean`): a cap
`vcap 0 2` claiming label 2, id-matching a `throws 1` frame (label 1). WITH the guard this run
ESCAPES (`idDispatch = none → escapedCap`, never `done`), so it records nothing coherence-violating —
`effect_sound` holds. WITHOUT the `handlesOp` guard (the pre-ADR-0054 identity-ONLY silent-wrong
dispatch), the same program would reach `done` recording `(2, liveBound = {1})` with `2 ∉ {1}`, and
`effect_sound` would be **FALSE**. That is the machine bug the theorem catches: a dispatcher that
routes a cap to a frame whose label it does not carry. The runtime bound being "computed from the same
frames dispatch walks" is the point — the theorem checks that dispatch's identity-match and the
frame's label-content agree, which is a real, breakable invariant (it broke, pre-0054).

## Consequences

- `effect_sound`'s axiom set: `[sorryAx, Trace, traceWithin, Source.evalTrace]` → `[propext, Quot.sound]`
  (the three bare axioms retired AND the body discharged; ⊆ trusted-3, fully clean).
- The discharge (`runTrace_traceWithin`, `Bang/Core/Semantics/Eval.lean`) is a machine induction via
  `Config.runTrace.induct` — NO preservation, NO logical relation, never approaching the parked `lr_*`.
  The `HasCTy` premise is NOT needed (the runtime bound is typing-independent); it stays on the
  statement for the intended reading.
- Q14 moves from OPEN to RESOLVED (this ADR).
- The trace is now a usable artifact for downstream tooling (the dynamic counterpart of the static
  effect discipline).

## References

- Full design + Phase-2 discharge plan: [`docs/notes/effect-sound-refoundation.md`](../notes/effect-sound-refoundation.md).
- The refuted alternatives as runnable witnesses: `Bang/Witness/EffectTraceWitness.lean`.
- The open question this closes: [`docs/notes/questions/Q14-effect-sound-trace-observation.md`](../notes/questions/Q14-effect-sound-trace-observation.md).
