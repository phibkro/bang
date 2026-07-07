---
type: design-question
title: "`effect_sound`: what does the trace observe?"
description: "the trace semantics under which effect_sound is both TRUE and meaningful"
status: open
area: meta
ties: ["ADR-0023", "ADR-0024"]
see-also: []
---
**Question**: `effect_sound` states `HasCTy [] [] c e (F q A) → evalTrace fuel c = done (v,t) →
traceWithin t e` — the static effect `e` over-approximates the observed trace `t`. With what trace
semantics is this both TRUE and meaningful?

**Why it matters**: it's a ◊2-block soundness theorem (the dynamic counterpart of the static effect
discipline). Currently `sorry` (not the ◊2 *gate*, which is `no_accidental_handling`).

**Detail (the tension, ADR-0023/0024)**: in the deep-handler machine, `e` bounds only the operations
that **escape** `c`'s own handlers, NOT those handled internally. `handle (throws ℓ)(… raise ℓ …)`
performs `raise ℓ` during evaluation, but ℓ is discharged by `c`'s handler, so `labelEff ℓ ⊄ e`. So:
- trace = **all dispatched labels** ⇒ `traceWithin t e` is FALSE (internal handling hides labels from `e`).
- trace = **escaping labels only** ⇒ for a program that runs to `done`, nothing escaped (an escaping op
  is stuck, not `done`), so `t = []` and the theorem is trivially true but vacuous.

**Options**: (1) trace logs `(label, handled-by-depth)` and `traceWithin` checks each label against the
effect *at the point it was performed* (the focus effect, which preservation bounds) rather than the
top-level `e`; (2) a two-level statement: internal labels ⊆ (labels discharged by `c`'s handlers),
escaping labels ⊆ `e`; (3) instrument `evalTrace` to log only at the program boundary and prove the
(weak) escaping-bound. (1) is the most informative.

**Blocked on**: choosing the trace semantics (a design decision, like ADR-0024 was for
`no_accidental_handling`). The CK machine makes either tractable (each DISPATCH is an observable point).

**Revisit signal**: taking up `effect_sound` / `Trace` concretization after the ◊2 gate.
