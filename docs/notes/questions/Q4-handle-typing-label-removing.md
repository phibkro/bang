---
type: design-question
title: "`handle` typing rule: simplified vs label-removing"
description: "handler typing must discharge its label so the effect row shrinks at the handler"
status: decided
area: effects
resolved-by: ["ADR-0022", "ADR-0023"]
ties: ["Q1", "ADR-0021", "ADR-0022", "ADR-0023"]
see-also: []
---
**Resolution (2026-06-22)**: Both refinements landed. F-restriction (ADR-0021 C2) +
**label-removal**: `handleThrows` now DISCHARGES its label (`e ≤ labelEff ℓ ⊔ φ`, output `φ` —
ADR-0022 D4), and the corrected answer-type premise `opArg ℓ "raise" = some A` (ADR-0023) makes the
zero-shot abort type-preserving. The effect row shrinks at the handler, which is what `effect_sound`
will need. Historical update + deliberation below.

**Update (2026-06-22, ADR-0021, C2)**: the `handle` rule body was restricted from
general `B` to `CTy.F q A` — handlers handle *returners*. This was forced by
`progress` (a general-`B` `handle h (lam M')` is a stuck non-`ret` normal form).
The rule is STILL same-φ; the label-removing refinement below remains deferred and
will be forced by `effect_sound` (a handler must discharge its label for the static
effect to over-approximate the trace). So Q4 is half-resolved: F-restriction yes,
label-removal no.

**Question**: the current `HasCTy.handle` rule says the handled computation
has the SAME effect grade as the unhandled body. The "real" rule should
REMOVE the handler's handled label from the effect row.

**Detail**: current rule (Phase A part 2 first cut):
```
| handle : HasCTy Γ M φ B → HasCTy Γ (handle h M) φ B
```
Real rule (label-removing):
```
| handle : HasCTy Γ M (φ ⊎ {ℓ_of_h}) B → HasCTy Γ (handle h M) φ B
```

**Why it matters**: type safety + soundness depend on the handler actually
discharging an effect. Without removal, the effect row never shrinks.

**Blocked on**: depends on Q1 (Eff algebra) — "remove label from row"
requires concrete row operations.

**Revisit signal**: Phase B proof of `preservation` or `effect_sound`
fails because handler doesn't discharge.
