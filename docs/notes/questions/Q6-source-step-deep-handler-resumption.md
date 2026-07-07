---
type: design-question
title: "Source.step's deep-handler resumption"
description: "deep-handler operational semantics = the CK machine; throws resolved, state threading → Q12"
status: partial
area: effects
resolved-by: ["ADR-0023"]
ties: ["Q12", "ADR-0023"]
see-also: []
---
**Resolution (2026-06-22, ADR-0023)**: `Source.step` is now a **CK machine** over
`Config = EvalCtx × Comp` (option 2 below — the `Frame`/`EvalCtx` infra). `up` dispatch scans the
frame stack for the nearest catching handler; the **throws** (zero-shot) case discards the captured
continuation and aborts with the payload. `preservation`/`progress`/`type_safety` re-proven
axiom-clean over it. The **state** (resumption) case still uses the same scan but must KEEP the
captured continuation and thread the stored state — deferred to **Q12** (graded state). Original
deliberation preserved below.

**Question (historical)**: the substitution-based `Source.step` returned `none` (stuck) when
`handle h (up ℓ op v)` didn't match. The "correct" behavior for deep handlers is to
propagate `up` outward while the inner handler is preserved for the
resumption.

**Why it matters**: real algebraic-effect programs nest handlers and
resume across multiple handler frames. Current Source.step can't model
this.

**Options**:
1. Keep substitution-based; accept it can't handle deep resumption. Use a
   different operational semantics for that.
2. Migrate to a CK-machine: `Source.step` operates on `EvalCtx × Comp`.
   The `Frame` ADT (§1.3) is already defined for this. Handler propagation
   captures the prefix-context as the resumption.
3. Add explicit continuation reification (CalcReify-style); Comp.up
   carries the captured continuation as data.

**Recommended**: (2) when proofs need deep handlers. The Frame / EvalCtx
infrastructure is already there.

**Blocked on**: nothing. Just session time to migrate.

**Revisit signal**: writing test programs that demonstrate handler
nesting, or Phase B proofs of `compile_forward_sim` for multi-handler
programs.
