---
type: design-question
title: "Ctx representation: List vs FinMap"
description: "typing-context representation — split into a Finsupp grade-vector + a type context (Torczon-style)"
status: decided
area: meta
resolved-by: ["ADR-0019"]
ties: ["Q10", "ADR-0019"]
see-also: []
---
**Resolution**: Forced active by Q10 (resource-enforcing rules need "grade ρ at
`x`, 0 elsewhere", which `List`+`zipWith` can't express). **Split** the context
into a Finsupp grade-vector `Var →₀ Mult` + an ambient type context
`List (Var × VTy)`, mirroring Torczon's `gradeVec`/`context`. Mathlib's
`Finsupp` supplies total `+`, `•`, and `single`. See **ADR-0019**. The original
deliberation is preserved below.

---

**Question**: is the current `List (Var × Mult × VTy)` representation good
enough, or should `Ctx` be a `FinMap Var (Mult × VTy)`?

**Why it matters**: `Ctx.add Γ₁ Γ₂` currently uses `List.zipWith` which
requires matching variable lists in matching order. A FinMap representation
handles arbitrary contexts cleanly.

**Options**:
1. Keep List + zipWith. Document the precondition (matching shape).
   Proofs work for "well-formed pairs"; harder when contexts diverge.
2. Switch to FinMap. Cleaner arithmetic; richer typeclass requirements
   (decidable Var equality, ordering for canonicalization).
3. Switch to a custom `Multiset (Var × Mult × VTy)` or similar.

**Recommended**: (1) for now. Switch to (2) if/when proofs surface the
need (typical Phase B compat lemmas may demand arbitrary Γ₁ + Γ₂).

**Blocked on**: nothing. Defer until proofs demand.

**Revisit signal**: a Phase B compat lemma that can't be stated cleanly
under the current Ctx representation.
