---
type: design-question
title: "Eff algebra: Semiring vs Lattice"
description: "effect algebra — switched to Lattice+OrderBot (⊥ / ⊔ / ≤); rows are a join-semilattice"
status: decided
area: effects
ties: ["Q8", "ADR-0001", "ADR-0032"]
see-also: ["Bang/Core/EffectRow.lean"]
---
**Resolution**: Switched `[Semiring Eff]` → `[Lattice Eff] [OrderBot Eff]`
across all modules (Core / Syntax / Operational / LR / Spec). The effect
algebra is now:
  - `⊥`     = no effects (empty row)
  - `e₁ ⊔ e₂` = combined effects (join)
  - `≤`      = effect inclusion (sub-effecting)

Concrete: `Bang.EffRow := Finset Label` (in `Bang/Core/EffectRow.lean`).
Mathlib gives Finset the required Lattice + OrderBot instances natively.

Knock-on effects:
- `HasCTy.ret` and `HasCTy.lam`: `0 (CTy.F ...)` → `⊥ (CTy.F ...)`
- `HasCTy.letC`: effect combine `φ₁ + φ₂` → `φ₁ ⊔ φ₂`
- `no_accidental_handling`: `l * e` → `l ⊔ e`
- `Disjoint` now concrete via Mathlib's `_root_.Disjoint` for Lattice
  + OrderBot (was axiom — closed)
- `group_recovers`'s `[AddGroup Eff]` hypothesis is vacuous for our Lattice
  Eff (no nontrivial Lattice + AddGroup instance) — theorem **RETIRED** (ADR-0032),
  not preserved; v1 rollback is the txn handler. See Q8 (resolved-but-bounded).
