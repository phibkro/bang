---
type: design-question
title: "`up` typing rule + opArgTy/opResTy"
description: "the perform/up typing rule + per-(label,op) effect signatures (EffSig)"
status: decided
area: effects
resolved-by: ["ADR-0022", "ADR-0023"]
ties: ["ADR-0022", "ADR-0023"]
see-also: ["Bang/Core/Typing.lean"]
---
**Resolution (2026-06-22)**: Landed. Per-`(Label, OpId)` signatures via the `EffSig`
typeclass; the `up` rule in `Bang/Core/Typing.lean`. ADR-0023 D6 made `opArg`/`opRes` **op-partial**
(`Label → OpId → Option VTy`, `none` = not in the label's interface); the `up` rule now requires
`opArg ℓ op = some A` / `opRes ℓ op = some B`. `preservation`/`progress`/`type_safety` are proven
axiom-clean over the CK machine (ADR-0023), so the rule is non-vacuously exercised. Original
deliberation preserved below.

**Question**: the `HasCTy.up` constructor was OMITTED in Phase A part 2
because it depends on `opArgTy` and `opResTy` (which are still axioms in
§5 LR helpers).

**What we'd want**:
```
| up : ℓ ∈ φ → HasVTy Γ v (opArgTy ℓ) → HasCTy Γ (up ℓ op v) φ (F q (opResTy ℓ))
```

**Blocked on**: concrete `opArgTy` / `opResTy` (needs an effect signature
registry; either built into Eff or carried separately).

**Revisit signal**: cannot type-check programs that use `perform` (i.e.,
literally any effectful program).
