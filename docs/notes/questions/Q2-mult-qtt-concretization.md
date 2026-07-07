---
type: design-question
title: "Mult = QTT concretization"
description: "concretize the multiplicity semiring as QTT (0/1/ω); the spec stays parametric in Mult"
status: decided
area: type-system
ties: []
see-also: ["Bang/Core/Grade.lean"]
---
**Resolution**: Concretized as `Bang.QTT` in `Bang/Core/Grade.lean`. CommSemiring
instance via case analysis (3 enum elements; proofs by `cases <;> rfl`).
Build green on first try, smoke-tested via `tools/eval.sh`.

The spec stays parametric in `[Semiring Mult]`; QTT is one valid instance
(the bang-lang default per ROADMAP.md). Phase B proofs may specialize to
QTT or stay parametric depending on what the proof needs.
