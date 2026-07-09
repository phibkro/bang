# ADR-0091 · #50: structOK multi-arg certification — single-fixed-slot descent

<!-- adr-frontmatter -->

- **Status**: Proposed
- **Summary**: `structOK` (#47) certifies single-arg structural recursion as total (⊥-row, no `Div`); multi-arg/accumulator recursion — the shape the tokenizer dogfood deliberately AVOIDED (`ce6d738`) — still conservatively types `Div` even when descent is plainly structural. The design note (`docs/notes/structok-multiarg-design.md`, code-grounded at TypeCheck.lean:1608-1662/:1728-1734/:1690-1694, gap verified LIVE against fresh main) surfaces a genuine fork. **Decision: (A) single-fixed-slot descent — exactly ONE designated argument position, the SAME slot at every recursive call site, must be a strict data subterm at each call; all other slots (accumulators) ride free.** Covers both corpus shapes (curried accumulator, tuple accumulator) at cost proportional to the existing checker (~55 lines generalized pair→n-indexed list + the shadowing-arm port). Soundness posture preserved by construction: the check is n copies of the already-sound bare-variable single-slot rule, and fixing ONE slot across all call sites forecloses the one known break (two per-site measures each idle on the other's turn); false-certification stays impossible, not merely unlikely. The five adversarial guards port to curried/tupled form as the regression corpus. **Rejected**: (B) full lexicographic descent — no corpus example needs it, real annotation/inference cost, cuts against the ADR-0088 explicit-over-inferred precedent; NOT foreclosed ((A) is (B) with slot-list length 1 — layer it later if a genuine zip/merge-shaped two-structural-argument case surfaces). (C) numeric well-founded measures — out of scope, tracked behind Q31.
- **Depends-on**: 0073, 0088
- **Relates-to**: #50 (tracker), #47 (the certifier this extends), Q31 (numeric measures), `docs/notes/structok-multiarg-design.md` (the full design note this ADR promotes)

## Status

Proposed (2026-07-09, promoted from the str49 lane's design note same day) — awaiting operator
ruling. Implementation is one bounded `TypeCheck.lean` unit once ruled; the letRecRow curried
wall (:1728-1734) and the structOK call-site check (:1608-1662) are the two edit sites, with
splitS's existing shadow-threading (:1690-1694) reused for the tuple case.

## Context, decision detail, options, and soundness argument

This ADR promotes the fork; the substance lives in the design note (single source of truth):
`docs/notes/structok-multiarg-design.md` — evidence that the gap is live (both naive
accumulator shapes RUN correctly but type `Int ! {Div}` on fresh main), the three root-cause
sites, the (A)/(B)/(C) analysis, and the §3 soundness argument. Read it before implementing
or re-litigating.

## Invariant compliance

- Elaborator-only; kernel census untouchable by construction (same posture as ADR-0088).
- Conservative-by-construction is PRESERVED: anything the extended rule cannot certify keeps
  `Div` — the failure direction stays "under-certify", never "over-certify".

## Revisit if

- A genuine two-structural-argument program (zip/merge-shaped) appears in the corpus → layer
  (B) as a slot-list extension of (A); the rep forecloses nothing.
- Q31 lands numeric types with a well-founded order → (C) becomes stateable; separate ADR.

## Evidence

`docs/notes/structok-multiarg-design.md` (the promoted note, `65ce49c`), `ce6d738` (the
tokenizer landing commit naming the avoided shape), TypeCheck.lean:1608-1662/:1728-1734/
:1690-1694 (the three sites), TypeCheck.lean:2995-3013 (the adversarial guard set that ports).
