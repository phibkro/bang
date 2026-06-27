# Scoped capabilities — the #18 (drop-VcapFree) design record

> Design analysis, NOT a decision. Captures the `scopedcap-design` pass (2026-06-27) for when
> task #18 ("make raw source `vcap` untypeable / drop the `VcapFree` precondition") is tackled.
> Reference: arXiv:2207.03402, Boruch-Gruszecki/Brachthäuser/Lee/Lhoták/Odersky,
> *Scoped Capabilities for Polymorphic Effects* (CC<:□ / capturing types). Add to `references/refs.bib`.

## Why this exists: there is NO v1 soundness hole

The `stateEscape` witness (`Bang/StateEscapeWitness.lean`, axiom-clean `stateEscape_not_typeable`)
proved that capability-escape-via-state is **behaviourally real but HasCTy-UNTYPEABLE today**. So
`type_safety` holds as stated for v1. The escape is blocked — it's a confirmed *guard*, not a hole.

**Every guard leans on `VcapFree`.** Three escape channels, three different guards:

| channel | guard in force | VcapFree-dependence |
|---|---|---|
| answer-return | B-occ `¬LabelOccurs ℓ A` (ADR-0057) | YES — B-occ alone leaves a raw dangling `vcap` typeable |
| arrow/dead-return | grade `b ∧ decide(q≠0)` (ADR-0060) | operates under the VcapFree diagonal |
| state-cell | closed-state `HasVTy [] [] s₀ S` (ADR-0025) + VcapFree | YES, explicitly |

State mechanism: a cap-typed cell `S = cap ℓ` is inhabited only by a literal `vcap`; `handleState`
forces `HasVTy [] [] s₀ S` ⟹ `s₀` is a literal `vcap` ⟹ VcapFree rejects it. The two guards compose;
neither alone suffices. **The hole opens only when VcapFree is dropped (#18).**

## Verdict: ADDITION for #18, REPLACEMENT (full CC<:□) for post-v1

- **#18 minimal path — the cap-free-cell ADDITION.** A premise `∀ℓ ¬LabelOccurs ℓ S` on
  `handleState`/`stateF` makes `S = cap ℓ` untypeable *directly via `LabelOccurs`*, independent of
  closed-state/VcapFree — the state-channel analog of B-occ (the avoidance "shadow" on the cell, as
  B-occ is the shadow on the answer type). **It is an ADDITION**, a third static premise alongside
  B-occ + grade; it unifies/retires nothing. For #18 each channel's VcapFree-leg is replaced
  per-channel: 3 channels → 3 premises. Cost: **~1 session, syntactic, reuses `LabelOccurs`**, threads
  the inc-5 LR the way B-occ did. Build-confirm with a BoccSpike-pattern probe before ratifying.

- **post-v1 REPLACEMENT — full CC<:□.** One capture-set discipline subsumes all three guards
  *natively*: answer-avoidance ⊇ B-occ; capture-prediction `cv` (paper Lemma 4.11/4.14) ⊇
  grade-liveness (CC<:□'s `cv` *is* ADR-0060's liveness rebuilt — `cv(app (lam…)(…cap…))` drops the
  dead cap by rule (app), exactly `escapeB_app`); reference-dependent capture sets ⊇
  closed-state+VcapFree (the §5.2 stack-allocation example — a cell carries a capture set; avoidance
  rejects a cell outliving a stored cap's scope). It also drops VcapFree AND buys re-handleable stored
  caps + effect polymorphism. **Cost ≥ the whole inc-5 effort**: needs subtyping (the kernel has none
  — `lam` dropped `Qle`), reference-dependent `VTy` (caps as tracked variables not raw values), and
  boxing for polymorphic tunneling. = ADR-0057 option C, gated on ADR-0027.

The three premises (B-occ, grade, cap-free-cell) are **forward-compatible** with full CC<:□ — each is
the empty-capture-set / monomorphic special case.

## Regression oracles (any change must keep all three untypeable + `#guard`-stuck)
`Bang/StateEscapeWitness.lean::stateEscape` (state) · `Bang/BoccRegress.lean::escapeB` (surface) ·
`escapeB_app` (arrow). Under the cap-free-cell ADDITION, `stateEscape` becomes untypeable via the
cap-free-`S` premise *independently of VcapFree*; `escapeB`/`escapeB_app` are untouched.

## Method caveat
The paper's metatheory is a surface calculus with subtyping + capture polymorphism; our kernel is
intrinsic + CK-machine. The de-risk verdict (from `scopedcap-design`) is that the #18 ADDITION stays a
**syntactic induction, not a logical relation** — it's a `LabelOccurs` premise like B-occ. Full CC<:□
is the larger lift. Cost/tractability figures are estimates from the design pass, not build-confirmed.
