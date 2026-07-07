---
type: design-question
title: "Open-term substitution: capture-avoiding subst vs de Bruijn"
description: "open-term graded substitution — de Bruijn makes variable capture structurally impossible"
status: decided
area: meta
resolved-by: ["ADR-0020"]
ties: ["ADR-0020"]
see-also: []
---
**Resolution**: **Option C — de Bruijn.** The named encoding produced FOUR
more machine-checked falsities while proving `subst_value` (capture,
grade-freshness, context-wf, bound-var-grade, non-deterministic lookup) — five
structural side-conditions for one lemma, each free under de Bruijn. Switched the
term representation to de Bruijn indices; **ADR-0020**. Option A (closed
side-condition) was the in-force stopgap that surfaced the full cost. Original
deliberation preserved below.

---

**Question**: `Comp.subst` is **not capture-avoiding** (Operational.lean §subst,
scoped to "closed-program reductions"). The graded substitution lemma
`subst_value` is therefore only true with a closedness side-condition (currently
`v` typed in the empty type context). How do we eventually support **open-term**
substitution — needed for the *interesting* graded case where the substituted
value carries its own resource demands (`γ_Δ ≠ 0`)?

**Why it matters**: the closed-`v` `subst_value` suffices for `type_safety`
(closed programs) but trivializes the grade arithmetic (`ρ·γ_Δ = ρ·0 = 0`). The
full coeffect payoff — substituting open values while tracking their usage — and
`preservation` for a *general* context both want open-term substitution.

**Detail** — the unconditional open lemma is FALSE under non-capture-avoiding
subst. Counterexample: `[vvar y / x](lam y. ret (vvar x)) = lam y. ret (vvar y)`
— the free `y` of the substituted value is captured by `lam y`.

**Options** (from the 2026-06-21 decision; A chosen for now):
- **A — closedness side-condition** *(in force)*. `subst_value` requires `v`
  closed. Cheap, true, unblocks the STD block. Trivializes grades for `v`.
- **B — capture-avoiding `Comp.subst`**. α-rename binders (fresh-name supply +
  α-equivalence machinery over named vars). True in general; a real sub-project.
- **C — de Bruijn representation**. Capture structurally impossible (Torczon's
  choice via autosubst2). Most robust; a ◊3-scale rewrite of syntax/subst/eval.

**Blocked on**: nothing now (A unblocks the STD block). Revisit when open-term
graded reasoning is needed.

**Revisit signal**: a coeffect theorem (or `preservation` for non-empty `Γ`)
that needs `subst_value` with `γ_Δ ≠ 0`; or the ◊3 CalcVM port, where a de
Bruijn switch (C) could be folded in.
