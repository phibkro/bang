---
type: design-question
title: "Typing rules must enforce grades (resource discipline)"
description: "make HasVTy/HasCTy resource-enforcing (thread + check grades) — the QTT-payoff gate"
status: decided
area: type-system
resolved-by: ["ADR-0019", "ADR-0020"]
ties: ["Q3", "ADR-0019", "ADR-0020"]
see-also: ["Bang/Spec.lean"]
---
**Resolution**: Done. The rules now thread + enforce grades (Path B / ADR-0019),
and after the de Bruijn switch (ADR-0020) the carrier is positional `List Mult`
rather than the Finsupp this entry assumed — `subst_value` is proven on it
(`e00ee9a`, axiom-clean). The original deliberation (which still names the
`Var × Mult × VTy` named context) is preserved below as the historical record.

**Question**: `HasVTy` / `HasCTy` carry a multiplicity in each context binding
(`Var × Mult × VTy`) but **never thread or check it**. Should they be upgraded
to be resource-enforcing (Torczon-faithful), so the grade actually constrains
typing?

**Why it matters**: this is the gate for the entire grade-soundness story —
the QTT payoff. Surfaced 2026-06-21 while fixing `subst_value`, which was
*vacuous* (conclusion = hypothesis). The real graded substitution lemma is now
stated (`Bang/Spec.lean`) but **unprovable** until the rules thread grades; the
same gap blocks `zero_usage_erasable` and `effect_sound`. Without this, ◊2
"kernel frozen v1" is not actually met — `HasCTy` is grade-insensitive.

**Detail** — the divergence from Torczon (`/tmp` clone of
plclub/cbpv-effects-coeffects, `resource/CBPV/typing.v`):

```
                TORCZON (resource-enforcing)        BANG (Phase-A first cut)
variable        T_Var i: γ i = Qone,                vvar: (∃ ρ, (x,ρ,A) ∈ Γ)
                  ∀ j≠i, γ j = Qzero                 └ ρ existential — IGNORED
return          T_Ret q V: γ = q Q* γ1              ret: Γ untouched
application     T_App: γ = γ1 Q+ (q Q* γ2)          app: same Γ for M and v
subsumption     T_VSub: γ Q<= γ'                    (none)
```

Torczon grades via a per-variable `gradeVec` (γ : fin n → Q); we fold the grade
into the context `List (Var × Mult × VTy)` with `Ctx.scale` (ρ·) and `Ctx.add`
(zipWith +) already defined but unused by the rules.

**Decision**: **Path B** (resource-enforce, then prove the real lemma). Chosen
over Path A (ungraded substitution lemma matching the weak rules — rejected as a
weakening we'd have to un-do, giving up the QTT payoff).

**Blocked on / collides with Q3**: the var rule needs "grade ρ at `x`, zero
elsewhere." `List` + `zipWith` (`Ctx.add`) requires matching shape and can't
cleanly express "zero on the rest" the way Torczon's `gradeVec` does. **Q3
(List vs FinMap) must be resolved as part of this upgrade** — it is no longer
deferrable; the rule shape forces the context-representation decision.

**Plan (sequenced)**:
1. Resolve Q3 (context representation) — the rule shape needs it.
2. Upgrade `HasVTy.vvar` to enforce the grade (one-at-`x` discipline).
3. Thread grades through `ret`/`app`/`letC`/`lam` (scale + add).
4. Discharge `subst_value`, then the STD block (preservation/progress/safety).
5. Then `zero_usage_erasable` / `effect_sound` become reachable.

**Revisit signal**: this IS the active ◊2 task — no deferral. Resolves when the
graded `subst_value` is proven with a clean axiom set.
