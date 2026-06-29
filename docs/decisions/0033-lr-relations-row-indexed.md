# ADR-0033 · The LR relations are indexed by the effect row ε (faithful Biernacki τ/ε)

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: The LR relations are indexed by the effect row ε (faithful Biernacki τ/ε); a faithful tightening of the Phase-A stub.
- **Depends-on**: 0021, 0023, 0016

- **Status:** Accepted + **LANDED** (◊4 U2, `eadec83`, 2026-06-23) — axiom-clean (`lr_sound`/`lr_fundamental`
  → `[propext, sorryAx, Quot.sound]`; the 4 LR-relation axioms became WF defs; ◊2/◊3 gates not regressed).
- **Date:** 2026-06-23
- **Layer:** P (proof / spec — the step-indexed logical relation and the two headline statements over it).
- **Supersedes:** the Phase-A stub signatures of `Crel`/`Krel`/`Srel` (`Bang/Meta/LR.lean` §5.2) and the
  corresponding clauses of `lr_sound`/`lr_fundamental` (`Bang/Spec.lean`).
- **Reference:** Biernacki et al. POPL'18 *Handle with Care* §5.1 Figs 6–9 (`E⟦τ/ε⟧` / `K⟦τ/ε⟧` indexed by
  type **and** row); ADR-0021/0023 (precedent: ◊2 statements tightened when a Phase-A stub met the real
  construction).

## Context

The ◊4 logical relation was stubbed in Phase A as four axioms with provisional signatures:
`Crel : Nat → CTy → Comp → Comp → Prop`, `Krel : Nat → CTy → Stack → Stack → Prop`,
`Srel : Nat → Eff → …`. Concretizing them (U2) by transcribing Biernacki Figs 6–9 onto our kernel surfaced
that the computation-level relations are indexed by **both** the answer type τ and the effect row ε — but
the stubs dropped ε inconsistently (`Crel`/`Krel` carried τ but not ε; `Srel` carried ε but not τ).

In **our** kernel the row is genuinely independent of `CTy`: `HasCTy γ Γ c e B` synthesises `e : Eff`
separately (`letC` joins `φ₁ ⊔ φ₂`, `up` produces `φ`), so `e` is **not** a function of `(c, B)` and cannot
be recovered from them. The row is **load-bearing** in the LR: `Srel`'s control-stuck clause is
`c = up ℓ op v ∧ labelEff ℓ ≤ ε ∧ …` — you need ε to express "stuck on an operation that lies in the row."
A 2-argument `Crel` therefore *cannot* be the faithful `E⟦τ/ε⟧`.

## Decision

Thread the effect row through the computation-level relations and the two headline statements:
- `Crel : Nat → CTy → Eff → Comp → Comp → Prop`, `Krel : Nat → CTy → Eff → … `, `Srel` gains the answer
  `CTy` (it already had ε). All four also take the ambient `[EffSig Eff Mult]` (already in `Spec.lean`'s
  variable scope, so the statements' external form is unchanged by that part). `Vrel` stays 4-arg — value
  types carry their rows internally at `U φ B`.
- `lr_fundamental : HasCTy γ Γ c e B → ∀ n, Crel n B e c c` — threads the `e` **already bound** by the
  hypothesis (relate `c` to itself at its own type *and* row).
- `lr_sound : (∀ n, Crel n B e c₁ c₂) → c₁ ⊑ c₂` — `e` universally quantified at the theorem level.

This is a faithful **tightening**, not a weakening (the proof-engineer red line): the old statements were
*under*-specified, and the new ones are strictly more precise. It was **surfaced** by the implementer (not
silently hacked) and authorised as a `STATEMENT_CHANGE_OK` correctness correction.

The relations are real WF defs over a plain lex measure `(n, sizeOf type, role)` (role `Vrel 3 > Crel 2 >
Krel 1 > Srel 0`, breaking the biorthogonal `Crel↔Krel` cycle at equal `(n, type)`; the `▷`/later step drops
`n` across `μ`-unroll and the `Srel` output clause). No iris-lean ▷ modality was needed.

## Rejected alternatives

| option | why not |
|---|---|
| Keep `Crel` 2-arg (τ only), recover ε from `(c, B)` | Impossible — verified against the `HasCTy` rules; `e` is an independent synthesised component, not a function of `(c, B)`. |
| Universal-over-rows `Crel` (∀ ε) | **False for `lr_fundamental`**: a computation stuck on `ℓ ∉ ε` is not safe at ε; the fundamental theorem must relate `c` to itself at *its* row, not all rows. |
| Top-level fixes the empty row (`⊥`) | Same failure — an effectful `c` is typed at a non-⊥ row; the relation must carry it. |

## Consequence

The two statements `lr_sound`/`lr_fundamental` are the headline ◊4 obligations; this fixes their shape
**before** the proofs (U5/U6) are written, so those proofs target the faithful relation. `≈`/`⊑` are
unchanged (ADR-0032 keeps `≈` stable too), so nothing downstream re-derives. The `effect_sound` /
`zero_usage_erasable` residuals are unaffected.
