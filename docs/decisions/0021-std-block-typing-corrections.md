# ADR-0021 · Effect/grade typing corrections surfaced by the STD block

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: Effect/grade typing corrections surfaced by the STD block — makes preservation/progress/type_safety provable; advances Q4.
- **Depends-on**: 0019, 0020

- **Status:** Accepted
- **Date:** 2026-06-22
- **Layer:** K (kernel — typing rules, multiplicity algebra, theorem statements)
- **Amends:** the Phase-A part-2 typing rules in `Bang/Core/Typing.lean` (the
  "first cut" `lam`/`handle` rules) and the `Mult` bound in `Bang/Core/IR.lean`
- **Advances:** OPEN_QUESTIONS Q4 (`handle` rule) — the F-type restriction lands
  here; the label-removing refinement stays deferred
- **Related:** Torczon et al. OOPSLA 2024 — `effects/CBPV/typing.v` (effect
  threading) + `resource/CBPV/typing.v` (grade arithmetic); we merge both
  variants (effect on `U`, coeffect on `F`, per ADR-0019/0020)

## Context

`subst_value` proven (ADR-0020, `e00ee9a`), the handoff framed the rest of the
STD block — `preservation → progress → type_safety` — as "downhill, largely
mechanical." Attempting `preservation` showed it is not: the Phase-A part-2
typing rules (a deliberate "first cut") diverge from the cited Torczon source in
four ways that make the frozen statements **false as written**. Each was traced
against `/tmp/cbpv-ec` (the `plclub/cbpv-effects-coeffects` port).

### C1 — `lam` discards the body's latent effect

```
first cut:   HasCTy (q :: γ) (A :: Γ) M φ B  →  HasCTy γ Γ (lam M) ⊥ (arr q A B)
                                                                    ^^^ φ dropped
```

The β-redex `app (lam M) v ↦ M[v]` (`Comp.subst v M`) then breaks preservation:
inverting `app` then `lam`, the redex is typed at effect `⊥`, but the reduct
`M[v]` genuinely carries the body effect `φ`. The conclusion
`∃ e', e' ≤ e ∧ HasCTy γ Γ M[v] e' B` with `e = ⊥` demands `φ ≤ ⊥`, i.e.
`φ = ⊥` — false for any effectful function body.

Torczon `effects/CBPV/typing.v`:

```
T_Abs M A B ϕ :  CWt (A .: Γ) M B ϕ  →  CWt Γ (cAbs M) (CAbs A B) ϕ
```

The lambda **carries its body's effect `ϕ`**. This is the effect-on-judgment
discipline our `Core` already commits to: `VTy.U` carries `Eff`, `CTy.arr` does
**not**, and `HasCTy` threads a separate effect index. `force`/`vthunk` already
honour it (effect rides `U`); `lam` was the lone violator. Constructing a closure
is operationally pure, but its *type-level* effect is the latent body effect —
exactly as a thunk's type carries the effect it will release when forced.

### C2 — `handle` over a non-`F` body is a stuck normal form

```
first cut:   HasCTy γ Γ M φ B  →  HasCTy γ Γ (handle h M) φ B      (any B)
```

With `B` general, `handle h (lam M')` is well-typed at `arr` type, `Source.step`
has no rule for it (the body is a `lam`, not `ret`/`up`, and `lam` doesn't step),
and it is not a `ret` — a stuck non-terminal. Worse, `handle h (handle h' (lam …))`
nests, so the well-typed-closed normal forms at `arr` type are an unbounded family
`handle* (lam …)` — `progress` cannot hold for general `B`. Handlers handle
**returners** (the return clause consumes the produced value); restricting the
body to `F q A` removes the pathological normal forms and is the standard CBPV
handler typing.

### C3 — the `letC` β grade reshape needs commutative multiplicity

`letC (ret v) N ↦ N[v]`. Inverting `ret` gives `γ₁ = q1 • γ_v`; `N`'s bound slot
is graded `q1 * q'` (`q' = q_or_1 q2`); `subst_value` yields grade
`γ₂ + (q1*q') • γ_v`, while the `letC` rule's own grade is
`q' • γ₁ + γ₂ = q' • (q1 • γ_v) + γ₂ = (q'*q1) • γ_v + γ₂` (associativity only).
Equating them needs `q1*q' = q'*q1` — **commutativity of `*`**.

Torczon's `POSR` (`common/coeffects.v`) deliberately omits mult assoc/comm ("some
of our proofs do not require … commutativity") — but Torczon's *resource* variant
proves soundness **semantically** (`semtyping.v`/`soundness.v`, a logical
relation), never a syntactic `letC` preservation, so it never incurs this
obligation. We do syntactic preservation, so we incur it. The concrete instance
`Bang.QTT` is already a `CommSemiring`, and quantitative-type-theory multiplicity
semirings are commutative across the literature (Atkey ICFP'18, McBride,
Granule/Orchard ICFP'19). Strengthening the bound is the honest statement of the
algebra we actually use.

### C4 — `progress` is stated for general `B` with `isReturn`

```
first cut:   HasCTy [] [] c e B  →  isReturn c ∨ ∃ c', step c = some c'
```

A bare `lam M` is closed-typeable at `arr` type, is not a `ret` (`isReturn` is
false), and does not step — a direct counterexample. `progress` is true only when
the conclusion's terminal predicate matches the type: at `F q A`, the closed
terminal forms are exactly `ret v`. State it at `F q A`, which is also all
`type_safety` needs.

## Decision

Align the four rules/statements with the merged Torczon discipline:

| # | site | from | to |
|---|------|------|----|
| C1 | `HasCTy.lam` (`Syntax.lean`) | conclusion effect `⊥` | conclusion effect `φ` (body effect) |
| C2 | `HasCTy.handle` (`Syntax.lean`) | body `B` (any `CTy`) | body `CTy.F q A` |
| C3 | `Mult` bound (`Core.lean` + all modules) | `[Semiring Mult]` | `[CommSemiring Mult]` |
| C4 | `progress` (`Spec.lean`) | general `B`, `isReturn` | `CTy.F q A`, `isReturn` |

With these, the STD block proves:

- **preservation** — case analysis on `Source.step` + inversion; β-cases use the
  proven `subst_value`; C1 makes `app` give `e' = e`, C3 makes the `letC` grades
  align, the `up`-head `handle` cases are vacuous (`up` is untypable, Q5).
- **progress** — induction on the derivation with the generalized terminal motive
  `isReturn c ∨ isLam c ∨ ∃ c', step c`; C2 keeps `handle` bodies `F`-typed so the
  case reduces; specialized to `F q A`, `isLam` is excluded by inversion, leaving
  `isReturn ∨ steps`.
- **type_safety** — fuel induction over `progress` (F) + `preservation`.

## Rationale

- **Make the false statement true, never weaken to dodge** (proof discipline,
  `docs/notes/OPEN_QUESTIONS.md` preamble). These are corrections *toward* the
  reference, not away from it — each `to` cell is what Torczon's mechanization
  does.
- **Effect-on-judgment is already the architecture.** C1 is not a new design; it
  restores the one rule that violated the `U`-carries-effect / `arr`-doesn't
  discipline baked into `Core` (ADR-0019/0020).
- **Correctness by construction.** C2 removes the stuck normal forms structurally
  (ill-typed), rather than detecting them in a side-condition.
- **Honest algebra.** C3 names the commutativity we already rely on (QTT) instead
  of hiding it by reordering a rule's `*` (which would diverge from Torczon's
  `T_Let` shape for no reason).

## Rejected alternatives

| option | why not |
|--------|---------|
| **C1:** annotate `CTy.arr` with the latent effect (`arr q A φ B`), keep `lam` pure | A second home for effects, contradicting `Core`'s commitment that effects ride `U`/the judgment and `arr` is effect-free. Two mechanisms for one fact (SoT violation). The lam-judgment fix is one mechanism, matches `T_Abs`. |
| **C2:** keep `handle` general, state `progress` with a broad normal-form predicate covering `handle* (lam …)` | The terminal set becomes an unbounded syntactic family; every downstream theorem reasons about non-returner handles that have no operational meaning. F-restriction is the standard, finite story. |
| **C3:** reorder `letC`'s cons-head to `q' * q1` so associativity alone closes it | A representation hack that hides the real requirement and diverges from `resource/…T_Let`. Multiplicities *are* commutative here; say so. |
| **C4:** keep general `B`, add an effect/type-subsumption rule to absorb the mismatch | Subsumption is an orthogonal, ordered-`Mult` feature (already deferred for `lam`'s `q' ≤ q`); it does not fix `lam`-at-`arr` being a non-`ret` normal form. |

## Consequences

- (+) The STD block (`preservation`, `progress`, `type_safety`) becomes provable
  on the de Bruijn base with the already-proven `subst_value`.
- (+) Q4 advances: the `handle` F-type restriction lands; only the label-removing
  refinement remains deferred (still needed for `effect_sound`).
- (~) **Existing proofs port mechanically.** `Metatheory.lean`'s `length_eq`,
  `weaken`, and `subst_gen` `lam`/`handle` cases need updated `intro`/`cases`
  patterns (the constructor signatures change) and `subst_lam_case`'s conclusion
  changes `⊥ → φ`; the proof bodies are unchanged. `[CommSemiring]` strictly adds
  instances, so no `[Semiring]`-era proof breaks.
- (−) **Generality narrows, deliberately.** `subst_value` et al. now require
  `[CommSemiring Mult]` rather than `[Semiring Mult]`; the canonical instance
  (QTT) satisfies it, and no current proof needed the extra generality.
- (=) **Unaffected:** `Core` type *syntax* (`arr` stays effect-free — C1 is a
  judgment fix, not a type change), the effect-row algebra, the LR/compile
  statements.

## Revisit if

- `effect_sound` forces the label-removing `handle` rule (Q4) — extend C2's
  F-restricted rule to subtract the handled label from `φ`, don't revert it.
- A multiplicity instance that is genuinely non-commutative becomes interesting
  (none on the roadmap) — then re-derive the `letC` reshape without C3, or carry
  a non-commutative `letC` variant.
- Subsumption (ordered `Mult`) lands — fold `lam`'s `q' ≤ q` and any effect
  subsumption in together; it composes with C1, doesn't replace it.
