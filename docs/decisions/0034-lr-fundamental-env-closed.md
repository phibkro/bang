# ADR-0034 · `lr_fundamental` is the env-closed (open-term) fundamental theorem; the bare `c c` is its `Γ=[]` corollary

- **Status:** Accepted + **statement amendment LANDED** (◊4 U6, `133a4c1`, 2026-06-23; `just verify` green,
  716 jobs). The proof BODIES remain `sorry` (the ◊4 proof work — `lr_fundamental`/`_closed` are
  `[propext, sorryAx, Quot.sound]`); ◊2 0-axiom + ◊3 trusted-three intact.
- **Date:** 2026-06-23
- **Layer:** P (proof / spec — the fundamental theorem of the logical relation and its closed corollary).
- **Supersedes:** the Phase-A stub statement of `lr_fundamental` (`Bang/Spec.lean`).
- **Reference:** Biernacki et al. POPL'18 §4–5 (the fundamental theorem is stated over a *related substitution
  environment*); Ahmed ESOP'06 (step-indexed semantic typing closes over env-substitutions). Sibling of
  ADR-0033 (the τ/ε row index) — same "a Phase-A stub meets the real construction and needs its faithful form".

## Context

The frozen stub was `lr_fundamental : HasCTy γ Γ c e B → ∀ n, Crel n B e c c` — same `c` both sides, NO
substitution environment, `Γ` arbitrary. This is the **classic *wrong* statement** of the fundamental
theorem: it is **false for open `c`**. Refutation (U6, verified): `c = ret (vvar 0)` is typable at
`Γ = [unit]`, but `Crel … (ret (vvar 0)) (ret (vvar 0))` needs `Vrel n unit (vvar 0) (vvar 0)`, which demands
`vvar 0 = vunit` — false. And it cannot even be the **induction invariant**: the induction over `HasCTy`
descends under binders (`letC`/`lam`/`case`/`split`) into sub-derivations with non-empty `Γ`, where the IH
must relate *open* sub-terms, blocking the same way. (Leaving it `sorry` was rejected for the same reason
`group_recovers` was retired — a false frozen theorem is a landmine, not a deferral.)

## Decision

Amend `lr_fundamental` to the faithful **env-closed** form, and add the closed corollary as a named lemma:
```
lr_fundamental        : HasCTy γ Γ c e B → ∀ n δ₁ δ₂, EnvRel n Γ δ₁ δ₂ → Crel n B e (closeC δ₁ c) (closeC δ₂ c)
lr_fundamental_closed : HasCTy γ []  c e B → ∀ n,                       Crel n B e c c                  -- Γ=[] instance, empty env, closeC ε c = c
```
- `EnvRel n Γ δ₁ δ₂` relates two closing substitutions pointwise by `Vrel` at each `Γ` slot; `closeC`/`closeV`
  apply a closing substitution to a `Comp`/`Val`. These live in `Bang/LR.lean §5.2b` (relocated from Compat so
  the frozen `Spec.lean` statement can reference them — Spec imports LR, not Compat).
- This IS "the fundamental theorem" as the LR literature means it; the bare `c c` was an under-specified stub.
- The closed corollary is exactly what the spine consumes: `lr_sound`'s capstone needs `Krel`-reflexivity
  (`krel_refl`, `Compat.lean`) at CLOSED stacks (eval contexts are closed), which derives from
  `lr_fundamental_closed`. So the dependency chain is **env-closed `lr_fundamental` → `lr_fundamental_closed`
  → `krel_refl` → `lr_sound` capstone**.
- A faithful **tightening**, not a weakening (the proof-engineer red line); surfaced by the implementer (not
  hacked), authorised as `STATEMENT_CHANGE_OK`. `Audit.lean` now gates `lr_fundamental_closed` too.

## Rejected alternatives

| option | why not |
|---|---|
| Keep the bare `c c` / arbitrary `Γ` | **False for open `c`** (refuted above); cannot be the induction invariant. |
| Restrict the frozen statement to `Γ=[]` | True, but it is the *corollary*, not the fundamental theorem — and the induction still needs the env-closed form internally. The env-closed headline is strictly more faithful at zero extra cost (the `EnvRel` machinery is needed either way). |
| Leave it `sorry` for open `Γ` (the spike's option b) | A false frozen statement parked as `sorry` is the `group_recovers` landmine (ADR-0032). Rejected. |

## Consequence

`lr_fundamental`'s shape is fixed BEFORE the proof (U6's substitution-descent + compat lemmas) is assembled,
so that work targets the faithful relation. `≈`/`⊑` and the other statements are unaffected. Meta-note: this
is the *third* ◊4 frozen-statement correction (ADR-0033 τ/ε row; this; plus the U1/U4 signature catches) —
the "frozen" LR statements were Phase-A **stubs**, and proving them is revealing their faithful forms
(correctness-by-construction: the proof determines the true statement). The genuinely-frozen statements are
the proven ◊2/STD block; the LR headlines are being finalised through the proofs.
