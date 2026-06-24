# 0038 — CBPV arrow observation in the biorthogonal LR: peeling `Krel(arr)` + returner-restricted empty-stack adequacy

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: CBPV computation-typed arrows in the LR: a PEELING/existential `Krel` arrow clause + returner-restricted empty-stack adequacy.
- **Depends-on**: 0034, 0036, 0033, 0035, 0016

- **Layer:** P (LR / proof-statement, with 0033 / 0034 / 0036)
- **Status:** Accepted
- **Depends on:** 0034 (env-closed fundamental), 0036 (closed-value carrier), 0033 (row-indexed relations), 0035 (biorthogonal LR for ◊4), 0016

## Context

The fundamental theorem's `lam`/`app` cases need the LR to relate CBPV **computation-typed
arrows** (`arr q A B`; `lam` is a computation normal form, `app` the elim via the `appF` frame:
`(appF w :: K, lam M') → (K, M'.subst w)`).

Biernacki's LR (our template) makes the arrow a **value type** (Fig 6 `⟦τ₁ →ε τ₂⟧`, related by
application landing in `E⟦·⟧`), so his continuation relation `K⟦·⟧` (Fig 7) has **no arrow clause**.
Our kernel makes `arr` a **CTy**, so `Vrel` can't host it and `Krel`'s `F`-keyed return-half is
vacuous at `arr` — the `lam`/`app` congruence could not close. This is a CBPV **adaptation**, not a
Biernacki transcription. (Confirmed by source-reading Fig 6/7 + Forster–Schäfer–Spies–Stark
"Call-By-Push-Value in Coq".)

## Decision

1. **Add an arrow clause to `Krel`** (keep `Crel` uniform-biorthogonal — option A), as the
   **peeling / existential** form. `Krel n (arr q A B) ε K₁ K₂` (the arrow conjunct) holds iff the
   stacks are `appF`-capped with a closed `Vrel`-related argument and `Krel`-related codomain tails:
   ```
   ∧ (∀ q A B, C = CTy.arr q A B → ∃ w₁ w₂ K₁' K₂',
        K₁ = Frame.appF w₁ :: K₁' ∧ K₂ = Frame.appF w₂ :: K₂' ∧
        Val.Closed w₁ ∧ Val.Closed w₂ ∧ Vrel n A w₁ w₂ ∧ Krel n B ε K₁' K₂')
   ```
2. **Restrict `krel_nil_succ` + `lr_sound_closed` to returner types** (`C = CTy.F q A`).

Landed sorry-free in `f0aebb1` (new cores `krel_appF_intro`, `compat_app`, `compat_lam`,
`converges_appF_lam`). WF: the clause routes `Krel n (arr q A B)` → `Vrel n A` + `Krel n B`, both
`sizeOf`-decreasing (same lex pattern as `F`→`Vrel`, `Vrel(U φ B)`→`Crel`). ◊2/◊3 gates held.

## Why — and why BOTH pure forms failed (the load-bearing part)

The build arbitrated between two candidate forms; **both pure forms were refuted**:

- **EXTENDING** (`Krel(arr) ⟺ ∀ Vrel w, Krel(B)(appF w :: K)`) — refuted by `compat_app`. Its builder
  `krel_appF_intro` must produce `Krel(arr)(appF v :: K)` from `Krel(B) K`; under extending, the
  arrow-half then demands `Krel(B)(appF w :: appF v :: K)` — a **double-`appF`** that never bottoms
  out. Non-terminating; blocks `compat_app`.
- **PEELING alone** — refuted by `krel_nil_succ`. The empty stack `[] ≠ appF`-capped, so the
  existential fails, yet `Krel(arr) [] []` is semantically **true-vacuous**.

**Resolution = peeling + F-restriction.** Peeling is correct for the *meaningful* observation
contexts: `appF`-capped stacks are the **only** non-stuck observers of a function (`letF`/`handleF`/`[]`
on a `lam` are all stuck → vacuous). The empty-stack adequacy is restricted to returners because:

> an arrow-typed **whole program** is a bare `lam`, **stuck at `[]`** (`step([], lam) = none`) ⇒
> `¬Converges` ⇒ `⊑` is **vacuously true** at arrow type. The empty stack is the whole-program answer
> context, which is intrinsically a **returner**.

Shrinking `Krel(arr)` to the `appF`-capped contexts is **sound for `lr_sound`**: the excluded contexts
observe arrow terms vacuously, so they add no `⊑` constraint. The F-restriction is **more faithful**,
not a hack. **Bonus:** it re-closes `krel_nil_succ`'s arrow-half (now vacuous since `F ≠ arr`) —
`krel_nil_succ` is sorry-free again.

## Consequences

- New cores sorry-free; the `lam`/`app` cases of `lr_fundamental` close (`crel_fund` via
  `closeC_lam`/`closeC_app` + `closeC_subst_comm`, same engine as `letC`).
- **Downstream:** `krel_refl` (the `lr_sound` capstone, task #32) will likely need the same
  arrow-`[]`-vacuity / F-restriction treatment — flagged there.

## Rejected alternatives

1. **Extending `Krel(arr)` clause** — double-`appF` non-termination. *Build-refuted.*
2. **Peeling alone (no F-restriction)** — `krel_nil_succ` false at arrow. *Build-refuted.*
3. **Structural `Crel`-at-arr (option B)** — changes `Crel`'s definition, ripples ~12 `rw [Crel]`
   sites, breaks the uniform ⊤⊤ ADR-0035 leans on.
4. **`arr`-as-value-type (option C, Biernacki's actual choice)** — kernel type-structure change
   (collapses `CTy.arr` into `VTy.U`, drops `lam`-is-a-computation-normal-form); violates invariant #5;
   out of ◊4 scope.

## Revisit if

- The `lr_sound` capstone (`krel_refl`) needs a different arrow treatment than the F-restriction.
- `arr` is ever remodeled as a value type (a kernel redesign, its own K-ADR).

_Shape confirmed by the build (`f0aebb1`), not hypothesized — both pure forms empirically refuted, then
the pre-authorized peeling + F-restriction closed `compat_lam`/`compat_app`. Both pure forms were the
main-loop's pins; the build was the arbiter._
