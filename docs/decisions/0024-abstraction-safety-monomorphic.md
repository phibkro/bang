# ADR-0024 · Abstraction-safety: `no_accidental_handling` is correct-by-construction in a label-indexed machine

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: Abstraction-safety: `no_accidental_handling` restated faithfully + proven — correct-by-construction in the label-indexed machine. Closes the ◊2 gate.
- **Depends-on**: 0018, 0023

- **Status:** Accepted
- **Date:** 2026-06-22
- **Layer:** K (kernel — the §0.5 effect-row well-formedness block; the ◊2 gate theorem)
- **Resolves:** the ◊2 gate (`no_accidental_handling` proven); concretizes the `WfInst`/`RowAll`/`HandlesIntended` axioms (`Bang/Core/Typing.lean §0.5`)
- **Builds on:** ADR-0018 (lacks-constraint discipline — the *why*), ADR-0023 (the label-indexed CK machine — the *mechanism* that discharges it)
- **Reference:** Zhang–Myers POPL'19 (accidental handling / tunneling); Biernacki et al. POPL'18 §5.4 (the set-row fragment)

## Context

ADR-0018 names `no_accidental_handling` as the invariant that licenses bang-lang's ρ-map-free
(set) effect rows: a handler must not capture an operation that was meant for a *different* handler.
Three §0.5 axioms (`RowAll`, `WfInst`, `HandlesIntended`) reserved the shape; the ◊2 gate requires
the theorem **proven**, not stubbed. Closing it surfaced that the placeholder statement was not just
unproven but **vacuous**, and that the property splits cleanly into a monomorphic half (now trivially
true by construction) and a polymorphic half (the real lacks-constraint obligation).

### The placeholder `no_accidental_handling` was vacuous

```lean
theorem no_accidental_handling {l e} {body : Comp} {h : Handler} :
    Disjoint l e → HasCTy γ Γ body (l ⊔ e) (F q A) → HandlesIntended l body h
```

`h` is **universally quantified**. The statement therefore claims *every* handler handles-intended
around `body` — false the moment `h` is a handler scoped to a foreign label (it would catch `e`'s
operations). No definition of `HandlesIntended` makes the ∀-`h` form both true and meaningful: the
guarantee only holds for an `h` that *is* `l`'s handler. The hypotheses (`Disjoint`, the body typing)
were also inert — nothing consumed them. A green proof of this would have been a lie.

## Decision

### D1 — Split the property along the polymorphism boundary

| | what it guards | where the danger is | our discipline |
|---|---|---|---|
| **monomorphic** | a *concrete* handler vs *concrete* foreign labels | nowhere — labels are matched exactly | `no_accidental_handling` (D2): structural |
| **polymorphic** | a handler vs operations arriving through a row *variable* `α#L` | bad instantiation `α := (row containing L)` | `rowinst_requires_disjoint` (D3): the lacks-constraint |

The monomorphic kernel (v1) has no `∀(α#L)` binder in its term/type syntax — type abstraction is a
surface/type-checker feature. So at the kernel level, accidental handling is **unrepresentable**: the
CK machine's `dispatch` (ADR-0023) matches an operation `(ℓ, op)` against `handlesOp h ℓ op`, which
for `throws ℓ₀` is `ℓ₀ = ℓ`. A handler structurally cannot catch a label it does not name. This is
correctness-by-construction (SOUL's root move: make the bad state unrepresentable, not detected).

### D2 — `no_accidental_handling`, restated faithfully (monomorphic)

```lean
def HandlesWithin (l : Eff) (h : Handler) : Prop :=         -- h's interface ⊆ row l
  ∀ ℓ' op, handlesOp h ℓ' op = true → labelEff ℓ' ≤ l

theorem no_accidental_handling {l e : Eff} {h : Handler} :
    HandlesWithin l h → Disjoint l e →
    ∀ ℓ' op, labelEff ℓ' ≤ e → handlesOp h ℓ' op = false
```

A handler scoped to `l` (`HandlesWithin l h`) never catches an operation whose label is in a
*disjoint* row `e` — foreign operations tunnel to an outer handler. **Every hypothesis is
load-bearing**: the proof uses `HandlesWithin` (h catches ⇒ label ≤ l), `Disjoint l e`
(label ≤ l ⊓ e = ⊥), and `EffSig.labelEff_ne_bot` (⊥ is impossible for a real label) to derive the
contradiction. `throws_handlesWithin` discharges the `HandlesWithin` premise for the only handler
form (`Handler.throws`); `state` extends it when it lands (Q12).

- *Why drop `body` + its typing?* The safety is **structural** (about `h`, `l`, `e`), independent of
  what `body` does — keeping an unused `HasCTy body` hypothesis would falsely imply it's needed. The
  body-typing's role (body's operations ⊆ `l ⊔ e`) is the *caller's* context, not a proof input.

### D3 — `rowinst_requires_disjoint`: `WfInst` carries the lacks-constraint

```lean
def WfInst (_q : Eff → CTy Eff Mult) (L ε : Eff) : Prop := Disjoint ε L

theorem rowinst_requires_disjoint {q : Eff → CTy Eff Mult} {L ε : Eff} :
    WfInst q L ε → Disjoint ε L := id
```

This is ADR-0018 rule 2 *verbatim* ("row instantiation is well-formed only when the instantiating row
is disjoint from `L`"), so `WfInst` **is** the disjointness condition and the theorem extracts it.
`RowAll` (the reified `∀(α#L)` type) is retired: the monomorphic `CTy` has no row-quantifier
constructor, so there is nothing to reify; the quantifier lives only as the `(family, L)` pair
`WfInst` inspects. When row polymorphism enters the surface language, a real `∀`-row `CTy` former +
an instantiation judgment replace this (a future K-ADR); the obligation it must discharge is exactly
`WfInst`'s content.

NB the old §0.5 warning "`HandlesIntended` must NOT be `= Disjoint`" applies to the *operational*
tunneling property (D2, which is about `handlesOp`, not `Disjoint`). `WfInst = Disjoint` is correct —
`WfInst` is a *well-formedness* predicate whose entire content is the disjointness side-condition.

## effect_sound — deferred (not the ◊2 gate), with a recorded subtlety

`effect_sound` (`static e over-approximates the observed trace`) is **not** closed here. Its current
statement `HasCTy [] [] c e (F q A) → evalTrace fuel c = done (v,t) → traceWithin t e` is in tension
with the deep-handler machine: `e` bounds only the operations that **escape** `c`'s own handlers, not
the ones handled *internally*. A label handled inside `c` (e.g. `raise ℓ` under `c`'s own `throws ℓ`)
is performed during evaluation yet is **not** in `c`'s effect `e` (the handler discharged it). So a
trace that logs *all* dispatched labels is not bounded by `e`. And a program that runs to `done`
escaped nothing (an escaping operation would be stuck), so an *escaping-only* trace is trivially `[]`.
A meaningful `effect_sound` needs a trace semantics that distinguishes these — recorded as a new
OPEN_QUESTION; it belongs with the `effect_sound`/`Trace` concretization, after the ◊2 gate.

## Rejected alternatives

| option | why not |
|--------|---------|
| Keep the ∀-`h` statement; pick a `HandlesIntended` that makes it provable | Any such definition is vacuous (true for all `h` only if it asserts nothing about `h` catching foreign labels). Proving a vacuous headline is the exact anti-pattern the proof discipline forbids. |
| Add `∀(α#L)` row polymorphism to `CTy` now, to prove `rowinst_requires_disjoint` "for real" | Type abstraction is a surface/type-checker feature, not kernel-v1 scope (the kernel terms have no type abstraction). Premature; would inflate the frozen kernel. Model the well-formedness semantically (`WfInst`) until the surface needs it. |
| Prove `effect_sound` now with an all-operations trace | False (internal handling hides labels from `e`). Would require weakening `traceWithin` to a lie. Defer to honest trace semantics. |

## Revisit if

- Row polymorphism enters the surface language: `RowAll` returns as a real `∀`-row `CTy` former + an
  instantiation judgment; `WfInst` becomes its well-formedness rule (the `Disjoint` content stays).
- `state` (or any multi-op handler) lands: `throws_handlesWithin` generalizes to the new handler's
  interface; `HandlesWithin`/`no_accidental_handling` are unchanged (they already quantify over `h`).
- `effect_sound` is taken up: design the escaping-vs-internal trace semantics first (its OPEN_QUESTION).
