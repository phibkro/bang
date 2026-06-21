# ADR-0019 · Typing context split — Finsupp grade-vector + ambient type context

- **Status:** Accepted
- **Date:** 2026-06-21
- **Layer:** K (kernel — resolves OPEN_QUESTIONS Q3, enables Q10)
- **Related:** 0001 (rows-as-Finset; same "let Mathlib supply the algebra" move, applied to grades), 0016 (two-hop; the graded source semantics this shapes), Torczon et al. OOPSLA 2024 (`resource/CBPV/typing.v` — the representation ported)

## Context

`HasVTy` / `HasCTy` (Bang/Syntax.lean) judge over `Ctx := List (Var × Mult × VTy)` —
the multiplicity glued to each binding. The Phase-A rules **carry but never
enforce** the grade: `vvar` is `(∃ ρ, (x,ρ,A) ∈ Γ)` (ρ discarded); `ret`/`app`
never scale or add grades. So `HasCTy` is **grade-insensitive** — and the graded
metatheory (a real `subst_value`, `zero_usage_erasable`, `effect_sound` — the
QTT payoff and the substance of ◊2) is unprovable. This was surfaced 2026-06-21
when the placeholder `subst_value` was found to be vacuous (conclusion =
hypothesis). Closing it requires resource-enforcing rules (Q10), and those force
the long-deferred Q3: **how is the context represented?**

The resource discipline needs the rules to express, at a variable, *"grade ρ at
`x`, zero everywhere else"* and, at elimination forms, *"split the grades:
`γ₁ + ρ·γ₂`"*. Over `List (Var × Mult × VTy)` with `Ctx.add = zipWith`:
- `zipWith` is **partial** — it silently truncates unless both lists share shape
  and order, so "add two contexts" is only meaningful under an unstated
  precondition;
- "ρ at `x`, 0 elsewhere" has no clean closed form (you'd scale-by-0 then patch).

The reference dev (Torczon, `resource/CBPV/typing.v`) avoids this by keeping
**two** things, not one:
- `context n := fin n → ValTy` — the **types**, fixed and shared across a whole
  derivation;
- `γ : gradeVec n := fin n → Q` — the **grades**, which split, scale, and add
  (`γ = γ₁ Q+ (q Q* γ₂)`).

The insight that decides the representation: **types are ambient; grades are
resources.** A resource is consumed and split between subderivations; a typing
assumption is not. Gluing them into one list forces them to split together,
which is exactly wrong — you cannot scale the grades without scaling the types.

## Decision

**Split the typing context into two independent components**, mirroring Torczon:

```
HasVTy (γ : GradeVec) (Γ : TyCtx) (v : Val)        (A : VTy)        : Prop
HasCTy (γ : GradeVec) (Γ : TyCtx) (c : Comp) (e : Eff) (B : CTy)   : Prop

GradeVec := Var →₀ Mult      -- Mathlib Finsupp; default ⊥/0; the resource vector
TyCtx    := List (Var × VTy) -- ambient typing assumptions; shared, no arithmetic
```

Grade arithmetic comes from Mathlib's `Finsupp` for free (`Var →₀ Mult` is a
`Module` over the `Semiring Mult`):
- `Finsupp.single x ρ` — "grade ρ at `x`, 0 elsewhere" (the var rule);
- `γ₁ + γ₂` — pointwise, **total** (no shape precondition);
- `ρ • γ` — scale every grade by `ρ` (elimination forms).

The rules then thread grades Torczon-style (the Q10 upgrade):
`vvar` demands `γ = Finsupp.single x 1` with `Γ` supplying the type; `ret`/`app`/
`letC`/`lam` scale-and-add. `Ctx.scale` / `Ctx.add` (the old `List` ops) are
retired in favour of the `Finsupp` `•` / `+`.

**Companion type-syntax change — the function arrow carries the argument
multiplicity.** Torczon's function type is `CAbs q' A B`; ours is
`CTy.arr A B`, dropping `q'`. Without it, `lam` cannot *record* how much it uses
its argument and `app` has nothing to scale the argument's grades by
(`T_App: γ = γ₁ Q+ q Q* γ₂`) — the resource-enforcing application rule is
unimplementable. So `CTy.arr` becomes `arr : Mult → VTy → CTy → CTy`
(`A →^q B`). This is done **now** because it is currently cheap: `arr` is
matched in exactly two places (the `lam`/`app` rules); the compiler and LR do
not pattern-match it yet. Deferring until they do would multiply the cost.

## Rationale

- **Total arithmetic, no hidden precondition.** `Finsupp +` is defined on all
  pairs; the `zipWith` shape-matching wart disappears (and with it a class of
  latent off-by-one context bugs).
- **The discipline becomes expressible.** `single x 1` *is* the variable rule's
  premise; there is nothing to encode by hand.
- **Mathlib supplies the algebra** — the same win ADR-0001 took for rows
  (`Finset` lattice) we now take for grades (`Finsupp` module). Laws inherited,
  not proven.
- **Ports Torczon near-line-by-line.** `gradeVec`/`context` ↦ `GradeVec`/`TyCtx`;
  `Q+`/`Q*` ↦ `+`/`•`. The substitution and preservation proofs port with it.
- **Single source of truth per concern** — grades live only in `γ`, types only
  in `Γ`; they can't disagree.

## Rejected alternatives

| option | why not |
|--------|---------|
| Keep `List (Var × Mult × VTy)`, patch the rules | `zipWith` add stays partial; "0 elsewhere" stays unexpressible; the proofs fight the representation forever. Premature-pragmatism: smaller diff now, permanent wart. |
| One `Finsupp (Var) (Mult × VTy)` | `(Mult × VTy)` has no meaningful pointwise `+` (grades add; types must *match*, not add). Conflates the two concerns the split exists to separate. |
| `Var → Mult` (plain total function) for grades | No finite support ⇒ no canonical `0`-default, no decidable equality, no `Finset` of used vars; loses the Mathlib `Finsupp` lemma library. |
| de Bruijn `fin n` (Torczon verbatim) | Faithful but abandons our named-variable substitution (`Comp.subst x v`) and the existing syntax/eval; a larger rewrite than the win justifies pre-◊3. |

## Consequences

- (+) Q10's rule upgrade becomes a mechanical port rather than a fight with the
  representation; `subst_value`'s `Γ + ρ·Δ` is `γ_Γ + ρ • γ_Δ` over `Finsupp`.
- (+) Q3 is resolved (was "defer until proofs demand" — the proofs now demand it).
- (−) Signature change to every `HasVTy`/`HasCTy` site: `Bang/Syntax.lean`
  (definitions), `Bang/Spec.lean` + `Bang/Compat.lean` (statements). Bounded —
  3 files, ~40 occurrences.
- (−) `subst_value` and the grade-soundness statements get restated against the
  two-context signature (already `sorry`; no proof lost).
- The effect row `e : Eff` is unchanged and orthogonal — effects annotate the
  computation, grades annotate variable usage; the split touches only the latter.

## Revisit if

- A proof needs the type context to *also* vary within a derivation (it
  shouldn't — that would signal a deeper modelling error, not a rep problem).
- `TyCtx`'s `List` lookup becomes a bottleneck → switch the **type** side to a
  `Finsupp`/`FinMap` too (independent of the grade-vector decision settled here).
- The named-variable encoding itself proves too costly at ◊3 and a de-Bruijn
  port becomes warranted — at which point `GradeVec`/`TyCtx` map straight onto
  Torczon's `gradeVec`/`context`.
