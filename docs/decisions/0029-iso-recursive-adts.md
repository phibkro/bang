# ADR-0029 — Iso-recursive ADTs (sum + product + μ) for the data layer

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: Iso-recursive ADTs (sum + product + μ with `fold`/`unfold`); inductive only; μ-vars ≠ polymorphism.
- **Resolves**: Q18
- **Depends-on**: 0027, 0026, 0028

- **Status**: Accepted
- **Layer**: K (kernel type-system extension)
- **Depends on**: 0027 (monomorphic — μ-vars ≠ polymorphism), 0026 (laws on the ladder), 0028 (inductive = verified core; coinductive → Div superset)
- **Date**: 2026-06-23

## Context

Rung 2 (a verified `Stack Int`) and the moat (Q19 — *laws between operations on user-defined data
objects*) both need **user-definable data types**. The kernel value types are `unit` + `int` only
(`VTy`). Q18: what data-type mechanism, and is it iso- or equi-recursive?

## Decision

**Extend `VTy` with iso-recursive algebraic data types: sum (`A + B`), positive product (`A × B`), and
iso-recursive μ (`μX.T`) with explicit `fold`/`unfold`.**

```
value formers (VTy/Val)        eliminators (Comp)         μ coercions
  inl v / inr v  : A + B         case   (on sum)            fold   : T[μX.T/X] → μX.T   (= a constructor)
  ⟨v, w⟩         : A × B         split  (on product)        unfold : μX.T → T[μX.T/X]   (= a match)
  fold v         : μX.T          unfold (on μ)              unfold (fold v) ↦ v   (fold/unfold ERASE)
```

- **μ-recursion variables are NOT polymorphism.** `μX.T` binds a *type-level recursion variable* (de
  Bruijn at the type level), categorically distinct from a `∀`-quantified parametric type variable.
  `μX. 1 + (Int × X)` is a **closed, monomorphic type**. So **ADR-0027's monomorphic v1 is preserved** —
  μ lives happily in monomorphic systems (STLC + μ); it is orthogonal to System F's `∀`.
- **Inductive only** (least fixpoint). Coinductive μ (streams, the OS scheduler loop) → the **Div
  fragment** (ADR-0028), added later — do not retrofit inductive μ into coinduction.
- **User-definable** (the moat needs it): from `+`/`×`/μ the user defines
  `List = μX. 1 + (Int × X)`, `Stack = List`, `Tree`, etc. The mechanism is **general from rung 2** —
  not a built-in `List`.
- **Laws via assert + property-test** (ADR-0026 tested rung): `pop (push x s) = (x, s)`, tested over
  arbitrary `Int × Stack` with `plausible`.

## Why iso, not equi

The functional/behavioral difference is **zero**: same programs typecheck, same runtime values,
`fold`/`unfold` erase (`unfold (fold v) ↦ v`). The difference is entirely metatheoretic:

- **Equi-recursive** makes type *equality* the equality of infinite regular trees — decidable
  (Amadio–Cardelli) but **coinductive and heavy**, and every type-equality step in
  `preservation`/`progress` becomes a coinductive argument. Brutal for a verified kernel, for no
  functional gain.
- **Iso-recursive** keeps type-matching **syntactic** — the existing `HasVTy`/`HasCTy` machinery just
  extends. The only cost is explicit `fold`/`unfold`, which is **runtime-free and recoverable at the
  surface**: a data **constructor IS a `fold`**, a **pattern-match IS an `unfold`** (ML/Haskell
  datatypes are iso-recursive). The surface elaborates `push`/`pop`/`match` into `fold`/`unfold` over
  the μ (a Q20 pseudoinstruction); the user never writes them.

For a verified language the metatheory burden dominates → iso wins decisively, giving up nothing real.

## Rejected alternatives

1. **Equi-recursive μ.** *Why not*: coinductive type equality, heavy proof burden, zero functional gain.
2. **Dependent inductive families** (Agda/Lean datatypes). *Why not*: a proof-assistant in the kernel —
   ADR-0026 keeps that off the kernel; ADR-0027 is monomorphic.
3. **A built-in `List`** (no general mechanism). *Why not*: ad-hoc; the moat needs user-*defined* types,
   so the mechanism must be general from rung 2.
4. **Church / CBPV encoding** (no new kernel types — encode data via functions/thunks). *Why not*: poor
   ergonomics + performance; possibly an *internal* lowering target, not the source mechanism.

## Consequences

- `VTy` gains `sum`/`prod`/`mu`/`tvar`; `Val` gains `inl`/`inr`/`pair`/`fold`; `Comp` gains
  `case`/`split`/`unfold`. A **K-ADR** (type-system extension) — **NOT a 6th computational primitive**
  (invariant #5 governs thunk·force·rows·handlers·STM; type-formers are orthogonal).
- Metatheory (`preservation`/`progress`) extends with the new value + elimination cases — syntactic
  type-matching keeps these light (the iso payoff).
- The surface hides `fold`/`unfold` in constructors/patterns (Q20 pseudoinstructions).
- **rung 2's `Stack Int`** is the first instance — and the first concrete **moat** demo (push/pop laws
  via `plausible`).
- Q18 resolved; design-space-map #4 resolved.

## Revisit if

- Coinductive data is needed (streams, the scheduler) → add **coinductive** μ in the Div fragment
  (ADR-0028); do not retrofit inductive μ.
- The surface coercion-hiding (Q20) proves insufficient → revisit the elaboration, not the kernel μ.
- Type inference (HM, ADR-0027 tier 2) interacts badly with iso `fold`/`unfold` placement → revisit at
  that tier (iso-recursive + inference is well-trodden: ML).
