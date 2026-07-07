# ADR-0079 · Generic (parameterized) data types elaborate to the monomorphic kernel — each concrete instantiation monomorphizes to a closed ADR-0069 μ; annotation-driven introduction

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: Parameterized data declarations (`data List a = Nil | Cons(a, List a)`) are realized by the SAME elaborate-to-mono move as the rest of polymorphism (ADR-0075): a generic decl gives POLYMORPHIC constructors (`Nil : ∀a. List a`, `Cons : ∀a. a → List a → List a`) that ride the HM generalize/instantiate machinery (ADR-0075/the IVTy·ICTy re-rep), and **each DISTINCT concrete instantiation monomorphizes to a closed ADR-0069 μ** (`List Int ↦ μX. Unit + (Int × X)`, args substituted for params, self-reference → the μ-bound var). **The kernel / `Source.eval` / `HasCTy` NEVER see a type variable** (invariant #5, kernel untouched). Surface: type params on `data` + `Ty.tApp name args` (type application). Constructor INTRODUCTION is ANNOTATION-DRIVEN (check-mode from an annotation or `let rec` signature drives the concrete element type down through the structure); an un-annotated generic ctor in synth position FAILS LOUD ("annotate") — the ADR-0075 annotation-checked tier. Generic-match binders are derived from the concrete scrutinee μ (`unrollMu` + navigate). Additive: non-parameterized `data` decls keep the byte-identical monomorphic path.
- **Depends-on**: 0069, 0075
- **Relates-to**: PATH-polymorphism bite-1 (this), the IVTy/ICTy re-rep (`b6c66a6`), #50 (the tokenizer's mono-limit finding this dissolves), the parser-combinator milestone (`Parser a` needs this)

- **Status:** Accepted (operator-approved 2026-07-07) — landed `3698367` (gendata)
- **Date:** 2026-07-07
- **Layer:** C + surface/checker (tested superset). Frontend LEAF (`Surface`/`TypeCheck`, fan-in 0); census byte-identical, kernel untouched.
- **Builds on:** ADR-0069 (monomorphic data — the sum/μ/product encoding this parameterizes), ADR-0075 (elaborate-to-mono — polymorphism realized in the checker, kernel stays flat). Same "monomorphize at the concrete use site" move as classic monomorphization (MLton, Rust).

## Context

Polymorphism bite-1 (PATH-polymorphism) needs generic data types — `data List a`, `data Parser a` — the other half (with higher-order polymorphism, ADR-0075/`b6c66a6`) of what a `Parser a` combinator library requires, and the dissolution of the tokenizer's #50 mono-limit finding (`StrList`/`IntList`/`TokList` collapse to `List a`). ADR-0069 gives MONOMORPHIC data (a fixed decl → a closed sum/μ/product encoding). The question: how do type parameters ride on top WITHOUT touching the verified kernel?

## Decision

**Same elaborate-to-mono seam as ADR-0075** — the kernel never learns about type variables:

1. **Surface.** Type parameters on `data` (`data List a = …`); `Ty.tApp : String → TyArgs → Ty` for type application (`List Int`). `TyArgs` is a **capped (≤2) mutual inductive** (`one`/`two`), NOT a `List Ty` — a `List Ty` field breaks `Ty`'s derived `DecidableEq`/`Repr` (the same reason `Surf` uses `DArms`/`SurfArgs`).
2. **Polymorphic constructors.** A parameterized decl gives ctor SCHEMES (`Cons : ∀a. a → List a → List a`) instantiated fresh per use via the generalize/instantiate already in the checker (the IVTy/ICTy re-rep).
3. **Monomorphization (`monoData`/`resolveTyG`, mutual fuel-recursion).** A concrete `List Int` monomorphizes to a **closed ADR-0069 μ** (`μX. Unit + (Int × X)` — args substituted for params, self-ref `List a` → the μ-bound var). Generic decls live in a new `ElabEnv.gen`; monomorphic decls keep the byte-identical `aliases` path.
4. **Introduction is ANNOTATION-DRIVEN.** Ctors elaborate to BARE folds before the checker runs, so the concrete element type isn't known at ctor-elab time. So a generic ctor is a bare fold whose concrete μ is driven by CHECK mode from an annotation (`: List Int`) or a `let rec` signature. An un-annotated generic ctor in SYNTH position fails loud ("annotate") — the ADR-0075 annotation-checked tier (verified by a negative `#guard`).
5. **Generic-match binders from the concrete scrutinee μ.** LOAD-BEARING (not optional): the binders in `match xs { Cons(h, t) -> … }` must be typed during elaboration (else `anfSplit` on `($length) t` throws "unbound t"). Derived by `unrollMu` + navigating the sum/product of the concrete scrutinee μ.

Payoff (build-verified via `runTypedYieldsInt`): `data List a` + `length : List Int -> Int` → 3; `sum` (element binder `h:Int`) → 35; the SAME `List` decl at `List Int` AND `List (Int×Int)` in ONE program → 3 (the polymorphic-DATA proof); `data Pair a b` at `Pair Int (Int×Int)` → 7.

## Rejected / staged (deferred, NOT forced)

- **Annotation-FREE introduction** (infer `a := Int` from `Cons(1, …)`'s field type) — a clean follow-on, un-started. v1 is annotation-DRIVEN (an intentional stop at the ADR-0075 annotation-checked tier), NOT annotation-free.
- **Full σ-reconstruct-and-compare scrutinee validation** — v1 accepts any `.mu _` as a generic-match scrutinee; a wrong-type scrutinee is caught downstream by the arm checker. Full reconstruct-and-compare deferred.
- **Type-application arity > 2 / non-`args=params` self-reference** — v1 caps arity at 2 and fast-paths direct self-reference where `args = params` (covers `List`/`Tree`/`Pair`/`Either`); `Rose`-style / nested-different-self deferred.
- **`List Ty` for `TyArgs`** — breaks `Ty`'s derived `DecidableEq`; the capped mutual inductive is the working rep.
- **A generic-data kernel primitive** — violates invariant #5; monomorphization keeps the kernel flat + untouched (census byte-identical).

## Consequences

- `StrList`/`IntList`/`TokList` collapse to `List a` (the #50 dissolution); `Parser a` and the parser-combinator library become expressible.
- The kernel stays monomorphic + verified — census byte-identical (16 headlines trusted-three), `TypeCheck` a fan-in-0 leaf; generic data is pure tested-superset.
- Non-parameterized `data` behaves exactly as before (additive).

## Revisit if

Annotation-free generic introduction is taken up (infer params from field types at intro); OR full scrutinee-type validation is wanted; OR arity > 2 / `Rose`-style nested self-reference is needed (a real program demands it) — extend `monoData`/`resolveTyG`'s self-reference handling.
