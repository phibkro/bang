# ADR-0083 · Option/Result are universal prelude types; Either IS the built-in binary sum (not a nominal type); the first witnessed isomorphisms

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: Now that generic data (ADR-0079) + annotation-free introduction (ADR-0081) are in, the universal generic types are promoted to the INJECTED PRELUDE (the opt-out module, Q34): `data Option a = None | Some(a)` and `data Result e a = Err(e) | Ok(a)`, filtered per-name like `Str`/`Char` (zero runtime fuel — data decls are elaboration-only). **`Either` is NOT a nominal data type — it IS the built-in binary sum `e + a`**: `Left`/`Right`/`match` are already RESERVED surface primitives (ADR/#53), so a nominal `data Either = Left | Right` COLLIDES and breaks the sum corpus; one-construct-per-problem ⟹ `Either` = the sum, and the isomorphism conversions bridge `Result`/`Option` to it. Seven functions (`mapOption`, `mapResult`, `bimap`, and the four iso conversions) are injected CONDITIONALLY — only when the program mentions the name (`surfUsesVar`) — so existing fuel-bounded `#guard`s are UNCHANGED. The four ISO round-trips (`from∘to = id`) are the FIRST WITNESSED ISOMORPHISMS (Q41's witnessed rung), property-tested through `Source.eval`. Kernel/`HasCTy`/census UNTOUCHED (frontend leaf).
- **Depends-on**: 0079, 0081, 0068, 0074
- **Relates-to**: Q41 (type isomorphism — the witnessed rung, now realized), Q34 (prelude-as-opt-out), Q26 (the Functor/Monad instances over these carriers = HKT bite-3, ADR-0082), #53 (the built-in sum whose `Left`/`Right` `Either` reuses)

- **Status:** Accepted (operator-approved 2026-07-07) — landed `1ac850a` (prelude IC)
- **Date:** 2026-07-07
- **Layer:** C + surface/checker (tested superset). Frontend LEAF (`TypeCheck`, fan-in 0); census byte-identical, kernel untouched.
- **Builds on:** ADR-0079 (generic data — `Option`/`Result` are generic decls), ADR-0081 (annotation-free intro — `Some(x)` constructs with no annotation), ADR-0068 (traits/laws — an iso is a witnessed law), ADR-0074 (the string prelude — the injection mechanism this extends).

## Context

`Option`/`Result`/`Either` are the universal generic types every program wants; before bite-1 + #55 they had
to be redefined per program. With generic data (ADR-0079) + annotation-free introduction (ADR-0081) in, they
become expressible as PRELUDE types. The question raised alongside (Q41) — `Result e a ≅ Either e a`,
`Option a ≅ Either Unit a` — makes the isomorphism conversions the first concrete test of the witnessed-iso
rung.

## Decision

1. **`Option`/`Result` as prelude data types.** `data Option a = None | Some(a)`, `data Result e a = Err(e) |
   Ok(a)`, prepended by `elabProg` and filtered per-name against user decls (like `Str`/`Char`); data decls
   cost zero runtime fuel.
2. **`Either` IS the built-in binary sum `e + a`.** `Left`/`Right`/`match` are reserved surface primitives
   (#53). A nominal `data Either = Left | Right` collides with them and breaks the existing sum corpus.
   One-construct-per-problem: `Either` = the sum; the isos convert `Result`/`Option` to it.
3. **Maps + isos, CONDITIONALLY injected.** `mapOption`, `mapResult` (success-side), `bimap` (bifunctor over
   `e + a`), and `resultToEither`/`eitherToResult`, `optionToEither`/`eitherToOption` — injected only when the
   program mentions the name (`surfUsesVar`, a total Surf traversal), so unused programs pay zero fuel and
   every existing fuel-bounded `#guard` is unchanged.
4. **Four witnessed isomorphisms.** Round-trip `#guard`s (`from∘to = id`, sentinel on the wrong branch):
   `eitherToResult∘resultToEither` on `Ok`/`Err`, `eitherToOption∘optionToEither` on `Some`/`None` — Q41's
   witnessed rung made real via the oracle.
5. **Three sum-sibling checker moves** (the sum analogs of the ADR-0081 #55 PRODUCT moves, needed for the
   sum-ranging isos): `synthSC` matchS `.vhole ⟹ .sum ?A ?B`; `elabS` matchS placeholder-hole arm binders;
   `elabS` inl/inr ANF a computation payload (value payloads byte-identical). Frontend-leaf, additive.

## Rejected / staged

- **A nominal `data Either`** — collides with the reserved `Left`/`Right` (#53), breaking the sum corpus. A
  future session wanting a nominal `Either` must pick non-`Left`/`Right` constructor names. Deliberately not
  provided.
- **Unconditional function injection** — the 7 fn-wrappers cost ~+10 fuel and tipped existing fuel-20 sum
  guards over. The conditional (`surfUsesVar`) injection is the fix (keep existing guards unchanged, per the
  landing gate).
- **`mapEither` instead of `bimap`** — `bimap` (maps both sides of `e + a`) is the more general bifunctor
  operation; chosen + documented.

## Consequences

- `Option`/`Result`/`Either` are universal (no per-program redefinition); `parser-combinators` dogfoods the
  prelude `Option` (its local `data Option` deleted).
- The first witnessed isomorphisms exist (Q41), on the bite-2 law machinery — the model for a future
  `derive Iso` / `Serialisable` codec (the schema thread).
- These are the instance CARRIERS for the Functor/Monad HKT tier (ADR-0082 Stage D).

## Revisit if

A nominal `Either` is wanted (needs non-reserved ctor names); OR a `Functor`/`Monad` trait unifies the
per-type maps (HKT, ADR-0082) — then `mapOption`/`mapResult`/`bimap` become one lawful `fmap`; OR structural
iso DERIVATION (Q41's derive rung) replaces the hand-written conversions.
