# ADR-0080 · Bounded generic functions monomorphize per concrete carrier — the dict-vs-mono fork resolved for MONOMORPHIZATION; carrier fixed annotation-driven

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: A BOUNDED generic function (`fn fold(xs) : List a -> a where Monoid a = …`) is realized by the SAME elaborate-to-mono move as the rest of polymorphism (ADR-0075): at each concrete use `(fold xs : Int)` the carrier `a` is fixed, the `Trait a` instance is resolved, and the instance's ops are SPLICED into a concrete `let rec` that kernel-typechecks and runs. This RESOLVES the ADR-0075/PATH-polymorphism bite-2 fork **for MONOMORPHIZATION** (Rust/MLton) over dictionary-passing (Haskell): it is consistent with bite-1's `monoData` and the raw-splice trait model (ADR-0068/0079), needs no runtime dictionary, and bang is whole-program elaborate-to-mono. **The kernel / `Source.eval` / `HasCTy` NEVER see a bound or a type variable** (invariant #5, kernel untouched, census byte-identical). Surface: a top-level `fn name(params) : declaredTy where Trait tyVar = body` decl + nullary trait ops (`fn empty() -> Self`). Traits stay **Self-based** (ADR-0068) — the bound `Monoid a` means "the carrier `a` implements Monoid" (Self = a); no trait type-parameter syntax is added. The carrier is fixed **annotation-driven** (ADR-0079): v1 requires the declared result type to BE the bound var (the fold shape `… -> a`), so the call-result annotation gives the carrier; a MISSING instance ⟹ a loud type error. LAWS are preserved unchanged (ADR-0068 tested rung). Only the CONSUMING half is in scope (fold/sum match on Cons/Nil); a bounded function that CONSTRUCTS generic data hits the #55 annotation-driven-intro wall (ADR-0079), deferred.
- **Depends-on**: 0075, 0079, 0068, 0069, 0073
- **Relates-to**: PATH-polymorphism bite-2 (this), ADR-0040 (laws), #55 (annotation-free generic intro — the construction-side deferral), Q26 (the generic lawful stdlib this unlocks)

- **Status:** Accepted (operator-approved 2026-07-07)
- **Date:** 2026-07-07
- **Layer:** C + surface/checker (tested superset). Frontend LEAF (`Surface`/`TypeCheck`, fan-in 0); census byte-identical, kernel untouched.
- **Builds on:** ADR-0075 (elaborate-to-mono — polymorphism realized in the checker, kernel stays flat), ADR-0079 (generic data + annotation-driven introduction — the `monoData` precedent + the annotation discipline), ADR-0068 (Self-based trait/impl wiring + the tested-rung laws this extends), ADR-0073 (`let rec` μ-knot — the monomorphized recursion desugars through it).

## Context — the bite-2 fork (ADR-0075 deferred it here)

PATH-polymorphism bite-2 is generic TRAITS + bounds: `trait Monoid a` + `fold : Monoid a => List a -> a`, the type-power prong toward the generic lawful stdlib (Q26). Bite-1 (ADR-0079) gave generic DATA; higher-order (ADR-0075/`b6c66a6`) gave inferred `compose`. The remaining question a bounded generic function forces: **how does `Monoid a => …` elaborate?** ADR-0075 named the fork and deferred it to here:

```
  monomorphization (Rust/MLton)      dictionary-passing (Haskell)
  ─────────────────────────────      ────────────────────────────
  specialize the bounded fn per      pass the instance record as a
  concrete carrier, splice its ops   hidden runtime argument
  · no runtime dictionary            · separate compilation
  · consistent with monoData +       · effect-system-idiomatic
    the raw-splice trait model       · a runtime value the kernel
  · code-size cost (per carrier)       would have to carry
```

## Decision

**Monomorphization** — the same elaborate-to-mono seam as ADR-0075/0079; the kernel never learns about bounds or type variables:

1. **Surface.** A bounded generic function is a top-level decl `fn name(params) : declaredTy where Trait tyVar = body` (`Decl.fnD`). The `where Trait tyVar` is the bound; `declaredTy` mentions `tyVar` (`List a -> a`). Trait ops may be **nullary** (`fn empty() -> Self`) — Monoid's identity is a value op, not an operator. Traits stay **Self-based** (ADR-0068): no trait type-parameter syntax; the bound `Monoid a` reads as "carrier `a` implements Monoid" (Self = a).
2. **Carrier fixed annotation-driven (ADR-0079).** At a use `(fold xs : Int)` the result annotation fixes the carrier. v1 requires the declared result type to BE the bound var (the fold shape `… -> a`), so the annotation directly gives the carrier — no μ-inversion. An un-fold-shaped bound (result ≠ the bound var) fails loud ("annotate the result"). This is the ADR-0075 annotation-checked tier, consistent with ADR-0079's annotation-driven introduction.
3. **Bound resolution.** The concrete carrier `T` selects the `Trait T` instance from the impl environment (structural keying, ADR-0068). A **MISSING** `Trait T` instance ⟹ a loud type error (the bound is unsatisfied) — never a silent stuck.
4. **Monomorphization (`monomorphizeBFn`).** Emit a RAW monomorphic wrapper: the instance's ops bound in a prologue (a 0-ary op `empty` ⟹ a value binding; an n-ary op `combine` ⟹ an annotated function thunk), the body as a concrete `let rec name : declaredTy[tyVar := T] = fun … = body in (\$name) arg`. Elaborating it ONCE resolves the spliced trait ops AT the concrete `T` (exactly as `buildEnv`'s impl pre-elaboration) and desugars the `let rec` (ADR-0073). Because op bodies are re-elaborated raw at the concrete carrier, a Vec `combine`'s inner `+` decomposes to concrete `Int` δ-rules — no trait-op resolution is left dangling.
5. **Laws preserved.** The trait-LAW mechanism (ADR-0068/0040 tested rung) is untouched — a generic trait carries laws unchanged.

Payoff (build-verified via `runTypedYieldsInt`): the bounded `sum : Monoid a => List a -> a` over the Int Monoid → 6; over the `(Int*Int)` component-wise Monoid → (4,6); the SAME `sum` at BOTH carriers in ONE program → 16 (the genericity proof — one generic fold monomorphized to two distinct instances, both run); a missing `Monoid (Int*Int)` instance ⟹ loud type error.

## Rejected / staged (deferred, NOT forced)

- **Dictionary-passing.** Not refuted — it is separate-compilation-friendly and effect-idiomatic — but it puts a runtime instance record into the value world the kernel would carry, and it is inconsistent with the whole-program raw-splice trait model already landed (ADR-0068/0079). Revisit if separate compilation or first-class instances become a requirement.
- **Trait type parameters in surface syntax (`trait Monoid a`).** Not needed: Self-based traits (ADR-0068) already express the carrier; the bound names it. A later nominal/parametric trait layer can add it without changing this seam.
- **Carrier inferred from the argument (μ-inversion of `List T`).** v1 is annotation-driven (ADR-0079 precedent). Inferring `a` from the argument's concrete type is the clean follow-on (the same annotation-free move ADR-0079 defers).
- **Bounded functions that CONSTRUCT generic data.** A bounded combinator that builds `Option (b × …)` in synth position hits the #55 annotation-driven-intro wall (ADR-0079). v1 scopes the payoff to CONSUMING (fold/sum — match on Cons/Nil); construction defers to #55.
- **Multi-parameter / non-fold-shaped bounds, multiple bounds (`(Monoid a, Ord a) =>`).** v1 is single-bound, single-param, result-is-the-bound-var. Additive extensions.

## Consequences

- The generic lawful stdlib (Q26) becomes expressible: `fold`/`sum`/`mconcat` over any `Monoid`, lawful, monomorphized.
- The kernel stays monomorphic + verified — census byte-identical (16 headlines trusted-three), `TypeCheck`/`Surface` fan-in-0 leaves; bounded polymorphism is pure tested-superset.
- Non-bounded `impl Add for Vec` (ADR-0068) and all existing traits/laws behave EXACTLY as before (additive).

## Revisit if

Dictionary-passing is demanded (separate compilation / first-class instances); OR annotation-free carrier inference is taken up; OR bounded construction (#55) / multi-bound / higher-kinded bounds (`trait Functor f`, ADR-0075 bite-4) are needed.
