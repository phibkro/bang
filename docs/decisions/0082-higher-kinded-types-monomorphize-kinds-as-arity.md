# ADR-0082 · Higher-kinded types (Functor/Monad) elaborate to the monomorphic kernel — kinds-as-arity, decidable HK-unification by constructor-injectivity, monomorphize-per-constructor (NOT dict-passing)

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: Higher-kinded types (`trait Functor f`, `trait Monad m`; type variables ranging over CONSTRUCTORS, `f : Type→Type`) are realized by the SAME elaborate-to-mono move as the rest of polymorphism (ADR-0075/0079/0080): the kernel never learns about kinds, ∀-variables, or type-constructors-as-values. A higher-kinded use is monomorphized at each concrete CONSTRUCTOR (the bite-2 `bfnWrapper` move, keyed on a constructor name instead of a resolved carrier type). Kinds are tracked as ARITY (a `Nat` per type variable — a degenerate kind), reusing bite-1's constructor-param count; an explicit `Kind` inductive is DEFERRED (needed only for higher-order kinds / monad transformers, not for Functor/Monad). Higher-kinded UNIFICATION is decidable by **constructor-injectivity decomposition** (`f a ~ Option Int ⇒ f:=Option, a:=Int`) — inside the Miller pattern fragment, available for free because bang has no type families (no reducing type synonyms); anything outside it (`f a ~ Int`) is an ANNOTATION-required descent, never an unsound guess (the ADR-0075 decidability invariant). Traits gain a constructor-kinded, APPLIED `Self` (`f a = Self a`) and POLYMORPHIC methods (`fmap : ∀a b. (a→b) → f a → f b`), composing bite-0 generalize/instantiate with bite-2 monomorphize-per-carrier. **This does NOT re-open the ADR-0080 dict-vs-mono fork:** HKT is additive to monomorphization; dict-passing is pulled only by separate compilation or first-class existential constructors, neither present in v1 (bang is whole-program, no existentials). The kernel / `Source.eval` / `HasCTy` stay UNTOUCHED, census byte-identical.
- **Depends-on**: 0075, 0079, 0080, 0068, 0069, 0073
- **Relates-to**: PATH-polymorphism bite-3/4 (this), Q26 (optics / lawful polymorphism — the northstar), Q39 (handler-agnostic + law-conformant IO interfaces — HKT is the mechanism), Task #9 (Option/Result/Either prelude — the instance carriers)

- **Status:** Accepted — scoped by hktscope (2026-07-07), mono-additive core VALIDATED end-to-end. **Implementation (PATH bite-3):** Stage C DONE (`7d887c2`) — concrete-use `fmap inc (Some 5) : Option Int ⇒ 6` (Case A). **Case B DONE (`c27bdb4`)** — abstract-over-f `fn twice … where Functor f` RUNS at TWO Functors (`twice` at Option AND Box, summed ⇒ 14; the write-once payoff). **FINDING (hktB) — the Case-B seam was NOT crossed because it need not be:** under whole-program elaborate-to-mono `twice` is never checked once generically; each use MONOMORPHIZES at the Surf pre-pass (`hktCtorHead`/`hktMatch`/`substCarrierHead`/`hktBfnWrapper` in `expandBFns`), realizing the `f := Option` injectivity decomposition STRUCTURALLY before the checker — which only ever sees concrete types collapsed to `mu`. `embVInst`/`resolveTy` UNTOUCHED; the concrete-collapse path byte-identical. **CONSEQUENCE:** the `IVTy.tcon1` checker substrate (Stages A+B) is confirmed **NOT NEEDED for whole-program HKT** — it would only be pulled by once-checked-generic functions / separate compilation, i.e. the SAME dict-passing trigger this ADR already defers. So A+B is now a **candidate for PRUNING** (dead in v1), not merely unwired. **Stage D DONE (`cea8ae2`) — the tier is complete.** `trait Monad m {pure,bind}` + `impl Monad for Option`: chain `bind (Some 5) …` ⇒ 12 (inner bind/pure un-annotated), short-circuit `bind None …` ⇒ None (error propagation), laws 3/3 (left/right identity, associativity), and the ⭐ Parser-as-monad showpiece (`bind digit {fun a => bind digit {fun b => pure(a*10+b)}}` on "34" ⇒ 34 — do-notation). Rode the SAME Surf-pre-pass mono (no `tcon1`); `pure`'s carrier fixed by its own annotation OR a `carrier?` hint threaded through `expandBFns` (continuation expanded under the enclosing `bind` carrier). Stage-D findings: (a) **Parser-as-monad REQUIRED a nominal `data Parser a`** — an alias `Thunk (…)` has no constructor head for HK resolution, CONFIRMING the ctor-vs-alias seam-to-watch below; (b) a **let-bound monadic computation loses its concrete μ at elaboration** (`let #l = (bind … : Option Int) in match #l` fails "callee not a function") — `optEqLaw` inlines the match directly as a v1 workaround (seam to watch: let-bound Option-computations don't re-establish their μ).
- **Date:** 2026-07-07
- **Layer:** C + surface/checker (tested superset). Frontend LEAF (`Surface`/`TypeCheck`, fan-in 0); census byte-identical, kernel untouched.
- **Builds on:** ADR-0075 (elaborate-to-mono; bidirectional + decidability stratification), ADR-0079 (generic data + `Ty.tApp`/arity — the proto-kind-system), ADR-0080 (bounded generic functions monomorphize per carrier — the `bfnWrapper` this generalizes to constructors), ADR-0068 (Self-based trait/impl + the tested-rung laws), ADR-0073 (`let rec` μ-knot). Reference: Miller's pattern-fragment higher-order unification (the decidable restriction); GHC's constructor-injectivity decomposition; Dunfield-Krishnaswami (bidirectional annotation-required descent).

## Context — the bite-3/4 question (ADR-0075 deferred it here)

PATH-polymorphism bite-3/4 is higher-kinded types: `trait Functor f`, `trait Monad m` — type variables that
range over CONSTRUCTORS (`f : Type→Type`), the "any iterable" / optics northstar (Q26) and the mechanism
that makes effect/IO interfaces handler-agnostic + law-conformant (Q39). Bite-1 (ADR-0079) gave generic
DATA (`data List a`, `Ty.tApp`, arity ≤2); bite-2 (ADR-0080) gave bounded generic FUNCTIONS monomorphized
per carrier. HKT is the next power rung. The questions it forces:
1. Do we need an explicit KIND system, or does bite-1's arity suffice?
2. HK unification is undecidable in general — what is the DECIDABLE fragment, and does it cover Functor/Monad?
3. Does whole-program monomorphization still work, or does HKT FORCE dictionary-passing (the ADR-0080
   revisit-trigger)?

## Decision

**Same elaborate-to-mono seam** — the kernel never learns about kinds or higher-kinded variables:

1. **Kinds are ARITY (reuse bite-1).** A type variable carries a `Nat` arity (a degenerate kind): `f` in
   `Functor f` has arity 1 (`Type→Type`), a plain `a` has arity 0. This reuses bite-1's constructor-param
   count (`GenData.params.length`). Ground kind-checking is already free: `Ty.tApp`'s head must be a declared
   data name (`Option Int` well-formed, `Int Int` unrepresentable). An explicit `Kind` inductive (`Type | k→k`)
   is DEFERRED — needed only for higher-order kinds (monad transformers `data StateT s m a`, `m : Type→Type`
   as an argument), which Functor/Monad do not require.

2. **Higher-kinded type variables solve to CONSTRUCTORS.** `IVTy` gains an applied form `tcon (head) (args)`
   whose `head` can be a constructor name, a hole, or a rigid — because under elaborate-to-mono a HK hole is
   always solved to a concrete constructor NAME at the use, never to an arbitrary type function. Threads
   through resolve/zonk/occurs/unify/freeHoles/abstract/instantiate/embed/extract (the `IVTy`/`ICTy` re-rep
   surface, `b6c66a6`).

3. **HK unification = constructor-injectivity decomposition (DECIDABLE).** `f a ~ Option Int` decomposes to
   `f ~ Option` (a HK-hole ~ a constructor name → bind `f := Option`) and `a ~ Int`. Sound and decidable
   because bang constructors are INJECTIVE — no type families, no reducing synonyms (a generative win: the
   ABSENCE of type families is exactly what buys decidable HOU here). This is inside the Miller pattern
   fragment. Anything outside it (`f a ~ Int`, a metavar applied to non-distinct-rigids) is a TYPE ERROR
   requiring annotation — the ADR-0075 annotation-checked descent, never an unsound guess.

4. **Traits over constructors + polymorphic methods.** `trait Functor f { fmap : (a→b) → f a → f b }`. `Self`
   becomes constructor-kinded and APPLIED (`f a = Self a`); `substSelf` substitutes a constructor NAME into
   `tApp` heads (extending today's nullary `tSelf`). Trait methods are ∀-quantified (`fmap : ∀a b. …`) — the
   impl's method is itself a polymorphic function, composing bite-0 generalize/instantiate (over the method's
   ∀-vars) with bite-2 monomorphize-per-carrier (over `f`). Instance resolution re-keys on the constructor
   NAME (`Functor Option`) rather than a resolved carrier VTy.

5. **Monomorphization — the ADR-0080 fork stays resolved for MONO (NOT re-opened).** At each concrete use
   `f` is pinned (Case A: `fmap inc (Some 5) : Option Int`, `f = Option` from the annotation — exactly
   `bfnWrapper`; Case B: a function abstract over `f` monomorphizes per concrete use, exactly as bite-2's
   `fold` per carrier, because bang is whole-program). `pure : a → m a` rides bite-2's nullary-op
   annotation-driven carrier-fixing (`empty` precedent). Dict-passing is pulled ONLY by separate compilation
   or first-class existential constructors — neither in v1. So HKT is ADDITIVE; the kernel stays monomorphic
   + census byte-identical.

6. **Laws preserved (ADR-0068/0040 tested rung).** Functor laws (`fmap id = id`, `fmap (g∘f) = fmap g ∘ fmap f`)
   and Monad laws (left/right identity, associativity) are Bool-valued equations discharged by evaluation on
   samples — the law body mentions `fmap`/`pure`/`>>=` at concrete instantiations. No new law machinery.

Payoff (target demos): a lawful `Functor Option` — `fmap inc (Some 5) : Option Int ⇒ Some 6`, laws discharge;
`Parser` as a `Monad` (`>>=`/`pure`) reusing `examples/parser-combinators` (the Q26/Q39 handler-agnostic,
law-conformant interface, made concrete). Staged — see PATH-polymorphism bite-3 (Stages A→D).

## Rejected / staged (deferred, NOT forced)

- **Dictionary-passing.** Not refuted (separate-compilation-friendly, effect-idiomatic) — but HKT does not
  introduce its triggers (no existentials, whole-program), so it stays deferred exactly as ADR-0080 left it.
  Revisit if separate compilation or first-class instances are demanded.
- **Explicit `Kind` inductive + higher-order kinds.** Arity-as-`Nat` covers Functor/Monad (first-order
  kinds). The `Kind` inductive + `(Type→Type)→…` kinds are needed only for monad transformers (`StateT s m`);
  deferred until a transformer is a real requirement.
- **Full higher-order unification.** Only the injectivity/pattern fragment is decidable; the rest is
  annotation-required. Not a limitation for Functor/Monad (every method's constructor is concrete at use).
- **Multi-parameter HK traits / HK bounds combined with value bounds (`(Functor f, Ord a) =>`).** v1 is
  single constructor-kinded trait param. Additive.
- **Effect-row-kinded traits (a trait over an effect row / grade).** Q27/Item-3 territory (row variables);
  orthogonal to constructor-kinding.

## Consequences

- The Q26 optics / lawful-polymorphism northstar and the Q39 handler-agnostic + law-conformant IO interface
  become expressible: `Functor`/`Monad` over any prelude constructor, lawful, monomorphized.
- The kernel stays monomorphic + verified — census byte-identical (16 headlines trusted-three),
  `TypeCheck`/`Surface` fan-in-0 leaves; HKT is pure tested-superset.
- bite-3 is a STAGED TIER (Stages A→D in PATH-polymorphism), each a spike+ADR unit — NOT one dispatch.

## Revisit if

Dictionary-passing is demanded (separate compilation / first-class existential instances); OR higher-order
kinds / monad transformers are needed (build the explicit `Kind` inductive); OR a HK-unification case outside
the injectivity fragment must be accepted without annotation (it must not — that would break the decidability
invariant; the correct response is to require the annotation).

**A+B prune-test (hktB):** the `IVTy.tcon1` substrate + its synthetic Stage-A/B unify/kind guards may be
DELETED once the honest test holds — *does any v1 path need a generic function type-checked ONCE?* While the
answer stays NO (whole-program, no separate compilation, no first-class existential constructors) the
substrate is dead and can go. If a future rung ever wants once-checked generics, that is the SAME trigger as
dict-passing — revive the two together.

**Seam to watch:** instance resolution re-keys on the constructor NAME; sound while a constructor name maps to
one data decl. If HK instances for two constructors ever collide on a shared method name resolved by
first-match, thread the expected constructor through (the same disambiguation ADR-0081's "seam to watch"
flags for shared data-constructor names).
