<!-- note-status: active -->
# Standard-library map — the third stratum

> The stdlib is the THIRD tier of bang's stratification: **kernel → surface → stdlib**. It is
> ordinary LIBRARY code over the five kernel primitives, never native language features (invariant
> #5 — paradigms, runtimes, and abstractions are *values*). This doc is the forward catalogue: what
> to build, gated by the type-system power it needs. A living map, not a spec. Established 2026-07-05.
>
> Companion: `docs/notes/design-space-map.md` (the language-design forks) · ADR-0027 (the
> polymorphism staging — now SHIPPED via ADR-0075) · ADR-0040 (lawful traits) · ADR-0069 (data decls).

## The three strata (the load-bearing frame)

```
KERNEL     5 primitives: thunk · force · effect rows · handlers · STM        (frozen; invariant #5)
   │         everything below is DEFINED over this — no new primitives
   ▼
SURFACE    concrete syntax + ergonomic sugar: data/trait/impl/law · do · if ·  (ADR-0065/66/68/69)
   │         match · => · A-normalization · operator resolution
   ▼
STDLIB     reusable generic abstractions — LIBRARY VALUES, not features:       ← THIS DOC
             containers · lawful algebra · effect/handler runtimes · optics
```

The stratification is the moat: what other languages bake in as keywords (`async`, `actor`,
exceptions, generators, `lens`), bang provides as library values over the kernel. The *only* reason
a stdlib abstraction isn't buildable today is the **type-system power** its generic form needs —
which is exactly ADR-0027's staging axis.

## The gating axis — type-system power (mirrors ADR-0027; the poly ladder is now SHIPPED)

```
rung                       provides                          unlocks in the stdlib          status
──────────────────────────────────────────────────────────────────────────────────────────────────────
monomorphic                concrete data + lawful traits     concrete Option/Result/List/Stack ·      ✅
  ADR-0040/0069            on FIXED types                    the Eq→Order hierarchy on Int
HM + row-poly              ∀a parametric poly + generic      generic Option a / List a / Pair a b ·   ✅ cea8ae2
  ADR-0027 stage 2         single-param lawful classes +     single-param Monoid/Ord/Semigroup a ·      ADR-0079/0080/0081
  (5d0a32f)                effect-row variables              map/fold/filter · effect-generic combinators
System F (stage 3)         higher-rank ∀                     concrete generic optics (Lens s t a b)   ○ frontier
HKT — DECIDED (ADR-0082)   type-CONSTRUCTOR variables        Functor/Applicative/Monad/Traversable ·  ✅ Functor+Monad
                           f : *→* in a class                van-Laarhoven + profunctor optics          (Applic./Trav./optics TODO)
graded / effect (native)   effect rows in the interface      generic handler runtimes · GRADED optics  ○ research (Q26)
                           (bang already has this in kernel)  (research; Q26)
```

**The HKT fork is DECIDED — ADR-0082** (Functor + Monad shipped; monomorphize kinds-as-arity). Functor,
Monad, Traversable, and profunctor optics all abstract over a type constructor `f : *→*` — the decision
**Q26** first named. Applicative/Traversable and the van-Laarhoven/profunctor optics ride the same rung
and remain the forward frontier (Q26).

## The catalogue

Grouped by concern. **Laws** column = the algebraic laws the abstraction carries (dischargeable on
ADR-0040's tested rung — a stdlib of *lawful* abstractions is the differentiator). Status: ✅ built ·
◑ partial · ○ blocked on the named rung.

### A. Data & containers

```
abstraction        laws                         rung        status / notes
────────────────────────────────────────────────────────────────────────────────────
Bool = 1+1         boolean algebra              mono        ✅ (ADR-0065; if = sugar over case)
Option/Maybe       —                            HM          ✅ generic `Option a` — prelude (ADR-0083)
Result/Either      —                            HM          ✅ generic + Either-as-builtin-sum (ADR-0083)
List a             functor/monoid/fold laws      HM/HKT      ✅ generic `List a` + map/fold/filter (ADR-0079);
                                                              Foldable/Traversable ride HKT (ADR-0082)
Stack / Queue      LIFO/FIFO behavioral          mono        ✅ IntStack (Surface demo) · Queue TODO
Map / Set          lookup/insert laws            HM+Ord      ○ generic Ord now available (HM); tree/assoc impl TODO
Vec (fixed)        AddCommGroup                  mono        ✅ `data Vec = Vec(Int,Int)` + Add (ADR-0069)
```

### B. Lawful algebra (the trait hierarchy)

```
abstraction              laws                              rung      status
──────────────────────────────────────────────────────────────────────────────────
Eq / Preorder / Order    refl·sym / +trans / +antisym      mono      ✅ Trait.lean (Int instance)
Semigroup / Monoid       assoc / +identity                 HM        ✅ generic bounded traits (ADR-0080)
AddCommGroup / Ring       group + distributivity            mono      ◑ Int's ops exist (ADR-0065/67 = ℤ);
                                                                        the trait hierarchy TODO
Functor / Applicative / Monad   the functor/monad laws      HKT       ✅ Functor + Monad (ADR-0082); Applicative TODO
Foldable / Traversable   naturality / linearity            HKT       ◑ HKT decided (ADR-0082); impl TODO
```

### C. Effect / handler runtimes — "runtimes are values"

The payoff of the kernel design: what other languages make language features, bang provides as
**handler libraries**. The *effect* is kernel-supported today; the *generic reusable* handler needs
polymorphism over the carried value.

```
runtime            mechanism                                rung        status
────────────────────────────────────────────────────────────────────────────────────
State              state handler over the state effect      mono→HM     ✅ kernel handler (get/put); generic
                                                                          `State s` needs HM
Exception/throws   throws handler                           mono→HM     ✅ kernel (raise/handle)
Reader / Writer    handler over an ask/tell effect          HM          ○ library over the kernel
STM                transaction handler (ADR-0030)           mono        ✅ v1 single-threaded; concurrent = Q21
Reactive cell      `=` = equality over thunks (ADR-0005)    mono        ✅ cellComp demo
Async / scheduler  handler + green threads (stack-switch)   HM+         ○ post-v1; the multikernel (design-map §)
Generators/coroutines  handler over a yield effect          HM          ○ library — no `yield` keyword (the moat)
Actors             `!` send over a mailbox effect+handler   HM+         ◑ `!` reserved; needs concurrency
IO                 handler at the use site (a runtime)      mono→HM     ◑ the runtime-is-a-handler story
```

### D. Optics (Q26 — the lawful-polymorphism north-star)

```
optic              encoding                                 rung        status
────────────────────────────────────────────────────────────────────────────────────
concrete accessor  get/set for ONE fixed type               mono        ○ near-term stepping stone
Lens s t a b       {get: s→a, set: s→b→t} + 3 laws          System F    ○ ADR-0027 stage 3
Prism              {match: s→t+a, build: b→t} + laws         System F    ○ same
van-Laarhoven      ∀f. Functor f ⇒ (a→f b)→(s→f t)          HKT ⚠       ○ the Q26 fork
Profunctor optic   ∀p. Profunctor p ⇒ p a b → p s t         HKT+ ⚠      ○ composes by ∘; heaviest
Graded optic       traversal carrying `! {ρ}`               native      ○ RESEARCH — bang's novel angle (Q26)
```

### E. bang-native / research (the substrate says something new)

```
graded optics          effect-indexed traversal, grades tracked        Q26 — no neighbour does this cleanly
the runtime-as-value    schedulers/IO/async all handler VALUES chosen   the moat; §5 of the design thesis
  library               at the use site, not language features
serializable thunks     ships code @ the data (Unison-like)             Distribution.lean / design-map §DSL
```

## What's ALREADY built (don't rebuild — extend)

`Bool` + arithmetic + comparisons (ADR-0065) · the `Eq→Preorder→Order` trait hierarchy + `Int`
instance + `OrderedPair` (`Bang/Frontend/Surface/Trait.lean`) · `IntList` + `IntStack` (ADR-0069 +
the Surface Stack demo) · `Vec` + `Add` (the ADR-0069 northstar) · the reactive cell (`=`, ADR-0005)
· the STM transaction handler + ledger (ADR-0030) · the state / throws kernel handlers.
**The polymorphism ladder SHIPPED (`cea8ae2`), all elaborate-to-mono (ADR-0075) over the UNTOUCHED
kernel:** generic `Option`/`Result`/`Either` (prelude, ADR-0083, + first witnessed isomorphisms) ·
generic data `List a`/`Pair` + map/fold/filter (ADR-0079) · bounded generic traits incl. `Monoid`
(ADR-0080) · annotation-free generic intro (ADR-0081) · HKT `Functor` + `Monad` with laws (ADR-0082)
· effect row-polymorphism (`5d0a32f`).

## Sequencing (what unlocks what)

```
✅ SHIPPED       generic Option/List/Pair · map/fold/filter · Monoid/Ord bounded traits · HKT Functor+
                   Monad (ADR-0079/0080/0081/0082/0083) · effect row-poly — all elaborate-to-mono (ADR-0075)
System F         concrete generic optics · higher-rank combinators — the forward frontier
HKT — DECIDED    Applicative/Traversable · van-Laarhoven & profunctor optics ride the ADR-0082 rung (Q26)
native/graded    generic handler runtimes · graded optics (research)
```

The instinct throughout: a stdlib abstraction is LIBRARY code (invariant #5). If you find yourself
wanting to add a keyword for it, stop — the kernel already supports it; the type-system power to write
its *generic* form is the ADR-0027 ladder (now SHIPPED via ADR-0075), not a language feature.
