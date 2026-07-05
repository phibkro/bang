<!-- note-status: active -->
# Standard-library map — the third stratum

> The stdlib is the THIRD tier of bang's stratification: **kernel → surface → stdlib**. It is
> ordinary LIBRARY code over the five kernel primitives, never native language features (invariant
> #5 — paradigms, runtimes, and abstractions are *values*). This doc is the forward catalogue: what
> to build, gated by the type-system power it needs. A living map, not a spec. Established 2026-07-05.
>
> Companion: `docs/notes/design-space-map.md` (the language-design forks) · ADR-0027 (the
> polymorphism staging this catalogue is gated on) · ADR-0040 (lawful traits) · ADR-0069 (data decls).

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

## The gating axis — type-system power (mirrors ADR-0027 + one unrecorded fork)

```
rung                       provides                          unlocks in the stdlib
──────────────────────────────────────────────────────────────────────────────────────────────
monomorphic (NOW)          concrete data + lawful traits     concrete Option/Result/List/Stack for
  ADR-0040/0069            on FIXED types                    ONE type · the Eq→Order hierarchy on Int
HM (ADR-0027 stage 2)      ∀a parametric poly + generic      generic Option a / List a / Pair a b ·
                           single-param lawful classes       single-param Monoid/Ord/Semigroup a ·
                                                             map/fold/filter · concrete lawful lens
System F (stage 3)         higher-rank ∀                     concrete generic optics (Lens s t a b)
HKT / F_ω  ⚠ UNRECORDED    type-CONSTRUCTOR variables        Functor/Applicative/Monad/Traversable ·
  FORK (Q26)               f : *→* in a class                van-Laarhoven + profunctor optics
graded / effect (native)   effect rows in the interface      generic handler runtimes · GRADED optics
                           (bang already has this in kernel)  (research; Q26)
```

**The HKT fork is the pivot.** Functor, Monad, Traversable, and profunctor optics ALL need to abstract
over a type constructor — beyond ADR-0027's System F ambition. It is one decision, first named in
**Q26**; decide it once, deliberately, when the first generic container or optic forces it — not
speculatively.

## The catalogue

Grouped by concern. **Laws** column = the algebraic laws the abstraction carries (dischargeable on
ADR-0040's tested rung — a stdlib of *lawful* abstractions is the differentiator). Status: ✅ built ·
◑ partial · ○ blocked on the named rung.

### A. Data & containers

```
abstraction        laws                         rung        status / notes
────────────────────────────────────────────────────────────────────────────────────
Bool = 1+1         boolean algebra              mono        ✅ (ADR-0065; if = sugar over case)
Option/Maybe       —                            mono→HM     ◑ monomorphic via `data Opt = None | Some(Int)`
                                                              NOW; generic `Option a` needs HM
Result/Either      —                            mono→HM     ◑ same shape as Option
List a             (functor/monoid laws once     mono→HM     ◑ IntList built (ADR-0069); generic + map/
                    Functor lands)                            fold need HM, Foldable/Traversable need HKT
Stack / Queue      LIFO/FIFO behavioral          mono        ✅ IntStack (Surface demo) · Queue TODO
Map / Set          lookup/insert laws            HM+Ord      ○ needs generic Ord (HM) + a tree/assoc impl
Vec (fixed)        AddCommGroup                  mono        ✅ `data Vec = Vec(Int,Int)` + Add (ADR-0069)
```

### B. Lawful algebra (the trait hierarchy)

```
abstraction              laws                              rung      status
──────────────────────────────────────────────────────────────────────────────────
Eq / Preorder / Order    refl·sym / +trans / +antisym      mono      ✅ Trait.lean (Int instance)
Semigroup / Monoid       assoc / +identity                 mono→HM   ○ monomorphic buildable; generic = HM
AddCommGroup / Ring       group + distributivity            mono      ◑ Int's ops exist (ADR-0065/67 = ℤ);
                                                                        the trait hierarchy TODO
Functor / Applicative / Monad   the functor/monad laws      HKT ⚠     ○ blocked on the Q26 HKT fork
Foldable / Traversable   naturality / linearity            HKT ⚠     ○ same
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
· the STM transaction handler + ledger (ADR-0030) · the state / throws kernel handlers. Monomorphic
`Option`/`Result` are expressible via `data` decls TODAY (they just aren't generic yet).

## Sequencing (what unlocks what)

```
NOW (mono)        concrete lawful accessors · Monoid/Ring hierarchy on Int · monomorphic Option/Result
HM (stage 2)      generic Option/List/Pair · single-param Monoid/Ord · map/fold/filter · GENERIC lawful
                    lens (the ADR-0027-validating demo — Q26)
System F (stage3) concrete generic optics · higher-rank combinators
HKT decision ⚠    Functor/Monad/Traversable · van-Laarhoven & profunctor optics — ONE fork (Q26),
                    decide when the first generic container/optic forces it, not before
native/graded     generic handler runtimes · graded optics (research)
```

The instinct throughout: a stdlib abstraction is LIBRARY code (invariant #5). If you find yourself
wanting to add a keyword for it, stop — the kernel already supports it; what's missing is only the
type-system power to write its *generic* form, and that's the ADR-0027 ladder, not a language feature.
