---
type: design-question
title: "Optics as the lawful-polymorphism north-star (+ the HKT fork, + graded optics)"
description: "optics (lens/prism/traversal) as law-carrying stdlib; forces the HKT/F_ω fork; graded optics"
status: open
area: type-system
ties: ["Q27", "ADR-0027", "ADR-0040", "ADR-0069", "ADR-0082"]
see-also: ["docs/notes/stdlib-map.md"]
---
**Status note**: the HKT sub-fork is CLOSED (**ADR-0082**, Functor+Monad shipped); the
optics-as-stdlib northstar below keeps this question OPEN.

**Question**: when and how does bang provide **optics** — composable, first-class, law-carrying
accessors (lens for products, prism for sums, traversal) — as STDLIB, given they gate on the
polymorphism lift and force an unrecorded higher-kinded-types decision?

**Why it matters**: optics are the grown-up dogfood of the pieces bang just built — lawful traits
(ADR-0040) over `data` declarations (ADR-0069). An optic IS a trait carrying its laws (lens:
get-set / set-get / set-set; prism: its build-match pair), checked on the tested rung exactly like
today's `comm` law. So "generic lawful lens over a `data` type" is the natural *validating demo* for
the ADR-0027 HM lift — it proves generic-code-over-a-lawful-interface end to end. And the profunctor /
van-Laarhoven unification forces the **HKT question** (`Functor f`, `Monad f`, `Profunctor p` all
abstract over a type CONSTRUCTOR `f : *→*`), a fork ADR-0027 does NOT cover (it stages to System F,
whose kinds are all `*`). Optics is therefore the lens (pun intended) through which the whole tier-2
stdlib — Functor/Monad/Traversable — comes into focus. See `docs/notes/stdlib-map.md` for the tier.

**Detail** — the encodings tier by required type-power:
```
concrete monomorphic accessor   get/set for ONE fixed type      ~now (traits+data) — but not "optics"
concrete generic optic          Lens s t a b = {get,set},  ∀stab System F (ADR-0027 stage 3)
van-Laarhoven                    ∀f. Functor f ⇒ (a→f b)→(s→f t) HKT (f : *→*) — the fork
profunctor                       ∀p. Profunctor p ⇒ p a b→p s t  HKT + constraint abstraction (F_ω-ish)
```
The bang-native angle: van-Laarhoven optics are parameterized by a `Functor`/`Applicative`
constraint — *effect-shaped*. Bang has **graded effect rows** as first-class kernel structure, so a
**graded / effect-indexed optic** (a traversal whose walk carries `! {ρ}`, grades tracked) is a
question the substrate uniquely poses — standard libraries bolt effects onto traversal awkwardly.

**Options**: (1) **concrete optics at System F** (records of get/set/match/build), forgo the
profunctor unification — no HKT, simpler type system, optics don't compose by bare `∘` (need explicit
combinators). (2) **full profunctor optics** — needs HKT/F_ω; elegant, composes by `∘`, but a much
heavier type + kind system and harder inference. (3) **defer entirely** until HM lands, then decide
(1) vs (2) with the concrete monomorphic lawful accessor as the near-term stepping stone.

**Recommended**: (3) — record now as the polymorphism-lift's validating demo; build the concrete
monomorphic lawful accessor when it's a useful stepping stone; decide (1) vs (2) when HM (ADR-0027
stage 2) lands. Do NOT add HKT speculatively — the same fork gates Functor/Monad, so decide it ONCE,
deliberately, when the first generic container or optic actually needs it.

**Blocked on**: ADR-0027 stage 2 (HM) for any generic optic; a SEPARATE, unrecorded HKT/F_ω decision
for the van-Laarhoven / profunctor forms (this Q is where that fork is first named).

**Revisit signal**: the HM lift starting (ADR-0027 stage 2); OR the first request for generic
containers with `map`/`traverse` (Functor/Monad hit the same HKT fork — decide together); OR anyone
reaching for effectful traversal (the graded-optic research angle).
