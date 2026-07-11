<!-- note-status: active -->
# Traits / typeclasses prelude survey — the census + the derivability matrix

> A DESIGN SURVEY, not a spec. The **sibling of `docs/notes/stdlib-prelude-survey.md`**: that note
> surveyed prelude FUNCTIONS; this one surveys prelude TRAITS/classes and, per trait, whether an impl
> is mechanically DERIVABLE from a data decl's shape. Same style: reference-cited, table-heavy.
> Established 2026-07-11.
>
> **Sources of truth.** Every "bang can/can't express X today" claim cites the generated reference
> `docs/reference/language.md` (§Traits & Laws — each grammar form is a `lake build`-gated `#guard`
> in `Bang/Frontend/Surface.lean`, so it cannot drift), an ADR, or an issue. The `bang` binary was
> NOT built in this lane (docs-only) — **nothing here is empirically re-tested; all bang claims are
> cited.** Peer-language claims cite the docs consulted (bottom).

## 0 · What a bang trait IS today (the ground this sits on)

`docs/reference/language.md` §Traits & Laws (ADR-0040 §5, ADR-0068): a **trait** = zero-or-more
Self-typed op SIGNATURES (`fn op(a,b) -> T`, tuple-style, every param `Self`) + zero-or-more first-class
`law` clauses (`law comm(a,b): add a b == add b a`, Bool-valued equation, curried-call bodies). An
**impl** supplies op bodies for one STRUCTURAL target (`impl Add for (Int * Int)`). v1 traits are
**Self-only** — no HK `[]` params at the base tier (ADR-0068); HKT (`Functor f`) is an additive tier
(ADR-0082, below). Laws land on the **tested rung** (decidable predicate over `Source.eval` runs,
sample-checked) — the verified rung stays Lean-level until a meta-elaborator climbs (ADR-0068 dec. 1;
Q43 = the climb, `proof-export-survey.md`). `bang test` sample-checks every discovered law (30
Int-tuple samples, fixed seed — §Traits & Laws, issue #60).

**The load-bearing usability constraint (issue #78, park ratified 2026-07-11):** trait ops are
**operator-dispatch-ONLY** — `env.insts` is consulted solely in the `.binopS` arm. A trait op called BY
NAME (`add(x,y)` or a sibling op) has **no execution path**; and `impl Eq for Int` is **permanently dead**
(the kernel Int δ-rule wins `==` before `env.insts` — the built-in-shadowing trap). This splits every
recommendation into *usable-today* (binop-shaped ops) vs *gated-on-#78-unpark* (name-callable ops).

## 1 · The census — Q1

Ten precedents: the two big deriving cultures (Rust `#[derive]`, Haskell `deriving`), the interface langs
(PureScript, Idris 2 `%deriving`, Scala 3 `derives`), the protocol/synthesis langs (Swift), the
no-typeclass contrast (OCaml `ppx_deriving`, Gleam/Elm builtin structural `==`), and **Lean 4 itself** —
the closest precedent, since bang's elaborator IS Lean and a bang derive handler would mirror Lean's
`deriving` handler mechanism directly. Frequency = count shipping the class in prelude/std (✓ ships as a
first-class class/protocol; ≈ ships under another spelling; d = also has a DERIVE path for it; · absent).

```
class            Rust Hs PureS Idris2 Lean4 Scala3 Swift OCaml Gleam Elm   freq  derive-path count
──────────────────────────────────────────────────────────────────────────────────────────────────
Eq / ==          ✓d  ✓d  ✓d   ✓d    ✓d(BEq) ✓    ✓d    ≈d   built built 10/10  8 (all but Gleam/Elm*)
Ord / compare    ✓d  ✓d  ✓d   ✓d    ✓     ✓     ✓d    ≈d    ✓    ✓     10/10  7
Show / Display   ✓d  ✓d  ✓d   ✓d    ✓d(Repr) ✓  ✓d    ≈d    ≈    ≈      9/10  8  (Debug/Repr/Show)
Hash             ✓d  ✓d  ·    ·     ✓d    ✓     ✓d    ≈d    ·    ·      6/10  6
Default/Inhabited✓d  ·   ·    ✓     ✓d(Inhab) ·  ·     ·    ·    ·      4/10  3
Clone/Copy       ✓d  n/a n/a  n/a   n/a   n/a   n/a   n/a  n/a  n/a     1/10  1  (Rust-only; GC langs auto)
Semigroup/Monoid ≈   ✓   ✓    ✓     ·     ✓     n/a   ·    ✓    ·       6/10  0  (no canonical instance!)
Functor/fmap     n/a ✓   ✓    ✓     ·     ✓     n/a   ·    ·    ≈       5/10  4  (Hs stock, PS/Idris/Scala)
Applicative      n/a ✓   ✓    ✓     ·     ✓     n/a   ·    ·    ≈       5/10  0
Monad / bind     n/a ✓   ✓    ✓     ✓(Monad) ✓  n/a   ·    ·    ≈       6/10  0  (never derived — a choice)
Foldable         n/a ✓   ✓    ✓     ·     ✓     n/a   ·    ·    ·       4/10  4  (Hs DeriveFoldable)
Traversable      n/a ✓   ✓    ✓     ·     ✓     n/a   ·    ·    ·       4/10  4
Num / +          ≈(ops)✓ ✓   ✓     ·     ✓(Numeric)· ≈   ·    ·       5/10  0
Enum/Bounded     ✓(≈) ✓  ✓    ✓     ·     ✓     ✓(Case)·  ·    ·       6/10  5
Codable/Serialize ✓(serde-d)· ·   ·     ·     ✓(d) ✓d    ✓d   ✓d   ✓d    6/10  6  (a fold — always derived)
```
*Gleam/Elm: structural `==` is a BUILTIN operator, not a user class — no derive because no class.

**The invariant deriving core** (≥8/10 AND ≥6 derive-paths): **`Eq` · `Ord` · `Show` · `Hash`** — the
four every deriving culture supplies as a mechanical fold over data shape. Below them, two clusters split
by a sharp line the matrix (§2) formalizes: the **structural cluster** (also `Default`, `Enum/Bounded`,
`Codable` — a pure fold) vs the **choice cluster** (`Semigroup`/`Monoid`/`Monad`/`Num` — **0 derive-paths
anywhere**, because there is no canonical instance to synthesize).

**Lean 4 (the closest precedent).** Ships BEq/DecidableEq/Repr/Inhabited/Hashable/Ord via **`deriving`
handlers** — a `DerivingHandler` (`Array Name → CommandElabM Bool`) registered per class that INSPECTS the
inductive's constructors/fields and EMITS the instance. The exact mechanism bang reuses: bang's elaborator
IS Lean, its `data` decl already lowers to a μ-sum-of-products (ADR-0069) a handler folds over.

## 2 · The derivability matrix — Q2

Per class: is an impl a **pure fold over the data decl's ctor/payload shape** (a), derivable only via a
**strategy/wrapper** (b), or a **genuine choice** (c)? bang's data decl `data T = C₀(…) | C₁(…)` lowers
to `μX. p₀ + (p₁ + …)` with `pᵢ` = the k-ary product payload (ADR-0069 dec. 2) — the elaborator ALREADY
HAS this shape, so a derive handler is a fold over exactly it.

```
class       kind  generated impl in BANG terms (fold over the ADR-0069 μ-sum-of-products)
────────────────────────────────────────────────────────────────────────────────────────────────────
Eq          (a)   per ctor: same-tag ⇒ AND over payload-slot Eq (recurse at μ); diff-tag ⇒ false.
                  A `case`/`case` diagonal over the sum + `split` over each product. Fold, no choice.
Ord/compare (a)   ctor-index order = decl order (ADR-0069 "sum by decl order" — the tag IS the ordinal);
                  ties broken left-to-right lexicographically over payload slots. Pure structural fold.
Show/Repr   (a)   ctor name ++ "(" ++ (Show over each payload slot, comma-joined) ++ ")". Needs the ctor
                  NAMES at the fold site (→ #108 interaction, §3). Fold over sum+product.
Hash        (a)   mix(tag, hash(slot₀), hash(slot₁), …) — fold, any fixed mixing fn. (Needs a hash
                  primitive/δ-rule on Int/Char first — a stdlib gap, not a wall.)
Default     (a')  first nullary ctor, else C₀ with each slot's Default (recurse). Fold, but PARTIAL:
                  a type with no base case (`data S = C(S)`) has no Default — the handler fails-loud.
Enum/Bounded(a)   nullary-only sums: minBound=C₀, maxBound=Cₙ, succ = tag+1. Fold over the sum, reject
                  if any ctor has payload (the Haskell restriction). Structural.
Codable     (a)   the fold IS the (de)serializer: tag → key, payload slots → fields. Same shape as Show
                  in reverse. Structural — every language derives it because it's a fold.
Functor     (b)   over `data T a` — map the type param through payload slots that mention `a`, leave
                  others. Derivable (Haskell DeriveFunctor) BUT needs the HKT tier (ADR-0082) to even
                  DECLARE `Functor f`; and needs to know WHICH slots are the param. Strategy-ish.
Foldable/   (b)   same as Functor: fold/traverse the `a`-typed slots. Derivable given HKT + param
Traversable       tracking. Post-ADR-0082 tier.
Semigroup/  (c)   NO canonical instance — `(+)` vs `(*)` vs first-wins vs last-wins are all lawful
Monoid            monoids on the same carrier. Haskell's answer is `newtype Sum`/`Product`/`First` WRAPPERS
                  (a via-strategy), never a stock derive. Genuine CHOICE — 0/10 languages derive it.
Monad/bind  (c)   the bind is the POINT of the type (Parser, State, …) — no structural default exists.
                  0/10 derive-paths. Always hand-written. (ADR-0082 ships it as a hand-impl trait.)
Num/+       (c)   which arithmetic? no structural fold. Choice.
Clone/Copy  (a)   structural (deep-copy each slot) but IRRELEVANT to bang: values are immutable thunks,
                  no ownership model — no Clone/Copy distinction to make. Drop from the recommendation.
```

**The line (the reusable criterion, = `laws-taxonomy.md` §1 applied to derivation):** a class is
**structurally derivable ⟺ its impl is determined by the carrier's shape** (Eq/Ord/Show/Hash/Default/
Enum/Codable — "this thing IS a structure", model-shaped, one fold). A class is a **choice ⟺ multiple
lawful impls exist on one carrier** (Semigroup/Monad/Num — the instance is INFORMATION, not derivable).
Functor sits between: structurally determined BUT gated on HKT to even name. This line is exactly the
model-shaped/morphism-shaped split — derivability tracks "is the answer forced by the shape".

**The bang differentiator (nobody ships this).** A bang trait carries first-class `law` clauses
(§Traits & Laws). So a DERIVED impl can **auto-attach its trait's laws**, and `bang test` sample-checks
them **for free** at zero user cost — *derived-AND-law-checked*. None of the 10 surveyed languages ship
this: Rust/Haskell/Lean derive the impl but the laws live in prose/docs, unchecked. Then Q43
(`proof-export-survey.md`) makes it **derived-AND-PROVEN** — a `#prove` pragma exports the auto-attached
law as a Lean goal over the elaborated `Comp`, discharged once, content-addressed cached, scoped to the
total fragment (where derived structural impls LIVE — a fold over a finite ADT is ⊥-row). The ladder is
bang-native: **derive the impl → auto-attach the law → sample-check free → prove on demand.**

## 3 · The bang gate-map — per recommended trait, honest per-item

Classes: **usable TODAY** (binop-dispatch shape, #78 no blocker) / **gated on #78-unpark** (name-callable
ops) / **gated on HKT tier** (ADR-0082 — verified below) / **gated on #108** (derive must name ctors).

```
trait        dispatch-shape today          derive-shape        gate
──────────────────────────────────────────────────────────────────────────────────────────────────
Eq / ==      USABLE (binop `==` arm)       (a) fold            derive gated on #108 (fold names ctors);
                                                               dispatch works NOW for user data via `==`.
Ord / <      USABLE (binop `<` arm)         (a) fold           same: `<` dispatches today; derive → #108.
Show         GATED #78 (no `show` binop —   (a) fold           `show x` is a NAME call ⇒ no exec path
             it's a name call, not an op)                      today (#78). Derive-shape ready; dispatch
                                                               blocked until #78 unparks (Stage-7/Q38).
Hash         GATED #78 (name call)          (a) fold           needs a hash δ-rule (stdlib gap) + #78.
Default      GATED #78 (name call)          (a') partial fold  name-call blocked (#78); fold ready.
Enum/Bounded GATED #78 (name call)          (a) fold           name-call blocked (#78).
Codable      GATED #78 (name call)          (a) fold           name-call blocked (#78); JSON dogfood ask.
Functor/Monad GATED HKT — but SHIPPED       (b)/(c)            **ADR-0082 VERIFIED: Functor+Monad ship as
             as hand-impls (ADR-0082)                          HAND-WRITTEN traits (Stages C/D done,
                                                               `cea8ae2`); NOT auto-derived.** fmap/bind
                                                               dispatch works at concrete carriers via the
                                                               Surf mono pre-pass — a NAME-call path that
                                                               EXISTS for HKT methods (unlike #78's binop
                                                               gap). Deriving them = future (b) slice.
Semigroup/   —                              (c) not derivable  a genuine choice; ship via-wrappers if at
Monoid                                                         all. Not a derive target.
```

**The dead-impl trap (must fix BEFORE deriving, or derives are silently dead).** #78 fact 3: `impl Eq
for Int` is permanently unreachable (kernel δ-rule wins `==`). So a derive mechanism MUST target **USER
`data` only** — never a built-in carrier — or emit dead code. This is a hard constraint on the derive
handler's carrier check, not a nice-to-have. (The #74-fix warning flags the manual case; the derive
handler should refuse built-in carriers outright.)

**#108 interaction (ruled 2026-07-11, option a).** Ctors are being **type-namespaced** (bare names
resolve when unambiguous). A `Show`/`Eq` derive must name the carrier's ctors in its fold — so the derive
handler runs **POST-namespacing** (it reads the resolved, per-type ctor set), never pre-. The #108 probe
that pins the resolution rules is the prerequisite for a robust `Show` derive (which prints ctor names).

**#74/#60 law-execution state (verified this lane).** #60 (law runner) and #74 (the `app: callee is not
a function` bug) are BOTH **CLOSED**. But #78 confirms the *underlying* gap stands: law bodies that call
a trait op by name still have no exec path (that IS #78's item 1) — #74's fix turned the opaque crash
into a clear diagnostic, it did not wire name-dispatch. So **law-checking of derived impls is blocked on
the same #78 unpark** as name-callable ops: today only binop-shaped laws (`a == b`, `a < b`) actually
run through `bang test`; a law calling `show`/`hash` by name reaches the #78 diagnostic, not PASS/FAIL.

## 4 · The recommendation — sequenced trait-prelude + the derive mechanism

### Tier 1 — ships with TODAY's dispatch + a derive handler for the binop-shaped pair

```
 trait   why now                                            derive     gate to clear first
 ───────────────────────────────────────────────────────────────────────────────────────────
 Eq      binop `==` dispatches TODAY on user data; the      (a) fold   #108 landing (ctor-namespacing
         floor of every container fn (elem/lookup/dedup).               probe, ruled+queued) → then the
 Ord     binop `<` dispatches TODAY; sort/min/max/BST.       (a) fold   derive handler targets USER data
                                                                        only (dead-impl trap, §3).
```

Tier 1 is deliberately the two classes whose ops are **already binop-dispatched** (`==`, `<`) — so the
derived impl is *usable the moment it's synthesized*, no #78 dependency. Both are pure structural folds
over ADR-0069's μ-sum-of-products; both carry canonical laws (`Eq`: refl/sym/trans; `Ord`: the total-order
laws) that **auto-attach and sample-check for free** — the differentiator, shipped in tier 1.

### Tier 2 — post-#78-unpark (Stage-7/Q38), the name-callable classes

`Show` · `Hash` · `Default` · `Enum/Bounded` · `Codable` — all (a) folds, all derive-ready, all blocked
ONLY on #78's name-call path (their ops aren't operators). They land the day trait ops become
name-callable — which #78 ruled is decided together with the Stage-7/Q38 handler surface. No new derive
machinery, just the dispatch unblock. (`Codable`/JSON is the loudest dogfood ask here — `dogfood-json`.)

### Tier 3 — the HKT deriving slice (post-ADR-0082-consolidation)

`Functor`/`Foldable`/`Traversable` deriving (kind (b) — map the type param through payload slots). Functor
and Monad already SHIP as hand-written traits (ADR-0082, verified); this tier adds the *auto-derive* fold.
Needs param-slot tracking on top of the existing HKT mono pre-pass. Not near-term.

### The derive-mechanism shape (the recommendation's core)

**Elaboration-level, Lean-`DerivingHandler`-style, laws auto-attached.** A `deriving (Eq, Ord)` clause on
a `data` decl (or a standalone `derive Eq for T`) runs a handler in the elaborator that (1) reads the
carrier's resolved μ-sum-of-products (ADR-0069, post-#108-namespacing), (2) emits the impl as a fold
(the §2 sketches), (3) **auto-attaches the trait's declared `law` clauses** so `bang test` picks them up
free. This mirrors Lean's own mechanism exactly — the smallest-surprise choice since the elaborator IS
Lean. It rides the tested rung (ADR-0068 dec. 1); Q43 lifts derived laws to proven on demand.

### ADRs vs issues

- **ADR** — "Deriving handlers: structural traits derive as a fold over the ADR-0069 μ-sum-of-products;
  derive targets USER data only (dead-impl trap); handler runs post-#108-namespacing; laws auto-attach to
  the tested rung." A genuine fork (elaboration-time derive vs hand-impl-only vs macro) a future session
  could relitigate → ADR. Records the rejected alternative (no-derive: keep all impls hand-written).
- **Issues** — the concrete slices (below). Tier-1 derive is an issue riding the ADR; the #78-gated tier
  is tracked by #78 itself.

## 5 · Proposed issues (titles + 2-line bodies — DO NOT file from this lane)

1. **feat(traits): `deriving (Eq, Ord)` — structural derive handler over the ADR-0069 μ-sum-of-products.**
   An elaboration-level derive (Lean-`DerivingHandler`-style) emitting Eq/Ord as a fold over the carrier's
   ctor/payload shape; targets USER `data` only (dead-impl trap, #78); auto-attaches the trait laws to the
   tested rung so `bang test` checks them free. Tier 1 — both ops are binop-dispatched today. Gated on #108.

2. **feat(traits): tier-2 derives — `Show`/`Hash`/`Default`/`Enum`/`Codable` (blocked on #78 unpark).**
   All (a) structural folds, derive-ready, but their ops are NAME calls (not operators) so they have no
   exec path until #78 (trait-op name-callability, parked to Stage-7/Q38) lands. Land the derive fold now,
   gate activation on #78. `Codable` is the dogfood-json ask.

3. **design(traits): the derive-handler ADR — fold-over-μ mechanism, dead-impl carrier check, law
   auto-attach, post-#108 ordering.** Pin the elaboration-time derive design (vs hand-impl-only) as an
   ADR; record the USER-data-only constraint and the derived→attached→checked→proven (Q43) ladder that no
   surveyed language ships.

---

**Consulted** (2026-07-11): Rust `#[derive]` + std prelude traits (doc.rust-lang.org); Haskell Report
`deriving` + strategies stock/newtype/anyclass/via + DeriveFunctor/Foldable/Traversable (haskell.org, GHC
guide); PureScript `Data.Generic.Rep` (pursuit); Idris 2 `%deriving` (idris2 docs); **Lean 4 `deriving`
handlers — `DerivingHandler = Array Name → CommandElabM Bool`; BEq/DecidableEq/Repr/Inhabited/Hashable/Ord**
(leanprover.github.io, Lean core `Deriving/`); Scala 3 `derives`+`Mirror`; Swift synthesized Equatable/
Hashable/Codable (swift.org); OCaml `ppx_deriving`; Gleam/Elm builtin structural `==` (no class). bang
facts: `docs/reference/language.md` §Traits & Laws (build-gated), ADR-0068/0069/0079/0082/0040 §5,
`laws-taxonomy.md`, `proof-export-survey.md` (Q43), issues #78/#108/#106/#97-3/#74/#60. NOT empirically
tested — `bang` binary not built.
