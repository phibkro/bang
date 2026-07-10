<!-- note-status: active -->
# Prelude / standard-library survey — the common core

> A DESIGN SURVEY, not a spec. Surveys the load-bearing prelude constructs across comparable
> languages, then maps each against bang's CURRENT type-power to produce a prioritized menu of what
> to supply. **Extends** `docs/notes/stdlib-map.md` (the third-stratum catalogue, gated by
> type-power) — this note asks the complementary question: given that ladder, which SPECIFIC
> everyday functions do peer preludes ship, and which are supplyable in bang TODAY?
> Established 2026-07-10.
>
> **Sources of truth.** Every "bang can/can't express X today" claim cites the generated reference
> `docs/reference/language.md` (each of its examples is a `lake build`-gated `#guard`, so it cannot
> drift) — the `bang` binary was NOT built in this lane, so nothing here is empirically re-tested;
> claims are reference-cited. Peer-language claims cite the docs consulted (bottom).

## 1. The census — what peer preludes ship

Nine languages: mainstream (Haskell Prelude, OCaml Stdlib, Rust std prelude + `Iterator`, Elm core,
Gleam stdlib, F# Core) and the **effects-native four** (Koka std, Effekt stdlib, Unison base, Flix
stdlib). Frequency = count of the 10 languages shipping the construct in its prelude/core (✓ = ships,
· = absent or non-core). "≈" = ships under a different spelling (e.g. Rust `Iterator::map`).

```
construct        Hs OCaml Rust Elm Gleam F# Koka Effekt Unison Flix  freq  note
────────────────────────────────────────────────────────────────────────────────────────────
LIST
 map             ✓   ✓   ≈    ✓    ✓   ✓   ✓    ✓     ✓     ✓    10/10  the universal core
 filter          ✓   ✓   ≈    ✓    ✓   ✓   ✓    ✓     ✓     ✓    10/10
 foldl/foldr     ✓   ✓   ≈    ✓    ✓   ✓   ✓    ✓     ✓     ✓    10/10  fold[l|r], reduce, fold_left
 length/size     ✓   ✓   ✓    ✓    ✓   ✓   ✓    ✓     ✓     ✓    10/10
 append/++       ✓   ✓   ✓    ✓    ✓   ✓   ✓    ✓     ✓     ✓    10/10
 reverse         ✓   ✓   ✓    ✓    ✓   ✓   ✓    ✓     ✓     ✓    10/10  ← bang HAS (Str only)
 head/tail       ✓   ✓   ≈    ✓    ✓   ✓   ✓    ✓     ✓     ✓     9/10  Option-returning in most
 take/drop       ✓   ·   ✓    ✓    ✓   ✓   ✓    ✓     ✓     ✓     9/10
 zip             ✓   ✓   ✓    ✓    ✓   ✓   ✓    ✓     ✓     ✓    10/10
 concatMap/flatMap✓  ·   ≈    ✓    ✓   ✓   ✓    ✓     ✓     ✓     9/10  flatMap / bind / concat_map
 range           ✓   ·   ≈    ✓    ✓   ✓   ✓    ·     ✓     ✓     8/10  [a..b] / List.range
 replicate       ✓   ·   ≈    ✓    ✓   ✓   ✓    ·     ✓     ✓     8/10
 elem/contains   ✓   ✓   ✓    ✓    ✓   ✓   ✓    ·     ✓     ✓     9/10
 any/all         ✓   ✓   ✓    ✓    ✓   ✓   ✓    ✓     ✓     ✓    10/10
OPTION / RESULT
 map / andThen   ✓   ✓   ✓    ✓    ✓   ✓   ✓    ✓     ✓     ✓    10/10  ← bang HAS map (mapOption/mapResult)
 withDefault     ✓   ✓   ✓    ✓    ✓   ✓   ✓    ✓     ✓     ✓    10/10  fromMaybe / unwrap_or / getOrElse
 isSome/isOk     ✓   ✓   ✓    ✓    ✓   ✓   ·    ·     ✓     ✓     8/10
TUPLE
 fst / snd       ✓   ✓   ≈    ✓    ✓   ✓   ✓    ·     ✓     ✓     9/10  ← dogfood #json top papercut
COMPARISON / ORDER
 compare / Order ✓   ✓   ✓    ✓    ✓   ✓   ✓    ·     ✓     ✓     9/10  ← bang HAS Eq→Order trait (Int)
 min / max       ✓   ✓   ✓    ✓    ✓   ✓   ✓    ✓     ✓     ✓    10/10
NUMERIC
 abs             ✓   ✓   ✓    ✓    ✓   ✓   ✓    ✓     ✓     ✓    10/10
 mod / rem       ✓   ✓   ✓    ✓    ✓   ✓   ✓    ✓     ✓     ✓    10/10  ← issue #102 (no `%` / `mod` yet)
 gcd             ✓   ·   ·    ·    ✓   ·   ✓    ·     ✓     ✓     5/10
STRING / CHAR
 length          ✓   ✓   ✓    ✓    ✓   ✓   ✓    ✓     ✓     ✓    10/10
 concat / ++     ✓   ✓   ✓    ✓    ✓   ✓   ✓    ✓     ✓     ✓    10/10  ← bang HAS (concat)
 toUpper/toLower ✓   ✓   ✓    ✓    ✓   ✓   ✓    ✓     ✓     ✓    10/10  char-level
 split / join    ≈   ·   ✓    ✓    ✓   ✓   ✓    ·     ✓     ✓     8/10
 isDigit/isAlpha ✓   ·   ✓    ·    ✓   ·   ✓    ·     ✓     ✓     6/10  ← dogfood calc/json hand-rolled
IDENTITY / FN
 id / const      ✓   ·   ·    ✓    ✓   ✓   ✓    ·     ✓     ✓     7/10  ← bang HAS id (⑦b example)
 (∘) compose     ✓   ·   ·    ✓    ✓   ✓   ✓    ·     ✓     ✓     7/10  ← bang HAS compose (row-poly example)
```

**The invariant core** (10/10, every language): `map · filter · fold · length · append · zip ·
any/all · Option-map · withDefault · min/max · abs · mod · string-length · string-concat ·
char-case`. This is the floor any prelude is expected to clear.

## 2. The bang gate-map

Each high-frequency construct against bang's CURRENT type-power. Reference facts: generic `List a` +
`map`/`fold`/`filter` **exist** (`docs/reference/language.md` §Standard library note + the ADR-0079
generic-data examples); the injected free stdlib is only `concat`/`reverse`/`eq` over `Str`
(§Standard library table); curried `let rec`s over-approximate to `! {Div}` (#47); the force
convention is `($f) x` and qualified `$(Mod.op) x` (§Modules); generic data arity ≤ 2 (§Types).

Classes: **(a) SUPPLYABLE TODAY** — System-F-typeable, arity ≤ 2, self-recursion only.
**(b) GATED** on a named wall. **(c) POST-V1** — needs typeclass-dispatch or IO.

```
construct           class  wall / note (all citing docs/reference/language.md unless marked)
──────────────────────────────────────────────────────────────────────────────────────────────
map (List a)        (a)    EXISTS — generic List + map shipped (ADR-0079); ref §generic-data.
filter (List a)     (a)    EXISTS — shipped alongside map (ADR-0079).
foldr / foldl       (a)    self-recursive over List a; System-F-typeable. Curried ⇒ `! {Div}` (#47).
length              (a)    single-arg structural rec ⇒ ⊥-row via structOK (dogfood-json GOOD §).
append (List a)     (a)    two-arg; supplyable, types `! {Div}` (curried over-approx, #47).
reverse (List a)    (a)    exists for Str; the List a form is the same shape — supplyable today.
head / tail         (a)    returns `Option a` (prelude Option exists, ADR-0083). Total, ⊥-row.
take / drop         (a)    two-arg (Int, List a) ⇒ `! {Div}` over-approx (#47); still runs.
zip                 (a)*   List a × List b → List (Pair a b). *arity-2 generic data is the CEILING
                           (ref §Types "arity ≤ 2") — `Pair a b` is exactly at it. Supplyable.
any / all           (a)    fold + Bool; Bool = 1+1 exists (ADR-0065). Supplyable.
concatMap/flatMap   (a)    map then concat; both supplyable. Curried ⇒ `! {Div}`.
elem / contains     (a)    needs `eq` on the element — trivial for Int/Str (bang has Str `eq`);
                           GENERIC `elem : Eq a => …` is class (c) (needs Eq-dispatch, below).
range (Int→List)    (a)    self-recursive Int producer; `! {Div}` over-approx. Supplyable.
replicate           (a)    same shape as range. Supplyable.
min / max (Int)     (a)    `if a < b …`; Int `<` exists (ref §operator table). Supplyable.
abs (Int)           (a)    `if n < 0 then 0 - n else n`; supplyable (dogfood calc hand-rolled it).
mod / rem           (b)    ISSUE #102 — no `%` binop and no injected `mod`; today `t-(t/k)*k`.
                           Wall = a new δ-rule + parser-table row (shape (a) in #102), OR inject `mod`.
fst / snd           (a)    ISSUE (dogfood-json papercut) — trivially `let (a,_) = p in a`; supplyable
                           as injected `let`-bindings TODAY. Absence is a stdlib GAP, not a wall.
compare / Order     (a/c)  Int Eq→Order trait EXISTS (ref §Traits, Int instance). GENERIC `compare`
                           over any Ord a is (c) — needs the bounded-trait dispatch through the
                           free stdlib (traits work in decls; injected-generic-fn dispatch is the gap).
withDefault         (a)    `match o { None -> d, Some(v) -> v }`; supplyable, ⊥-row.
isSome / isOk       (a)    single match; supplyable.
string length/concat(a)    concat SHIPPED (ref §Standard library). length = same shape.
char toUpper/isDigit(a)    code-point arithmetic on `Char n` (ref §Strings idioms 97/48/…);
                           supplyable as `let rec` over Char. isDigit = `48 <= n && n <= 57`.
split / join        (a)    List Char recursion; supplyable, `! {Div}`.
id / const          (a)    id SHIPPED (ref ⑦b example). const = `fun x => fun _ => x`. Supplyable.
compose (∘)         (a)    SHIPPED (ref row-poly example, one generic `compose`). Supplyable.
──────────────────────────────────────────────────────────────────────────────────────────────
generic `Functor`/`fmap`  (b)  HKT — DECIDED (ADR-0082, Functor+Monad shipped); a PRELUDE-level generic
                                `fmap`/`>>=` over any `f` rides that rung. See stdlib-map.md §B.
typeclass `show`/`==`     (c)  post-v1 — needs typeclass-polymorphic dispatch through injected fns.
IO / print / readLine     (c)  post-v1 — IO is "a handler at the use site" (stdlib-map.md §C), no
                                console runtime in v1.
```

**The effects-native surprise (the operator's cited question).** *Does `map`'s effect row join the
element function's row?* Three of the four effects-native languages answer **YES, by row-propagation**:

```
Koka     map : (list<a>, (a) -> e b) -> e list<b>       — map itself total; result row = f's row `e`
Unison   List.map : (a ->{𝕖} b) -> [a] ->{𝕖} [b]        — same: caller's ability threads through
Flix     map : (a -> b \ ef, List[a]) -> List[b] \ ef   — `ef` polymorphic; pure f ⇒ pure map
Effekt   map[A,B](l){ f: A => B / {} }: List[B] / {}     — DIFFERENT: signature rows are EMPTY;
                                                            block effects are handled at the CALL SITE
```

The Koka/Unison/Flix shape is exactly what **bang's effect-row polymorphism already gives** (ref: the
"ONE `compose`, generic over its effect row" example — a higher-order fn whose row is its argument's
row). So a bang `map` over an effectful element function threads the row the same way — bang is
already in the majority camp *by construction*, no new mechanism. Effekt's contextual/lightweight
polymorphism (empty rows, effects discharged where `map` is *called*) is the outlier and the biggest
surprise: it means Effekt's `map` signature literally cannot *see* the element effect, trading
row-visibility for a lighter surface. Bang's design (rows visible in the type, `T ! {ρ}`) sides with
Koka/Unison/Flix — the more common and the more type-transparent choice.

## 3. The recommendation

### First slice — supplyable TODAY, ordered by dogfood-demand evidence

All class (a). Ordered by how loudly the dogfood corpus asked (calc/json findings + issues #101/#102):

```
 #  construct        why now (evidence)
 ──────────────────────────────────────────────────────────────────────────────────────
 1  fst / snd        dogfood-json TOP papercut ("first thing most people reach for"); trivial.
 2  length (List a)  10/10 universal; every list program wants it.
 3  append (List a)  10/10 universal; the calc/json parsers hand-rolled concat-like joins.
 4  abs (Int)        both dogfooders hand-rolled `0 - n`; 10/10 universal.
 5  min / max (Int)  10/10; guard-heavy code (calc eval, bounds) wants them.
 6  head / tail      Option-returning; 9/10; list destructuring boilerplate.
 7  take / drop      9/10; slicing shows up in every list-processing program.
 8  isDigit/isAlpha/toUpper/toLower  calc lexer + json parser BOTH hand-rolled code-point tests.
 9  id / const       id already shipped; const is one line and completes the pair (7/10).
10  withDefault (Option/Result)  10/10; pairs with the shipped Option prelude (ADR-0083).
```

(`mod` is demand-rank-high — issue #102, stress session — but it is class (b), so it heads the second
slice, not this one.)

### Second slice — keyed to which walls fall

```
wall that must fall           unlocks
──────────────────────────────────────────────────────────────────────────────
#102 (`%` binop or `mod`)      mod / rem / gcd — the numeric floor (10/10 for mod).
#101 (wildcard `_` arm)        NOT a stdlib fn, but the enabler: multi-ctor container
                               fns (a generic `find`/`lookup` over a big sum) get far
                               cheaper to WRITE without spelling every ctor arm.
#97 item-2 (mutual let rec)    mutually-recursive container walks (tree map/fold) read
                               top-down instead of leaf-first — parser/AST stdlib code.
#47 (Div elimination)          take/drop/append/range STOP over-approximating to `! {Div}`
                               and become genuinely ⊥-row — a precision win, not a new fn.
bounded-trait injected dispatch  GENERIC `elem`/`compare`/`min` over any `Ord a`/`Eq a`
  (ref §Traits works in decls;  (the class-(a/c) split above) — the traits EXIST; the gap
   injected-generic-fn is the gap) is calling them through the free stdlib layer.
HKT prelude surface (ADR-0082)  a prelude-level generic `fmap`/`>>=`/`traverse` (stdlib-map.md §B/§D).
```

### The injection-mechanism fork (SURFACED — operator's call)

Today's stdlib is `stdlibFnSrcs`: **source STRINGS injected into every program's scope** at
type-check (ref §Standard library — `concat`/`reverse`/`eq` are `let rec` source snippets in
`Bang/Frontend/TypeCheck.lean`). The fork as the first slice grows past ~3 functions:

```
option                        pro                              con
──────────────────────────────────────────────────────────────────────────────────────────────
A. keep stdlibFnSrcs strings  zero new machinery; already      strings aren't type-checked in
   (grow the list)            works; no import needed          isolation, no module boundary, no
                              (matches "free in every prog")   `pub`/private, re-parsed every run;
                                                               a 30-fn prelude-as-a-string is a smell.
B. a real prelude MODULE      rides ADR-0093 imports; the      needs the module to be auto-`use`d
   (`Prelude.bang`, auto-used) prelude becomes ORDINARY bang    (no explicit `import Prelude`), and
                              LIBRARY CODE (invariant #5 —      dogfood-calc found `use` won't hoist
                              "abstractions are values"); it    a `pub let rec` (#97 item-3) — so B
                              type-checks, fmt's, tests like    is BLOCKED on that fix for the
                              any module; dogfoods the module   recursive fns that make up most of a
                              system on the stdlib itself.      prelude.
```

**Recommendation: B is the right answer** — a `Prelude.bang` written in bang, auto-imported, is the
single-source-of-truth, invariant-#5-honest form (the stdlib should BE library code, not a string the
checker splices). It also dogfoods ADR-0093 on the most-used code in the language. **Its real cost**:
it is *blocked today* on `use`-hoisting-`pub let rec` (#97 item-3) — most prelude entries are
recursive, and `use` can't currently hoist them. So the honest sequencing is: **ship the first slice
via mechanism A now** (it works, unblocks the demand), and **treat B as the target once #97 item-3
lands** — then migrate the string-prelude into `Prelude.bang` and delete `stdlibFnSrcs`. Naming the
right answer (B) and its cost (blocked on #97-3), per the correctness-first discipline; A is the
named fallback, not a silent default. This is an operator call — I recommend, don't rule.

## 4. Proposed issues (titles + 2-line bodies — DO NOT file from this lane)

1. **feat(stdlib): first-slice prelude functions — `fst`/`snd`/`length`/`append`/`abs`/`min`/`max`/
   `head`/`tail`/`take`/`drop`/`withDefault`/`id`/`const` + char-class kit.**
   All class-(a) supplyable today (see stdlib-prelude-survey.md §3). Ship via `stdlibFnSrcs`
   (mechanism A) now; each is System-F-typeable, arity ≤ 2, self-recursive. `fst`/`snd` is the
   dogfood-json top papercut; the char kit (`isDigit`/`toUpper`) was hand-rolled in BOTH dogfooders.

2. **refactor(stdlib): migrate the injected prelude to a real `Prelude.bang` module (auto-`use`d).**
   Replace `stdlibFnSrcs` string-injection with an ordinary bang module auto-imported into every
   program (invariant #5: the stdlib should BE library code). BLOCKED on #97 item-3 (`use` won't
   hoist a `pub let rec`) — most prelude fns are recursive. Land #97-3 first, then migrate + delete
   the strings.

3. **docs(stdlib): the effect-row-propagation contract for higher-order stdlib fns.**
   Document that bang's `map`/`filter`/`fold` thread the element function's effect row into the
   result (Koka/Unison/Flix shape, already true via bang's row-poly — stdlib-prelude-survey.md §2),
   NOT Effekt's empty-row/call-site-handled shape — so users know an effectful mapper's row surfaces.

---

**Consulted** (2026-07-10): Koka book + row-poly paper (koka-lang.github.io, arxiv 1406.2061 —
`map : (list<a>,(a)->e b)->e list<b>`); Effekt docs effect-polymorphism (effekt-lang.org —
`map[A,B](l){f:A=>B/{}}:List[B]/{}`); Unison docs abilities (unison-lang.org —
`List.map : (a ->{𝕖} b) -> [a] ->{𝕖} [b]`); Flix effect-polymorphism (doc.flix.dev —
`map(f: a -> b \ ef, l): List[b] \ ef`); Gleam `gleam/list` (hexdocs.pm); Elm core `List` +
`Basics` (package.elm-lang.org). Mainstream Haskell Prelude / OCaml Stdlib / Rust std prelude +
`Iterator` / F# Core from primary knowledge. bang facts: `docs/reference/language.md` (build-gated).
