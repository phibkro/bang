# parser-combinators

A **parser-combinator library written in bang** — the acceptance test for the
polymorphism milestone (ADR-0075 higher-order + ADR-0079 generic data + **#55
annotation-free generic introduction**). It proves the capabilities *compose into
a real reusable library with GENERIC combinators that RUN*.

## What it is

A parser is a thunked function

```
Parser a = Thunk (Str -> Option (a * Str))
```

consume a prefix of the input, return `Some((value, rest))` on success or `None`
on failure. With #55 the result type is **itself generic** (`Parser a`): `mapP`
and `orElse` are `∀ a b`, and every `Some(…)` is built with **no annotation** —
the element type is *inferred* from the fields (see *How #55 lifts the walls*).

## What it demonstrates

| combinator | signature | capability exercised |
|---|---|---|
| `satisfy`  | `(Int -> Bool) -> Parser Int`            | higher-order (predicate → parser) |
| `char`     | `Int -> Parser Int`                      | specialization of `satisfy` |
| `mapP`     | `(a -> b) -> Parser a -> Parser b`       | **fully generic** map (b inferred, no annotation) |
| `orElse`   | `Parser a -> Parser a -> Parser a`       | **generic** ordered choice `<\|>` |
| `andThen`  | `Parser Int -> Parser Int -> Parser Int` | sequencing (bind); value = sum |
| `many`     | `Parser Int -> Str -> Int`               | recursive fold (zero-or-more) |

- **Generic data, annotation-free** — `data Option a` constructed at `Option (Int *
  Str)`, `Option ((Int*Int) * Str)`, … with **no** `: Option …` at any site; the
  instantiation is inferred from the constructor's fields (#55).
- **Higher-order polymorphism** — every combinator takes thunked parsers/functions
  and applies them; `digit = mapP sub48 (satisfy isDigit)` composes two combinators.
- **Genericity witness** — the ONE `mapP` is reused at result type `(Int * Int)`
  (`pairP = mapP {fun v => (v, v)} digit`), proving `Parser a → Parser b` with `b ≠ a`.

The demo runs the parses and sums them:

```
many digit "42abc"                      -> 2   (counts digits 4,2)
firstVal digit "7"                      -> 7   (digit value, not code point)
firstVal (orElse (char 'z') digit) "9x" -> 9   ('z' fails, falls to digit)
firstVal (andThen digit digit) "34"     -> 7   (3 + 4)
pairP "5" (mapP at b := Int*Int)        -> 10  (5 + 5, the genericity witness)
                                     sum = 35
```

## How to run

```
nix develop            # dev shell (lake on PATH)
lake exe bang run examples/parser-combinators/main.bang    # -> 35
```

`bang run` is the TYPED pipeline (`checkAndLower`, ADR-0076) — the generic
combinators **type-check** before they run. Or via the gate: `just check-examples`
(diffs stdout against `expected.txt`).

## How #55 lifts the walls (the ADR-0079 follow-on)

The prior version was **monomorphic-at-Int** because a generic combinator could
not construct generic data without a placeable annotation. Three walls, now lifted:

1. **Generic-ctor construction in synth position** — a bare `Some(x)` / `Cons(1,
   Nil)` now types: the instantiation is inferred by unifying the *fields* against
   the ctor's template μ (params → fresh holes). A ctor is `∀a. …`, instantiated
   like any polymorphic function. So `Some((w, rest))` with `w : b` synthesizes
   `Option (b * Str)` — `b` a type variable, no annotation.
2. **Match through a higher-order parser** — matching `($p) s` (whose `Option`
   structure is behind the `p` hole) works: the `match` recovers the scrutinee's
   data type from its arm constructors (`None`/`Some` ⟹ `Option`) and unifies a
   template μ back onto the parser argument. So `mapP`/`orElse`/`andThen` inspect a
   generic parser result with no `: Option (Int * Str)`.
3. **Computation nested in a ctor arg** — `Some((($f) v, rest))` A-normalizes the
   computation and its (generic) product field is split into fresh holes, so no
   explicit `let w = (($f) v : Int)` is needed to place the type.

### Residual (still needs annotation)

`andThen`/`many`/`firstVal` stay Int-specialized here — not a generic-data wall but
because they *combine values with `+`* or return a numeric default (`0`), which
fixes the element to `Int`. A fully value-generic `andThen : Parser a -> Parser b
-> Parser (a * b)` is expressible (returns a pair instead of a sum); it is left
Int-shaped to keep the demo's numeric result. The one genuine frontier is **effect
row-polymorphism** (item 3) — orthogonal to #55.
