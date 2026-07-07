# parser-combinators

A **parser-combinator library written in bang** — the acceptance test for the
polymorphism milestone (ADR-0075 higher-order + ADR-0079 generic data). It
proves the two new capabilities *compose into a real reusable library*.

## What it is

A parser is a thunked function

```
Parser = Thunk (Str -> Option (Int * Str))
```

consume a prefix of the input, return `Some((value, rest))` on success or `None`
on failure. Result values are `Int` (this is a **monomorphic-at-Int** library —
see *What walled* for why the result type is not itself generic).

## What it demonstrates

| combinator | signature | capability exercised |
|---|---|---|
| `satisfy`  | `(Int -> Bool) -> Parser`            | higher-order (predicate → parser) |
| `char`     | `Int -> Parser`                      | specialization of `satisfy` |
| `mapP`     | `(Int -> Int) -> Parser -> Parser`   | higher-order (function → parser → parser) |
| `orElse`   | `Parser -> Parser -> Parser`         | ordered choice `<\|>` |
| `andThen`  | `Parser -> Parser -> Parser`         | sequencing (bind); value = sum |
| `many`     | `Parser -> Str -> Int`               | recursive fold (zero-or-more) |

- **Generic data** — `data Option a` used at `Option (Int * Str)` *and* `Option Int`;
  products `(Int * Str)`; `Str = List Char`.
- **Higher-order polymorphism** — every combinator takes thunked parsers/functions
  and applies them; `digit = mapP sub48 (satisfy isDigit)` composes two combinators.

The demo runs four parses and sums them:

```
many digit "42abc"                    -> 2   (counts digits 4,2)
firstVal digit "7"                    -> 7   (digit value, not code point)
firstVal (orElse (char 'z') digit) "9x" -> 9 ('z' fails, falls to digit)
firstVal (andThen digit digit) "34"   -> 7   (3 + 4)
                                     sum = 25
```

## How to run

```
nix develop            # dev shell (lake on PATH)
lake exe bang run examples/parser-combinators/main.bang    # -> 25
```

or via the gate: `just check-examples` (diffs stdout against `expected.txt`).

## What walled (the finding for the next #50)

The library is **monomorphic in the result type** (`Int`), not fully generic
(`Parser a`). Two limits of the current polymorphism, both from ADR-0079's
**annotation-driven generic-data introduction**:

1. **A generic combinator cannot construct generic data.** A truly generic
   `map : (a -> b) -> Parser a -> Parser b` must build `Some((f a, rest)) : Option (b * Str)`
   — but `b` is a *type variable*, and a bare generic constructor in synth
   position fails loud (`fold needs an expected μ type — annotate`). You cannot
   annotate with a type variable, and **annotation-free introduction is deferred**
   (ADR-0079 "Rejected/staged"). So combinators are pinned to a concrete result
   type where every construction site *can* carry a concrete annotation.

2. **Check-mode does not thread through `match`/`if` arms, nor into a
   constructor argument that is itself a computation.** Every construction site
   needs its *own* explicit `(… : Option (Int * Str))`, and a computation nested
   directly in a constructor arg (`Some((($f) v, rest))`, `Some((v1 + v2, …))`)
   must be **let-bound first** (`let w = (($f) v : Int) in Some((w, rest))`) — the
   binding is where the type lands. This is the ADR-0075 computation-hole boundary.

**The feature that unblocks a fully generic `Parser a`:** annotation-free generic
introduction (infer the element type from the constructor's field types at the
intro site), which would let generic combinators construct `Some`/pairs without a
placeable annotation. That is the next bite of PATH-polymorphism.
