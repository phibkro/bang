# wildcard-match

The user-facing win for the `_` wildcard match arm (issue #101): `match c {
Red -> 1, _ -> 0 }` names ONE shared body for every constructor not spelled
out explicitly, instead of writing an arm per constructor even when most of
them agree.

```
data Color = Red | Green | Blue | Yellow | Purple
let rec isWarm : Color -> Int = fun c => match c { Red -> 1, _ -> 0 } in
```

`_` must be the LAST arm (arms after it could never fire — rejected as
unreachable), needs at least one explicit constructor arm before it so the
elaborator knows which `data` type it belongs to, and must cover at least
one constructor (a wildcard over an already-exhaustive match is dead code
and rejected too). All three are B014 diagnostics — `bang explain B014`.

The expansion is a pure PRE-elaboration rewrite (`expandWildcardArms`,
`Bang/Frontend/TypeCheck.lean`): `_ -> body` becomes one fresh arm per
missing constructor, each binding its own payload under fresh, unused
names, and reusing `body` verbatim. By the time the kernel-facing
elaborator runs, there is no wildcard left — the ADR-0069 named-match
elimination shape (a `matchS` chain over the unfolded scrutinee) is
completely unchanged, so this is sugar over the existing eliminator, not a
new kernel construct.

The wildcard also covers a constructor WITH payload (`Cons`, below) — the
expansion mints exactly as many fresh binders as that constructor's arity,
all ignored by the wildcard body:

```
data List a = Nil | Cons(a, List a)
let rec countWarm : List Color -> Int = fun cs =>
  match cs { Nil -> 0, Cons(c, rest) -> ($isWarm) c + ($countWarm) rest }
in
```

```
lake exe bang run examples/wildcard-match/main.bang
# palette = [Red, Blue, Red, Green] -> 2 warm colors (the two Reds)
```
