# trait-recursive-ord

The `Ord` sibling of `trait-recursive-eq`: an `impl Ord for IntList` whose
`lt` op recursively compares list tails (`tx < ty`) via its own instance —
same #112 recursive-carrier shape, a different comparison op (lexicographic
`<` over the 3-way ladder, not `==`), confirming the knot-based dispatch fix
(ADR-0097 addendum) is not `Eq`-specific.

```
lake exe bang run examples/trait-recursive-ord/main.bang
# [1,2] < [1,3] (true), [1,3] < [1,2] (false) -> 1
```
