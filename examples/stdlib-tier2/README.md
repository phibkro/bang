# stdlib-tier2

Issue #144's stdlib tier-2 additions: `zip`/`range`/`replicate` (the List-family
CONSTRUCTION members ADR-0103 explicitly left un-gated on landing) plus
`strLength` (the `Str`-specific counterpart of `length : List a -> Int` — a
distinct name avoids the bare-name collision the two differently-typed folds
would otherwise hit, since bang has no overload resolution).

```
range 0 5        -- [0, 1, 2, 3, 4]
replicate 3 7     -- [7, 7, 7]
zip xs ys         -- pairs elementwise, truncating to the shorter list
strLength "hello" -- 5
```

**The annotation-anchoring idiom** (ADR-0103, R6's finiteness discipline —
never a guess): a bound-free generic's instantiation is discovered from an
explicit annotation on the argument that DIRECTLY carries the free type
variable, not from the call's result type. `range`/`take`/`drop`/`append`
anchor on a `List a`-typed argument (`(xs : List Int)`); `replicate`'s free
variable sits in a BARE argument position (the element, not a `List`), so it
needs `(x : Int)` directly; `zip` has TWO free variables (one per side), so
BOTH arguments need their own annotation. An un-annotated call that leaves a
variable unresolved is a loud, self-teaching error naming the fix.

```
lake exe bang run examples/stdlib-tier2/main.bang
# range-sum=10, replicate-sum=21*100, zip-pair-sum=24*10000, strLength=5*1000000
# -> 5242110
```
