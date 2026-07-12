# ctor-nary

The user-facing win for issue #144: a `data` constructor's payload arity is
no longer capped at 2 (B011, ADR-0069's "a v1 bound, not a design position").
`data Quad = Q(Int, Int, Int, Int)` constructs, matches, and derives directly
— no manual tuple nesting needed at the surface.

```
data Triple = T(Int, Int, Int) deriving (Eq, Ord)
data Quad = Q(Int, Int, Int, Int) deriving (Eq, Ord)
```

Internally the elaborator still right-nests an N-ary payload into the
kernel's binary product (`Int * (Int * Int)` for `Triple`, matching
`prodOfTys`'s existing encoding) — the kernel is untouched; only the
surface's arity-2 THROW was ever the limit, not the encoding. `deriving (Eq,
Ord)` folds over every field (not just the first 1-2), so structural equality
and lexicographic ordering both work at any arity.

```
lake exe bang run examples/ctor-nary/main.bang
# T(1,2,3) sum + eq/neq/lt flags, then Q(1,2,3,4) sum + eq/neq/lt flags,
# packed into one Int -> 10201016
```

Cross-engine agreement: `bang run` (env), `bang run --engine=ck` (kernel),
and `bang run --compiled` (CalcVM) all produce the same `10201016`.
