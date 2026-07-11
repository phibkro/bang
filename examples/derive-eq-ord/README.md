# derive-eq-ord

The user-facing win for `deriving (Eq, Ord)` (issue #109, ADR-0097): a `data`
decl gets structural equality and ordering for free, instead of hand-writing a
`trait Eq`/`trait Ord` declaration plus a same-tag structural-fold `impl` for
each (roughly 15 lines — see `examples/trait-recursive-eq/main.bang` for the
hand-written shape the generated code matches).

```
data Point = Pt(Int, Int) deriving (Eq, Ord)
```

generates (equivalent to, not literally spliced as source):

```
trait Eq { fn eq(a, b) -> (Unit + Unit) law refl(a): a == a }
impl Eq for Point { fn eq(p, q) = match p { Pt(x0, x1) -> match q { Pt(y0, y1) -> ... } } }

trait Ord { fn lt(a, b) -> (Unit + Unit) law irrefl(a): 0 == 0 }
impl Ord for Point { fn lt(p, q) = match p { Pt(x0, x1) -> match q { Pt(y0, y1) -> ... } } }
```

`==`/`<` on `Point` values then dispatch through the generated `impl` exactly
like a hand-written one (operator binop-dispatch, no derive-aware syntax
needed at the use site) — usable directly inside an ordinary `match`.

`bang test` discovers and samples the generated trait's laws with zero extra
wiring (ADR-0097 §5) — try `bang test examples/derive-eq-ord/main.bang` on a
decls-only variant of this file to see `Eq.refl`/`Ord.irrefl` PASS.

```
lake exe bang run examples/derive-eq-ord/main.bang
# p1 == p2 (same payload, true), p1 == p3 (different payload, false),
# p1 < p3 (lexicographic, true), p1 == origin (false, so classified = 1) -> 1
```
