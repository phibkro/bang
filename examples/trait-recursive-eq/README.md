# trait-recursive-eq

A trait `impl` whose op body **calls its own instance recursively** — `Eq.eq`
for `IntList` compares list tails with `tx == ty`, where `tx`/`ty : IntList`,
the SAME type the `impl` is defined for.

Regresses issue #112: `buildEnv`'s `.implD` arm used to elaborate a 2-param
op's body by TEXTUALLY SPLICING it into every `.binopS` call site, so a
self-referential call needed the impl's own instance to be complete before it
existed — `no impl provides 'eq' for (mu. …)`. The fix knot-binds every
2-param impl op via the SAME `let rec` fixpoint machinery ordinary recursive
functions use (`letRecS`/Landin's knot, ADR-0073), so `tx == ty` resolves
through real recursion, not substitution. See ADR-0097 §3 ("the
recursive-carrier wall") and its addendum for the full diagnosis.

```
lake exe bang run examples/trait-recursive-eq/main.bang
# l1 == l2 (same, true), l1 == l3 (diff, false) -> 1
```
