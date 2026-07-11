# list-basics

**The ADR-0103 payoff**: `take`/`drop` (`Prelude.bang`) are self-recursive
generics over the list element type (`Int -> List a -> List a`) with **no
trait bound** — the `monomorphizeLetRec` pre-pass discovers each call site's
concrete instantiation from its argument annotation and emits one
monomorphic `let rec` residue per element, exactly witness w3's by-hand
shape (`docs/decisions/witness-0103/`), auto-generated. No `∀`, tyvar, or
bound ever reaches the kernel.

This program also declares its own `data List a`/`length` (the List type
itself and a bound-free `length` are not yet in the always-on prelude — see
the ADR's own Implementation note for why). `take 3` of `[1,2,3,4,5]` is
`[1,2,3]` (length 3); `drop 3` is `[4,5]` (length 2); packed as `3*100+2`.

```
lake exe bang run examples/list-basics/main.bang    # -> 302
```
