# state

The **State effect** as ordinary library code — a `with`-installed handler, not a
language feature. `state 0 in …` installs a state handler seeded at 0; `put 5`
updates it, `get` reads it back. Demonstrates that mutability is a handler over
the thunk+effect kernel (invariant #3).

```
lake exe bang run examples/state/main.bang    # get after (put 5) -> 5
```
