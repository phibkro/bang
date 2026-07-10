# handle-custom-tracer

ADR-0095 D1's own worked example, verbatim (the operator-ruled surface for a **user-defined
effect handler**): declare `effect Net`, install a handler with `handle e with Net as net { … }`,
perform via `net.fetch(args)`. Each `fetch(n)` clause resumes tail-first with `n * 10`; the
handled body sums two performs. Demonstrates the FULL Stage-7 arc end to end — a user effect
declared, performed, and handled entirely through surface text, on both engines via `bang eval`.

```
lake exe bang run examples/handle-custom-tracer/main.bang    # (1*10) + (2*10) -> 30
```
