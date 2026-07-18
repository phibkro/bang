# Reactive spreadsheet tracer

This is the smallest spreadsheet-shaped program that exercises BANG's existing pull-reactive
semantics end to end. It introduces no signal primitive, subscription runtime, cache, scheduler, or
kernel form.

Two named State capabilities are input cells:

```text
price = 10                 quantity = 2
       \                      /
        subtotal = price × quantity
             ├───────────────┐
             ▼               ▼
          tax = subtotal/10  │
             └──────┬────────┘
                    ▼
             total = subtotal + tax
```

The formulas are ordinary unmemoized thunks. Forcing `total` pulls through that dependency DAG and
re-samples `price` and `quantity`. The program observes total `22`, updates price to `12`, then observes
the live total `26`.

It also demonstrates the important adverse route. `sampled = $total` forces the formula before the
update; `snapshot = {sampled}` therefore describes the fixed value `22`, not the live dependency. This
is intentional sampling/untracking under ADR-0005, but it is an easy spreadsheet-authoring mistake.
Keep the force inside the formula thunk when the relationship should remain live.

Run the public journey after the normal bootstrap/build:

```sh
.lake/build/bin/bang check examples/reactive-spreadsheet/main.bang
.lake/build/bin/bang run examples/reactive-spreadsheet/main.bang
.lake/build/bin/bang run --compiled examples/reactive-spreadsheet/main.bang
```

Both run routes print:

```text
((22, 26), (22, 22))
```

- `(22, 26)` is `(live before, live after)`.
- `(22, 22)` is `(sampled before, snapshot after)`.

The example corpus gates the source/oracle, environment-machine, and calculated-machine routes. The
Wasm differential gate additionally emits the whole program and compares Wasmtime output with the same
`expected.txt`.

## Honest boundary

This tracer demonstrates a static formula dependency shape and pull recomputation on observation. It
does **not** yet maintain an explicit runtime dependency graph, cache formula values, invalidate only
affected cells, schedule push propagation, diagnose formula cycles, or prove glitch freedom. Those
features need an observable workload and a subsequent PATH; calling this “incremental recomputation”
would overstate the implementation.
