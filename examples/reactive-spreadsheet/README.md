# Reactive spreadsheet tracer

This is the smallest spreadsheet-shaped program that exercises BANG's existing pull-reactive
semantics end to end. It introduces no signal primitive, subscription runtime, cache, scheduler, or
kernel form.

Two named State capabilities are runtime input cells. Five stable declarations in `Formulas.bang`
describe the static formula graph:

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

`subtotal`, `tax`, and `total` are ordinary pure functions. The entry program wraps the selected
`total` formula in one unmemoized `liveTotal` thunk that reads both State inputs on every force. The
program observes total `22`, updates price to `12`, then observes the live total `26`.

It also demonstrates the important adverse route. `sampled = $liveTotal` forces the formula before the
update; `snapshot = {sampled}` therefore describes the fixed value `22`, not the live dependency. This
is intentional sampling/untracking under ADR-0005, but it is an easy spreadsheet-authoring mistake.
Keep the State reads and formula call inside the observation thunk when the relationship should remain
live.

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

## Observe dependencies

The compiler's existing versioned fact base exposes the formula DAG; each edge reads “`from` depends
on `to`”:

```sh
.lake/build/bin/bang query dump examples/reactive-spreadsheet/Formulas.bang \
  | jq -c '.refs'
```

The result is gated byte-for-byte in `expected-dependencies.json`:

```json
[{"from":"subtotal","to":"price"},{"from":"subtotal","to":"quantity"},{"from":"tax","to":"subtotal"},{"from":"total","to":"subtotal"},{"from":"total","to":"tax"}]
```

The reverse pre-edit question is already available through the same facts:

```sh
.lake/build/bin/bang impact examples/reactive-spreadsheet/Formulas.bang subtotal
```

It reports `tax` and `total` as transitive dependents. This representation matters: expression-local
`let` names are intentionally absent from the declaration-granular fact base because they have no
stable public identity. Put reusable/queryable formulas in a module rather than exposing traversal
ordinals that would change whenever a preceding expression is edited.

The example corpus gates the source/oracle, environment-machine, and calculated-machine routes. The
Wasm differential gate additionally emits the whole program and compares Wasmtime output with the same
`expected.txt`.

## Honest boundary

This tracer demonstrates a queryable static declaration graph and pull recomputation on observation.
The `refs` facts are source relationships, not runtime subscriptions or evidence about how often a
formula executed. It does **not** expose anonymous local subexpressions, maintain a runtime dependency
graph, cache formula values, invalidate only affected cells, schedule push propagation, diagnose
general formula cycles, or prove glitch freedom. Those features need an observable workload and a
subsequent PATH; calling this “incremental recomputation” would overstate the implementation.
