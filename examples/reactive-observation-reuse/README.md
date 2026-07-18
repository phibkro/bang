# Observation-scoped reactive reuse

This tracer continues the 401-call baseline in `../reactive-recomputation/`. The reuse path passes an
ordinary user-defined `Memo` capability through the same stable declarations and scopes its handler
inside one observation. It reports 203 invocations:
all 100 line formulas and 100 cache-checking `unitAmount` calls still run, but the shared multiplication
and its two input formula calls run only once.

`Memo` deliberately has one state-like `swap` operation. A lookup swaps in the miss sentinel; a hit is
immediately restored, while a miss is replaced with the computed value. This small destructive-read
protocol fits the currently shippable first-class custom-capability substrate and makes every state
transition explicit.

The program prints:

```text
(((7050, 203), (7450, 203)), ((7050, 203), (7050, 201)))
```

The first outer pair is the correct scoped route: before and after the price update, the handler starts
empty, the value changes, and the count resets to 203. The second outer pair deliberately retains one
handler across both forces: after the update it wrongly stays at 7050 and drops to 201 because the two
input formulas are skipped. That adverse result makes cache lifetime part of the executable contract.

This does not memoize BANG thunks. Global call-by-need would violate ADR-0005's load-bearing freshness
invariant. It also does not provide a general cache: v1 handler memory is `Int`, this positive-valued
fixture uses `0` as a miss sentinel, cache operations are not included in the formula-invocation count,
and there is only one cached declaration. General keys, value types, eviction, cross-observation
retention, invalidation, concurrency, and cost-based policy remain outside this tracer.

A natural two-operation `lookup`/`store` version passed the source, environment, and compiled evaluators
but trapped in concrete Wasm. The backend currently carries one runtime clause and one update flag for a
first-class custom capability; its deliberate multi-operation guard traps rather than guessing a clause.
Supporting multiple operations needs runtime operation identity plus per-clause update metadata, so that
backend representation change is recorded as a separate successor instead of being hidden in this
surface-semantics increment.
