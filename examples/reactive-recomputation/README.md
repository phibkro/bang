# Reactive recomputation measurement

This example measures BANG's current uncached pull behavior before any cache is designed.
`Workload.bang` is an invoice-shaped DAG with two shared inputs, one shared `unitAmount` formula,
100 line-item formulas, and one aggregate total. Every formula returns its ordinary value together
with an in-band invocation count;
the count is terminal output, so source, machine, compiled, and Wasm routes must preserve it.

The first observation uses price 10 and quantity 2. The program then changes price to 12 and forces
the same live thunk again. It prints:

```text
((7050, 401), (7450, 401))
```

Both observations execute 401 formula calls: 100 price calls, 100 quantity calls, 100 calls to the
shared derived formula, 100 line-item calls, and one total call. The static compiler facts
independently report 104 declarations and 202 edges.
That distinction is intentional: a dependency edge is not an execution event.

This is evidence of repeated full-DAG evaluation for this workload, not a benchmark and not proof that
caching is always beneficial. It excludes allocation cost, wall-clock latency, dynamic dependencies,
and invalidation semantics. The next decision must compare the measured redundancy (401 calls for 104
stable formulas) with the semantic and implementation cost of caching. The first discarded prototype
reported 301 calls but repeated only trivial input-identity declarations; adding the shared derived
node prevents representational overhead from masquerading as the optimization signal.
