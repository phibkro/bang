# ndet-replicated-kv-b

Half of the **replicated-KV handler-swap pair** (with
[`ndet-replicated-kv-a`](../ndet-replicated-kv-a/)) — see that directory's
README for the full write-up (what the pair demonstrates, the LWW-merge
shape, the convergence-vs-divergence breakdown, the CALM reading).

This half is SEED B: the identical simulated system, `pick(n) => 2` instead of
`pick(n) => 0` (write3 — the highest-stamped write — arrives FIRST at every
replica instead of write1), producing a DIFFERENT schedule-dependent
intermediate (`afterFirstA = 300` vs seed A's `100`) while both replicas still
converge to the identical final merged value (`300` each) — see
`../ndet-replicated-kv-a/README.md`'s convergence/divergence table for the
exact numbers.

```
lake exe bang run examples/ndet-replicated-kv-b/main.bang
```
