# ndet-sim-kv-b

Half of the **sim-KV handler-swap pair** (with [`ndet-sim-kv-a`](../ndet-sim-kv-a/)) —
see that directory's README for the full write-up (what the pair demonstrates,
the replica/round/quiescence shape, and the relationship to
`docs/notes/ndet-dst-design.md`'s Draft C).

This half is SEED B: the identical simulated system, `pick(n) => 1` instead of
`pick(n) => 0`, converging on a different final cell value (`1100` vs seed A's
`1120`) while staying internally consistent (`allConverged = 1`).

```
lake exe bang run examples/ndet-sim-kv-b/main.bang    # -> 1100
```
