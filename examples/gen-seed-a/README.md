# gen-seed-a

Half of the **Gen handler-swap pair** (with [`gen-seed-b`](../gen-seed-b/)) —
generation-as-effect (`docs/notes/ndet-dst-design.md`'s Deterministic Simulation Testing frame):
`Choice.pick(n)` means "choose a value bounded by `n`"; a *seeded* handler decides what every
`pick` returns. The program performs three picks and sums the results — a stand-in generator
run. This handler is SEED A: `pick(n) => 2` always returns `2`, so the run is `2+2+2 = 6`, and
because the handler is a pure function of nothing but its own clause, the run REPLAYS bit-for-
bit every time — the DST property (same "seed" ⇒ same sequence of choices ⇒ same output).

```
lake exe bang run examples/gen-seed-a/main.bang    # 2 + 2 + 2 -> 6
```
