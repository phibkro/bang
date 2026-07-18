# sched-seeded-lcg

The **DST bridge**: a THIRD `Sched` handler over the identical driver from
[`../sched-roundrobin/`](../sched-roundrobin/)/[`../sched-swap-dfs/`](../sched-swap-dfs/),
whose `next` policy is a seeded LCG (the same `s*25+17 mod 65536` step
`examples/dst-rounds-lcg` uses) instead of a hand-picked round-robin/DFS rule:
`221131233` — a pseudo-random-looking interleaving that is nonetheless
**deterministic and replayable**: re-running this exact program produces the exact
same trace every time, because the seed is a plain constant closed over by the
handler clause, and bang's evaluation has no other source of nondeterminism.

```
lake exe bang run examples/sched-seeded-lcg/main.bang    # -> 221131233
```

## Why this is the DST story, not just a third policy

`docs/notes/ndet-dst-design.md`'s thesis: *"deterministic replay is a HANDLER, not a
runtime mode."* A FoundationDB-style simulator owns every source of nondeterminism in
ONE seeded component so a failing run reproduces exactly by re-running its seed. Here
that component is the `Sched` handler: the driver never calls anything nondeterministic
directly, it only ever asks `sched.next(round)`, and the handler resolves every one of
those asks from a seed. Swap the seed (or the handler entirely) and you get a
DIFFERENT-but-still-fully-deterministic interleaving — the same handler-swap property
`../sched-roundrobin/` vs `../sched-swap-dfs/` demonstrates, now with "seeded PRNG" as
the third point in the design space alongside "hand-designed policy."

## The v1 wall this demo works around (named honestly)

A textbook seeded scheduler carries a MUTABLE PRNG register the handler updates on
every pick. ADR-0114 now provides a ret-shaped value update envelope, but this historical
demo deliberately keeps its original plain/read-only clause and threads the seed externally.
It also can't CALL a
recursive `Div`-performing function (like the LCG step) inline and then do arithmetic
on the result — that is a compute-then-return body, and even though it types today for
SIMPLE arithmetic (`examples/dst-rounds-lcg`'s `(s/64) - ((s/64)/2)*2` on an
already-computed `s`), a clause that calls `$lcgStep` itself still hits the ret-shape
wall (the call is itself a `Div`-effect the clause would have to perform before
resuming).

The honest v1 workaround (`main.bang`'s comment, `ndet-dst-design.md` §5.1's stateless
seed-splitting idiom): precompute the LCG's pick sequence ONCE outside the handler (up
to 9 rounds — the most this 3-task/3-step driver ever needs), close over the whole
table, and have the clause do plain `if round == k then …` dispatch plus arithmetic on
an already-bound value. This is MORE work than a real mutable-PRNG handler would need,
and it is exactly the shape `docs/notes/sched-library-demo.md`'s
§"what waits for the CTR gate" names as the concrete ergonomics benchmark for when
compute-then-return clause bodies fully land.
