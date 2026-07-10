# ndet-sim-kv (seed A / seed B)

The **sim-KV hello-world** for the nondeterminism-as-effect story
(`docs/notes/ndet-dst-design.md` — rung 2's entry increment, the DST/FoundationDB
technique restated as "install a handler"). Half of a pair with
[`ndet-sim-kv-b`](../ndet-sim-kv-b/): the IDENTICAL simulated system, run under
two different `Choice` handlers ("seeds"), demonstrating that **nondeterminism
is an ordinary user effect** — the kernel never learns any of this exists.

## What it demonstrates

```
Choice as an effect     `effect Choice { pick : Int -> Int }` — pick n means
                        "choose a value bounded by n"; a HANDLER decides what
                        every pick returns. The program performing pick is
                        agnostic to the strategy (ADR-0016's paradigm-is-a-value
                        thesis, on the distributed axis).

the DST handler         a SEEDED, DETERMINISTIC `Choice` handler. Two properties
                        fall out for free: REPLAYABLE (same seed -> same picks ->
                        same output, every run — verified below by running each
                        seed three times) and SWAPPABLE (a different seed is a
                        different VALUE installed at `with Choice as sched { … }`
                        — nothing else about the program changes).

the sim-KV shape        two replicas (r1, r2) hold the SAME key, last-writer-wins.
                        Three write-rounds each race two writers against BOTH
                        replicas; `sched.pick(2)` resolves delivery order PER
                        REPLICA (the message bus can reorder each replica's link
                        independently) — 0 means the higher-value writer arrives
                        LAST (wins), 1 means the lower-value writer does.

quiescence, observed    after all three rounds, the program checks whether every
                        round's two replicas converged to the SAME winner and
                        folds that into the answer (+1000 per fully-converged
                        run). This is OBSERVED convergence (an equality check),
                        not a proved join-semilattice law — the certified-CRDT
                        version is a separate, later rung (see the design note
                        §6), deliberately not built here.
```

## The two seeds

Both directories run the exact same `<sim>` body; only the handler clause
differs:

```
lake exe bang run examples/ndet-sim-kv-a/main.bang    # pick(n) => 0  ->  1120
lake exe bang run examples/ndet-sim-kv-b/main.bang    # pick(n) => 1  ->  1100
```

Seed A always resolves each race in favour of the higher-value writer (`20`,
`40`, `60`); seed B always favours the lower-value writer (`10`, `30`, `50`).
Because each seed's clause is a CONSTANT (v1's ret-shape restriction, ADR-0095
D4 — a clause body must be a bare value, no carried-register PRNG yet, see the
design note §2.2/§7), both replicas under one seed always see the identical
delivery order and always converge — that is the same honesty the design note's
Draft B names ("a constant clause cannot make two picks differ from EACH
OTHER"). What DOES differ is seed A vs seed B: swapping the `with` clause is
the *entire* diff between the two programs, and it changes both replicas'
converged value (`60` vs `50` per replica) while both runs stay internally
consistent (`allConverged = 1` in both). That is the handler-swap demo in
miniature — "same program, different runtime" on the distributed axis.

## Relationship to the design note's Draft C

`docs/notes/ndet-dst-design.md` §4.4's Draft C sketches a scheduler clause
`pick(n) => ret ((lcg SEED) mod n)` — a stateless-PRNG coin computed from a
seed and the op argument. That EXACT shape still doesn't parse (bang's `BinOp`
has no `mod`/`%`, only `+ - * / < ==`), but the underlying gate the design note
worried about — G1, "compute-then-return clause bodies are D4-blocked" — has
in fact already lifted for pure arithmetic: `pick(n) => (n * 3 + 7)` types and
runs today (confirmed live against this lane's build). This example stays
within the CONSTANT-clause shape anyway (rather than reaching for arithmetic
coins) because a real per-step-varying PRNG still needs `mod`, which isn't in
`BinOp` — that gap is now the narrower, precise remaining ask, distinct from
D4 itself.
