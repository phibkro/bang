# ndet-replicated-kv (seed A / seed B)

The **R2 hello-world** — a replicated key-value store under DST — from
`docs/notes/distributed-story.md` §4 and `docs/notes/ndet-dst-design.md`.
Grows [`ndet-sim-kv-a`](../ndet-sim-kv-a/)/[`-b`](../ndet-sim-kv-b/)'s
single-race-per-round shape into a real per-replica **delivery-order fold**
plus an explicit **anti-entropy merge** step — the two pieces R2 adds over
R1's warm-up. Half of a pair with
[`ndet-replicated-kv-b`](../ndet-replicated-kv-b/): the IDENTICAL simulated
system, run under two different `Choice` handlers ("seeds").

## What it demonstrates

```
Choice as an effect     `effect Choice { pick : Int -> Int }` — same mechanism
                        as ndet-sim-kv: a handler decides every `pick`'s
                        result; the program performing `pick` is agnostic to
                        the strategy (ADR-0016's paradigm-is-a-value thesis).

the replicated KV       TWO replicas (ra, rb) hold the SAME key. THREE writes
                        carry a totally-ordered write-stamp (1 < 2 < 3, paired
                        with values 100/200/300 so "higher stamp" and "higher
                        value" coincide — the stamp scheme this demo picked,
                        expressible entirely with v1's `<`/`==`, no `mod`
                        needed). Each replica's delivery order is chosen
                        independently by `sched.pick(3)` (which write arrives
                        FIRST at that replica) — the message bus reordering
                        each replica's link differently, same idea as
                        ndet-sim-kv's per-replica-independent picks.

the LWW merge           merge(x, y) = keep whichever write has the higher
                        stamp. Commutative, associative, idempotent — an
                        LWW-register JOIN (a join-semilattice merge, the CALM
                        precondition — docs/notes/calm-as-grade-survey.md).
                        Because it's a join, folding the three writes in ANY
                        order lands on the SAME final value: write3 (value
                        300) always wins, independent of delivery order.

the CALM claim,         the payoff (below): both replicas, under BOTH seeds,
in miniature            converge to the identical final value (300 each,
                        600 merged) — because the merge is order-free, no
                        coordination between replicas was needed to reach
                        agreement. Meanwhile the SCHEDULE-DEPENDENT
                        intermediate (which write arrived first) genuinely
                        differs between seed A and seed B, proving the two
                        schedules really did interleave differently — the
                        convergence isn't a coincidence of the picks being
                        inert, it's the merge's algebra doing the work. This
                        is "order-free merge ⇒ coordination-free convergence"
                        — CALM's headline, in eight lines of bang. Where this
                        goes next (typing monotonicity as a grade so the type
                        system flags which ops need coordination): rung 3,
                        docs/notes/calm-as-grade-survey.md.
```

## The two seeds

Both directories run the exact same `<sim>` body; only the handler clause
differs:

```
lake exe bang run examples/ndet-replicated-kv-a/main.bang    # pick(n) => 0  ->  1700
lake exe bang run examples/ndet-replicated-kv-b/main.bang    # pick(n) => 2  ->  1900
```

(Exact values recomputed against `lake exe bang run`, not hand-derived — see
`expected.txt` in each directory, the run oracle.)

## What converges vs. what differs (read this against the raw output)

Each run's output is one `Int` encoding two separate facts:

```
output = (raFinal + rbFinal) + allConverged * 1000 + afterFirstA
```

```
                              seed A (pick(n) => 0)   seed B (pick(n) => 2)
──────────────────────────────────────────────────────────────────────────
raFinal (replica A, final)          300                     300
rbFinal (replica B, final)          300                     300
allConverged (ra == rb?)              1                       1
afterFirstA (intermediate)          100                     300
```

**CONVERGES** (identical across both seeds): `raFinal`, `rbFinal`,
`allConverged` — every replica, under every schedule, lands on the same
merged value (`300`) and every round is internally consistent
(`allConverged = 1`). This is the state the anti-entropy merge produces —
the thing a real replicated store promises its clients.

**DIVERGES** (legitimately different across seeds, proving the schedules
really interleaved differently): `afterFirstA` — under seed A, write1
(value 100, the LOWEST stamp) is what replica A observes first; under seed B,
write3 (value 300, the HIGHEST stamp) arrives first instead. Two genuinely
different message orders, visible in the trace — yet both eventually fold to
the identical final state. That's the whole point: the intermediate is
schedule-dependent, the converged value is not.

## Why a constant clause is enough (and its honest limit)

Per-seed, the scheduler clause is a CONSTANT (`pick(n) => 0` or
`pick(n) => 2`) — v1's ret-shape restriction (ADR-0095 D4; no carried-register
PRNG yet, `docs/notes/ndet-dst-design.md` §2.2/§7). A constant clause can't
make replica A's pick differ from replica B's pick WITHIN one seed (both
replicas see the same "which write arrives first" answer, `firstA == firstB`
here) — the same honesty `../ndet-sim-kv-a/README.md` names. What a constant
clause DOES do is make seed A differ from seed B: swapping the `with` clause
is the *entire* diff between the two programs, and it changes the observed
delivery order everywhere — the handler-swap demo, now over a real
order-dependent fold instead of a single two-way race.

## Determinism (same seed ⇒ same output, every time)

Both directories are deterministic: re-running either `main.bang` three times
in a row produces byte-identical output every time (no real IO, no clock, no
threads — the entire "distributed" run is one seeded `bang eval`). Verified
as part of this lane's gate (`just check-examples` runs each once per
`just verify` pass; the report accompanying this pair additionally shows
three repeated manual runs per seed).

## What this demo deliberately does NOT build

- **No CRDT law-checking** (rung 1) — the merge here is hand-written LWW, not
  a `merge` function checked against `lawInstancesOf`/`bang test`.
- **No proved convergence law** — convergence is OBSERVED (an equality
  assertion baked into the output), not a Lean theorem.
- **No CALM typing** (rung 3) — nothing here flags an operation as needing
  coordination; there is no non-monotone op (no compare-and-swap) in this
  demo at all. That's next.
- **No real network, no failure model** — see the R2 addendum in
  `docs/notes/distributed-story.md` for exactly what's faked and the named
  next rung (failure injection as another `Choice` dimension).
