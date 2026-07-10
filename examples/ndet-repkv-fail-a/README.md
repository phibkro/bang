# ndet-repkv-fail (seed A / seed B)

**Failure injection** — the R2 addendum's named next rung
(`docs/notes/distributed-story.md` §5): "failure injection (drop / delay /
partition) as another `Choice` dimension — a second `pick` the
message-delivery step consults ('does this write get delivered at all this
round?'), still a handler the kernel never learns about." Grows
[`ndet-replicated-kv-a`](../ndet-replicated-kv-a/)/[`-b`](../ndet-replicated-kv-b/)'s
delivery-**order** fold with a delivery-**outcome** consultation and an
explicit anti-entropy repair round. Half of a pair with
[`ndet-repkv-fail-b`](../ndet-repkv-fail-b/): the IDENTICAL simulated system,
run under two different `Choice` handlers ("seeds").

## What it demonstrates

```
Choice as an effect,   `effect Choice { pick : Int -> Int }` — the SAME
now doing double duty  mechanism as every ndet-* example, now consulted
                        TWICE per write per replica in spirit: once (in the
                        base demo) for delivery ORDER, and here for delivery
                        OUTCOME — "does this write arrive at all?" (0 =
                        delivered, nonzero = dropped). Both are ordinary
                        `pick` calls; the program performing them is agnostic
                        to which question the handler is really answering
                        (ADR-0016's paradigm-is-a-value thesis, still holding
                        on the failure axis).

per-call-site           v1's ret-shape restriction (ADR-0095 D4) means a
discrimination via      handler clause body can't carry a register, but IT
the bound argument      CAN branch on its own `n` argument (confirmed live:
                        `pick(n) => n` types and runs —
                        ../ndet-replicated-kv-a/README.md's Draft-C note).
                        This demo exploits exactly that: the six delivery
                        picks (3 writes × 2 replicas) use six DISTINCT bounds
                        (21..26), so ONE clause value per seed can answer
                        "delivered" for five of them and "dropped" for the
                        sixth by comparing `n` against a literal — the whole
                        failure-injection mechanism is one `if n == 26 then …`
                        in the handler, nothing new added to the kernel.

the possibly-partial    each replica folds its three writes in ORDER
per-replica fold        (write1, write2, write3 — a fixed order this time;
                        the base pair already covers order-independence,
                        this pair isolates the NEW axis), but a write only
                        folds in if its delivery pick says "delivered". A
                        dropped write leaves the register UNCHANGED — the
                        replica simply never learns that write happened this
                        round.

the anti-entropy        after both replicas' per-round folds, an
repair round             UNCONDITIONAL re-sync (no `pick` involved — this
                        round cannot itself drop) takes each replica to the
                        LWW-max of its own state and its peer's. This is the
                        piece that makes convergence EVENTUAL: a background
                        gossip round that repairs whatever a drop left
                        behind, rather than every write being immediately
                        and reliably visible everywhere.

the eventual-           PRE-anti-entropy, the two replicas' folded registers
consistency claim,      may genuinely DIFFER (a drop really happened and
made visible            really had a consequence). POST-anti-entropy, they
                        ALWAYS agree (the merge is still the same
                        commutative/associative/idempotent LWW-max join as
                        the base pair, so no coordination between replicas
                        was needed to reach agreement once the round runs).
                        That gap — differ-then-repair — IS "eventual
                        consistency", made visible as one more fold instead
                        of asserted in prose.
```

## The two seeds

Both directories run the exact same `<sim>` body; only the handler clause
differs:

```
lake exe bang run examples/ndet-repkv-fail-a/main.bang    # pick(n) => 0                    ->  113603
lake exe bang run examples/ndet-repkv-fail-b/main.bang    # pick(n) => if n==26 then 1 else 0 -> 103602
```

(Exact values recomputed against `lake exe bang run` on all three engines —
`env` (default), `oracle`, `compiled` — all three agree; see
`expected.txt` in each directory, the run oracle.)

## What converges vs. what differs (read this against the raw output)

Each run's output is one `Int` encoding five separate facts, each living in
its own non-overlapping decimal digit-slot:

```
output = (aFinal + bFinal) + postConverged*100000 + preConverged*10000 + a3*10 + b3/100
```

(`aFinal+bFinal` ∈ [0,600) never collides with the higher slots; `a3*10` ∈
{1000,2000,3000} and `b3/100` ∈ {1,2,3} are exact since 100/200/300 are
multiples of 100.)

```
                                seed A (drop-free)     seed B (write3@B dropped)
────────────────────────────────────────────────────────────────────────────
a3 (replica A, PRE-merge)             300                       300
b3 (replica B, PRE-merge)             300                       200
preConverged (a3 == b3?)                1                         0
aFinal (replica A, POST-merge)        300                       300
bFinal (replica B, POST-merge)        300                       300
postConverged (aFinal == bFinal?)       1                         1
output                              113603                    103602
```

**DIVERGES pre-merge** (seed B only): `b3` — under seed B, replica B's own
delivery pick for write3 (bound 26) answers "dropped", so replica B's
per-round fold only ever sees write1 (100) and write2 (200) and stops at
their max (200). Replica A, whose six delivery picks all answer "delivered",
folds all three and reaches 300. `preConverged` genuinely reads 0 — the two
replicas are NOT in agreement yet, a real (simulated) inconsistency, not a
cosmetic one.

**CONVERGES post-merge** (identical across both seeds): `aFinal`, `bFinal`,
`postConverged` — after the anti-entropy round, BOTH replicas land on 300
under BOTH seeds, and `postConverged` reads 1 in both. Under seed A there was
nothing to repair (`preConverged` was already 1); under seed B the repair
round is what does the work — replica B picks up write3's value from replica
A's state during the unconditional re-sync.

That is the whole point of this rung: the SAME merge algebra
(`../ndet-replicated-kv-a/`'s join-semilattice LWW-max) that made delivery
*order* irrelevant to the base pair's final value also makes delivery
*loss* recoverable here, given one more fold — "eventual" is not "immediate",
but it IS "eventually", and now that gap is a value you can read off stdout
instead of a claim in a README.

## Why a constant/arithmetic-on-`n` clause is enough (and its honest limit)

Per-seed, the scheduler clause is EITHER a true constant (seed A: `pick(n) =>
0`) OR a single `if n == <literal>` branch on the bound (seed B) — v1's
ret-shape restriction (ADR-0095 D4; no carried-register PRNG yet,
`docs/notes/ndet-dst-design.md` §2.2/§7 — the same honesty
`../ndet-replicated-kv-a/README.md` names). Because the six delivery-consult
call sites use six DISTINCT bounds, ONE handler value per seed can still
answer six DIFFERENT questions — that is what lets a stateless clause
simulate "drop exactly this one write at exactly this one replica" without
any PRNG or carried register. What it can NOT do: make the SAME bound answer
differently across two calls within one seed (there is only one call per
bound here, so that limit isn't exercised, but it is the same wall the base
pair's README names for delivery order). A real failure injector would want
a per-round-varying drop probability; this demo stays within the
literal-branch-on-bound shape instead, the same honest trade the base pair
makes for delivery order.

## Determinism (same seed ⇒ same output, every time)

Both directories are deterministic: re-running either `main.bang` three
times in a row produces byte-identical output every time (no real IO, no
clock, no threads — the entire "distributed" run, drops included, is one
seeded `bang eval`). Verified live for this pair:

```
$ for i in 1 2 3; do lake exe bang run examples/ndet-repkv-fail-a/main.bang; done
113603
113603
113603
$ for i in 1 2 3; do lake exe bang run examples/ndet-repkv-fail-b/main.bang; done
103602
103602
103602
```

Also verified as part of this lane's gate (`just check-examples` runs each
once per `just verify` pass), and cross-checked on all three engines
(`--engine=env` the default, `--engine=oracle` the kernel reference,
`--engine=compiled` the calculated-VM path) — all three agree on both seeds.

## What this demo deliberately does NOT build

- **No real network** — one process, one `bang eval`; "does this write get
  delivered" is a `pick` call, not a socket or a timeout.
- **No delay or partition modeling yet** — only binary drop/deliver per
  (replica, write). The R2 addendum's next-next rung is **partition**: drops
  CORRELATED by replica (a whole link down for a round, not one write lost)
  — see `docs/notes/distributed-story.md` §5 for exactly what's still faked
  and what's named next.
- **No CRDT law-checking** (rung 1) — the merge here is hand-written LWW, not
  a `merge` function checked against `lawInstancesOf`/`bang test`.
- **No proved convergence law** — both pre- and post-merge convergence are
  OBSERVED (equality checks baked into the output), not a Lean theorem.
- **No CALM typing** (rung 3) — nothing here flags an operation as needing
  coordination; there is no non-monotone op (no compare-and-swap) in this
  demo at all. That rung needs a non-monotone op to contrast against the
  monotone LWW merge this whole family of demos already has.
