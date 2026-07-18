# sched-roundrobin

**The concurrency-axis handler-swap demo** (ADR-0101 §G1: "concurrency is an ordinary
effect; a scheduler is a handler installed at the use site"). Three cooperative tasks,
each yielding 3 times, interleaved by a round-robin `Sched` handler. The output IS the
interleaving trace — each running task appends its own id (a single digit) to an
accumulator every step it takes, base-10 — so round-robin's strict alternation reads
directly off the number: `123123123`.

```
lake exe bang run examples/sched-roundrobin/main.bang    # -> 123123123
```

## The shape

`Sched.bang` declares one effect, two ops:

```bang
pub effect Sched { spawn : Int -> Int, next : Int -> Int }
```

`spawn` registers a task (echoes back the caller-chosen id — see `Sched.bang`'s doc
comment for why v1 can't allocate ids inside the handler itself). `next` is the
scheduling DECISION: the driver calls `sched.next(round)` once per round (passing a
plain round counter, not a mutable "whose turn" register — these clauses are deliberately
plain/read-only; ADR-0114's `update` form is not used), and the handler returns which runnable task index
goes next. Everything about HOW tasks interleave lives in that one clause:

```bang
with Sched_Sched as sched {
  spawn(n) => n,
  next(round) => round - (round / 3) * 3     -- round-robin: round mod 3
}
```

`Task.bang` encodes a "task" as a `Step` coroutine (`Fin` = done, `More(k)` = "not
done, here is the thunk for my next step") — the honest v1 substitute for a captured
continuation, which the surface doesn't have (ADR-0025 D1). See `Task.bang`'s doc
comment and `../../docs/notes/sched-library-demo.md` §"why Step, not a continuation"
for the full argument.

## The payoff: same driver, different runtime

[`../sched-swap-dfs/`](../sched-swap-dfs/) is the SAME driver body — not just the
same shape, the same file up to one clause — under a depth-first/run-to-completion
`Sched` handler instead: `111222333`. Nothing about the task set or the driver's
control flow changes; only the installed handler's `next` policy does. That is the
moat thesis ("paradigm is a value; runtime is the handler installed at the use site")
made concrete on the concurrency axis, exactly as `examples/dst-rounds-const`/
`dst-rounds-lcg` demonstrate it on the distributed-delivery axis. [`../sched-seeded-lcg/`](../sched-seeded-lcg/)
is a third handler (seeded pseudo-random) over the same driver, for the deterministic-
replay half of the story.
