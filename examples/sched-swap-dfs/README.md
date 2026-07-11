# sched-swap-dfs

The handler-swap partner of [`../sched-roundrobin/`](../sched-roundrobin/): the exact
same driver body (same `Sched` effect, same 3-task/3-step-each task set, same
digit-trace accumulator), with only the handler's `next` clause changed from
`round mod 3` (round-robin) to the constant `0` (always the lowest-index runnable
task) — depth-first / run-to-completion. Task 1 runs all 3 of its steps before task 2
gets a turn, then task 2 runs to completion, then task 3: `111222333`.

```
lake exe bang run examples/sched-swap-dfs/main.bang    # -> 111222333
```

## Diff against the round-robin partner

The ENTIRE difference between this program and `../sched-roundrobin/main.bang` is one
line inside the `with Sched_Sched as sched { … }` block:

```
                     ../sched-roundrobin/           ../sched-swap-dfs/
next clause:         round - (round / 3) * 3        0
output:              123123123                      111222333
```

Same task set. Same driver. Same effect row. One clause in the installed handler
changed, and the entire concurrency behavior of the program changed with it — no
recompilation of the driver, no new language feature, just a different VALUE
installed at the `with` site. This is ADR-0101 §G1's headline claim
("scheduler-as-handler") shown as a runnable diff, not asserted in prose.
