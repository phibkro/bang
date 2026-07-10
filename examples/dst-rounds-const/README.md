# dst-rounds-const

The swap partner of [`../dst-rounds-lcg/`](../dst-rounds-lcg/): the SAME
recursive `Sched`-performing driver, with only the handler's policy clause
swapped — every delivery draw returns 0 (a fully synchronous network), so
both replicas always agree and **16**/16 rounds converge (vs 9/16 under the
LCG policy). The program's *runtime is the handler installed at the use
site*; swapping it changes the distributed behavior without touching one
character of the driver.

```
lake exe bang run examples/dst-rounds-const/main.bang    # -> 16
```
