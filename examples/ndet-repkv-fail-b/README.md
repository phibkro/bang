# ndet-repkv-fail-b

Half of the **replicated-KV failure-injection pair** (with
[`ndet-repkv-fail-a`](../ndet-repkv-fail-a/)) — see that directory's README
for the full write-up (what the pair demonstrates, the delivery-outcome
mechanism, the pre-/post-merge convergence table, the eventual-consistency
reading).

This half is SEED B: the identical simulated system, `pick(n) => if n == 26
then 1 else 0` instead of seed A's constant `pick(n) => 0`. Bound 26 is
replica B's delivery-consult for write3 (the highest-stamped, highest-value
write) — under this seed it comes back "dropped", so replica B's pre-merge
fold only reaches write2's value (200) while replica A (every one of whose
six delivery picks still answers "delivered") reaches write3's value (300).
The two replicas' PRE-anti-entropy states genuinely DIFFER
(`preConverged = 0`) — real, observable divergence, not a faked one. The
UNCONDITIONAL anti-entropy round that follows (no `pick` involved — it cannot
itself drop) then re-syncs replica B to the LWW-max of both replicas' states,
so both land on 300 and `postConverged = 1` — see
`../ndet-repkv-fail-a/README.md`'s worked table for the exact digit-by-digit
arithmetic (`103602`).

```
lake exe bang run examples/ndet-repkv-fail-b/main.bang
```
