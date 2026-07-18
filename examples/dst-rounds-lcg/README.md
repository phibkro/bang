# dst-rounds-lcg

**Handler-swap pair 4 (the DST-rounds pair)** — a replicated-KV
delivery-order census under a swappable `Sched` effect, with the LCG seed
threaded through the **driver's own recursion**. The novel demonstration
over the earlier `ndet-*` examples: the performer is a *recursive* function
carrying a declared user-effect row (`! {Div, Sched}`) and performing
through a lexically captured capability — recursion × user effects ×
capabilities composing in one program.

Each of 16 rounds, two replicas each draw a delivery order for the same
racing write pair; a round converges iff the draws agree. The handler owns
only the **policy** (seed → bit). This predates ADR-0114 and deliberately retains plain,
read-only clauses, so the driver threads evolving scheduler state itself. Compare
`../stateful-quota/` for the later explicit update envelope; this program remains the
before/after ergonomics baseline for moving a richer recursive scheduler into that form.

LCG policy (bit 6 of the seed): **9**/16 rounds converge. Swap partner:
[`../dst-rounds-const/`](../dst-rounds-const/) — same driver byte-for-byte,
constant policy, **16**/16.

```
lake exe bang run examples/dst-rounds-lcg/main.bang    # -> 9
```
