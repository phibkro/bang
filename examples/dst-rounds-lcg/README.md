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
only the **policy** (seed → bit): clause bodies are ret-shape and `param`
is read-only in v1 (ADR-0095 D4 / ADR-0092 D5), so evolving scheduler state
*cannot* live in the handler — the seed-threading in the driver is the
honest workaround, and the day the CTR gate lands this program is the
before/after ergonomics benchmark.

LCG policy (bit 6 of the seed): **9**/16 rounds converge. Swap partner:
[`../dst-rounds-const/`](../dst-rounds-const/) — same driver byte-for-byte,
constant policy, **16**/16.

```
lake exe bang run examples/dst-rounds-lcg/main.bang    # -> 9
```
