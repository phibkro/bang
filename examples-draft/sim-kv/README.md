# sim-kv (DRAFT + BLOCKED — the wall-straddling skeleton)

The replicated-KV **hello-world** skeleton: N replicas + simulated clients + a simulated message
bus, driven under a seeded `Choice` handler. `pick` chooses which pending message delivers next (the
interleaving) and deliver-vs-drop (fault injection). Convergence is **observed**
(`quiescentEqual` — are all replicas equal after the script drains?), NOT proved as a law — that is
rung 1 / rung 3 (post-v1, see the note §6).

This skeleton deliberately **straddles the v1 wall**: the scheduler clause
`pick(n) => ret ((lcg SEED) mod n)` is a *compute-then-return* body — arithmetic in the clause — which
hits ADR-0095 **D4** (the ret-shape restriction, gap **G1**). It is the concrete carrier of the ndet
note's headline ask: land binop typing (ADR-0065) + grade surfacing (Q27) so a clause can
compute-then-return, and this scheduler becomes runnable.

Design choices that keep it AS CLOSE to v1 as possible (note §5):
- **stateless seed-splitting** — the coin is `f(seed, step)`, NOT a mutable PRNG register, so the
  handler needs no carried-param UPDATE (retires gap G2) and no clause-head param binder (retires G3).
- **externalized world** — replicas + queue threaded as an immutable value through `let`, not carried
  in the handler param.

Net: the DST handler, designed honestly, needs *less* surface than it first appears — **only G1
(D4)** is on its critical path.

The complete `deliverStep`/`pendingCount`/`quiescentEqual`/`world0`/`SEED` definitions are elided;
this file shows the handler + stepping SHAPE, not a full program.

Design note: `docs/notes/ndet-dst-design.md` §4.4, §5, §7.
