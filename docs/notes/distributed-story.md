<!-- note-status: active -->
# The distributed-systems story — nondeterminism as an effect, the runtime as a handler

> Direction input (operator, 2026-07-09): "prove non-deterministic systems — distributed
> systems, consensus protocols, CRDTs, the CALM theorem. A KV store becomes the hello world
> of the distributed-systems story." This note pins the architecture mapping and the honest
> cost ladder BEFORE any of it is scoped. Post-v1 arc — nothing here is v1 work; the v1
> hooks it rides on are named in §3.

## 1 · Why bang is shaped for this (the thesis, one level up)

Every source of distributed pain is an **effect** (network send/recv, failure, timeout,
reordering, nondeterministic choice); every strategy for taming one is a **handler**
(scheduler, simulator, fault injector, adversary, model checker). In a language where
programs are descriptions until forced and ALL effects route through handlers:

- **Deterministic replay is a handler, not a runtime.** FoundationDB-style simulation
  testing — one handler owning every bit of nondeterminism (message order, drops,
  partitions, crash-restarts, clock) — is library code. Everyone else builds a bespoke
  simulator; bang installs one.
- **"The network is a runtime, and runtimes are values"** — the moat thesis (paradigm =
  row, runtime = handler) applied to distribution.
- **Nondeterminism is an effect too**: a `choice` effect whose handlers enumerate (DFS/BFS/
  random/weighted) turns "run the model checker" into "install the exploring handler."

## 2 · The cost ladder (cheapest rung first; the honest map)

| rung | ships | mechanism | cost / when |
|---|---|---|---|
| **1. Certified CRDTs** | user `merge` proved a join-semilattice (comm · assoc · idem) | `lawInstancesOf` discovers the laws, `bang test` shrinks counterexamples (#60, LANDED), Q43 proof-export lifts the surviving laws to Lean goals | **NEAR** — the law machinery exists; Q43 is the missing hop |
| **2. Simulation testing (DST)** | scheduler handler owning all nondeterminism; convergence checked AS A LAW ("all replicas equal after quiescence") | handlers + the `choice` effect; forking executions = **multi-shot ω-channel** | **MID** — needs Stage-7 surface (Q38), IO prong (ADR-0084), #61 env fix (speed), and the rq22 hybrid (closure rep for the statically-marked ω-channel) |
| **3. CALM as a grade** | monotone ops typed coordination-FREE; the row tells you which ops need consensus | monotonicity as a grade/coeffect; effect rows are already join-semilattices (invariant #2); Flix's lattice semantics = prior art (see q38 survey) | **RESEARCH** — genuinely novel; no graded-effect CALM exists. Publishable if it works |
| **4. Mechanized consensus** | Raft/Paxos refinement proofs | the Verdi/IronFleet territory | **FAR** — Verdi ≈ 50k lines of Coq, person-years. Named, not promised |

**The differentiated bet is rungs 1–3**: cheap for bang (the machinery is the language),
expensive for everyone else (bespoke simulators, bolt-on verifiers). Rung 4 is where every
verified-distributed project has bled out; it stays on the map as the horizon, not the plan.

## 3 · What the arc calls in from the current roadmap

- **STM's reserved privilege** (invariant #3, ADR-0030): the concurrent shared-heap form
  returns post-v1 — this arc is where that debt is called.
- **rq22 becomes load-bearing** (`multishot-survey.md`): the simulator's execution-forking
  is the ω-resumption channel; the survey's verdict (labelling for one-shot majority +
  closure rep ONLY for a statically-marked ω-channel — the operator's 0/1/ω grade idea)
  is the exact mechanism rung 2 needs.
- **Stage 7 handler surface (Q38)** + **IO prong (ADR-0084)**: the simulator and the real
  network are two handlers of the same effect — the surface must exist first.
- **#61 env semantics (ADR-0094)**: simulation runs millions of steps; the per-step
  constant must be lookup-shaped, not subst-shaped.

## 4 · The hello world: a replicated KV store

One artifact walks the whole ladder:

1. per-key CRDT registers (LWW / OR-set) with `merge` laws checked (rung 1);
2. replicas driven under a partition-injecting simulation handler, convergence checked as
   a law over the trace (rung 2);
3. add ONE compare-and-swap key: CALM names it non-monotone — the type system says *this
   op and only this op* needs coordination (rung 3), the rest stay coordination-free.

The `examples/ledger` handler-zoo showcase (same program, five runtimes) is the
single-node rehearsal of exactly this shape: the KV store is that zoo with the network as
the sixth handler.
