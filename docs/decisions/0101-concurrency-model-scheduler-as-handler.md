# ADR-0101 · Concurrency model: scheduler-as-handler; components/threads are backends, not the model

<!-- adr-frontmatter -->

- **Status**: Accepted (direction ratified 2026-07-11; implementation is post-v1, spike-gated)
- **Summary**: Concurrency is an ORDINARY effect (a `conc`/`Sched` row label) and a scheduler is a
  HANDLER installed at the use site — the moat thesis ("runtimes are values") on the concurrency axis.
  Components-as-actors and shared-heap threads are two future BACKENDS of that real-scheduler handler,
  NOT competing language models. Adds NO kernel primitive and NO grade axis (invariants #2/#3/#5
  intact): concurrency enters the ROW, the only load-bearing grade stays the resumption grade 0/1/ω
  on the continuation. STM's concurrency privilege stays RESERVED and backend-blocked (ADR-0030).
  One-shot resumption SUFFICES for spawn/await (the wasm substrate is one-shot by construction).
  DETERMINISTIC REPLAY is the default runtime (the seeded sim-scheduler); production nondeterminism is
  the explicit opt-in (handler swap). `!` (actor-send) payloads are restricted to the Sendable fragment
  so one surface covers both backends at identical semantics. WASI-0.3 async is the first production
  backend target, gated on one lowering spike. This ADR records DIRECTION only — nothing in v1 scope
  changes; the Non-Features/PRD boundary stays intact.
- **Depends-on**: 0007 (`!` = actor-send, force explicit), 0016 (two-hop architecture), 0059 (Wasm 3.0
  backend, grade-directed lowering), 0030 (STM = transactional handler; privilege = concurrency-only),
  0001 (effect rows are sets), 0018 (rows carry a lattice/OrderBot)
- **Relates-to**: `docs/notes/wasm-concurrency-survey.md` (the survey + grill sheet this ADR rules on),
  `docs/notes/actor-sendable-design.md` (§7 = the G7 Sendable input, verbatim below),
  `docs/notes/ndet-dst-design.md` + `docs/notes/distributed-story.md` (the demonstrated seeded-sim
  precedent), `docs/notes/calm-as-grade-survey.md` (`coord` label; grading-the-row rejected),
  `docs/notes/multishot-survey.md` (one-shot sufficiency; Q22/Q27 stays parked),
  `Bang/Witness/SendableFragment.lean` (the copy≡share syntactic core, axiom-clean, in the gate),
  issues #115 (concurrency-model direction) / #116 (components-as-actors measurement, deferred)

- **Layer**: K (kernel semantics — where concurrency enters the model: the row, not a new primitive)
- **Date**: 2026-07-11

## Status

Accepted (operator ratification, 2026-07-11). The operator ratified the *direction*; the
*implementation* is post-v1 and spike-gated. This mirrors ADR-0030's shape: a decision made and
evidenced now, whose realization waits on a substrate/spike — recorded here so a future session does
not relitigate it. Nothing in v1 scope changes as a result of this ADR (§Consequences).

## Context

`wasm-concurrency-survey.md` mapped how bang should model concurrent execution against the 2026 wasm
platform, and posed eight grill questions (G1–G8) with evidence-backed default answers. The
single load-bearing 2026 fact: **WASI 0.3 shipped native async (2026-06-11) built on the Component
Model's own async ABI + a host-managed cooperative event loop — NOT on stack-switching** — i.e. the
production platform independently arrived at *scheduler-as-handler* at the platform level (survey §1.2).
Combined with the already-demonstrated seeded `Choice`/`Sched` sim-scheduler (`ndet-dst-design.md`,
passing today), the survey's default answers held up under grilling. This ADR rules on the package,
naming the one genuinely open contract-edge (G6 replay) rather than over-promising it.

## Decision (the ratified package — G1–G8)

### G1 — THE MODEL: scheduler-as-handler

Concurrency surface ops (`spawn`/`yield`/`await`/`send`; `!` = actor-send per ADR-0007) are an
**ordinary effect** carried in the row, and a **scheduler is a handler** installed at the use site.
This is the moat thesis on the concurrency axis: a program's concurrency *runtime* is a handler, not a
language feature. Components-as-actors and shared-heap threads (below) are **two backends of the
real-scheduler handler**, not competing models.

*Evidence:* the seeded sim-scheduler (`Choice`/`Sched`) is demonstrated and passing today
(`examples/ndet-*`), and WASI-0.3's host-driven cooperative event loop is the same shape at the
platform level (survey §1.2, §2c).

### G3 — STM's concurrency privilege stays RESERVED

The shared-heap STM privilege (invariant #3 / ADR-0030) **stays reserved and backend-blocked**: its
wasm substrate (shared-everything-threads + shared GC structs) is CG Phase 1, years out (survey §1.4).
The transactional *handler* (ADR-0030, already v1) covers single-threaded transactional semantics in
the interim. The privileged parallel form returns when its substrate ships.

### G4 — concurrency enters the ROW, not a grade axis

Concurrency is a `conc`/`Sched` **row label**, exactly like `Choice` today (invariant #2: rows are
sets, union = join — ADR-0001/0018). Coordination is the CALM `coord` **row label**
(`calm-as-grade-survey.md`). **Grading-the-row is REJECTED** (a per-label multiplicity breaks
rows-are-sets). The **only** load-bearing grade is the resumption grade 0/1/ω — and that lives on the
*continuation*, not the row.

### G5 — one-shot resumption SUFFICES

Spawn/await/yield need only **one-shot** continuations: wasm stack-switching is one-shot by
construction (`resume`/`switch` destructively consume; second use traps — survey §1.3), OCaml 5
demonstrates one-shot suffices for concurrency, and bang's v1 backend covers green-threading on stock
Wasm 3.0 via the WasmGC frame-chain (survey §5). Multi-shot is needed **only** for DST
*execution-forking*, which is copy-able and stays parked behind Q22/Q27 (`multishot-survey.md`).
Concurrency does not force multi-shot.

### G6 — DETERMINISTIC REPLAY IS THE DEFAULT

The seeded, stateless-seed-splitting sim-scheduler is the **v1 concurrency runtime**: every concurrent
bang program is replayable by construction (same seed ⇒ same interleaving ⇒ byte-identical output).
Production nondeterminism is the **explicit opt-in** — swap to the wasm-backed scheduler handler. DST
(FoundationDB-style simulation) is therefore not a bolt-on but the default (survey §4).

**Open contract-edge (named, not silently promised):** *what replay covers once real IO handlers
exist.* Today the only nondeterminism seam is the scheduler's `pick`, so **schedule-only replay** is
exact. When production handlers perform real IO (network, clock, filesystem), a recorded pick-sequence
replays the *scheduling* faithfully but does **not** by itself reproduce external effect *results* —
that needs a **recorded-effects** discipline (log-and-replay the IO responses too, the DST record/replay
distinction). Which of the two — *schedule-only* vs *recorded-effects* — bang's replay guarantee spans
is a **named open question** (Q(conc-6), below), not a promise this ADR makes. The v1 sim runtime is
schedule-only because it has no real IO; the guarantee's shape past that boundary is deferred to when
real IO handlers land.

### G7 — `!` payloads are the Sendable fragment

*(Adopted verbatim from `actor-sendable-design.md` §7, the operator-ready input.)*

Adopt survey §G7 **resolution (i)**: `!` payloads are restricted to the **Sendable** fragment
(`Sendable : Val → Prop` / its `Ty` mirror — closed first-order data: `unit`/`int` + `sum`/`prod`/`mu`,
excluding `U`/`arr`/`cap`). This is *not* a new primitive, row, or grade — a **structural type
predicate** at the `!` site (invariant #2/#5 intact). It licenses **one surface `!` with two backends**
(in-process SHARE, component COPY) at *identical* semantics, justified by the kernel theorem
`copy ≡ share` (syntactic core proven axiom-clean in `Bang/Witness/SendableFragment.lean`; contextual
closure rides the parked binary LR). Reject Pony-style reference capabilities (disproportionate given
global immutability) and always-copy (iii) (discards free in-process sharing). Static refusal at the
`!` site for non-Sendable payloads (`error(bang.nonSendablePayload)`). Out-of-scope doors:
in-process thunk-send (a distinct marked op) and replicated-mutable-data (the CRDT/`coord` arc).

### G8 — WASI-0.3 async is the FIRST production backend target

The first production scheduler backend is the **WASI-0.3 cooperative async** runtime (shipped
2026-06-11, no stack-switching needed, the handler shape bang already has — survey §1.2). Gated on
**one spike**: the WASI-0.3 async ABI (`async func`/`stream<T>`/`future<T>`) ↔ graded-CBPV
grade-directed lowering (ADR-0059) fit is unverified (Q(conc-3), below).

### G2 — components-as-actors DEFERRED pending measurement

Components-as-actors is a **deployment/isolation/distribution** backend, not the intra-program spawn
primitive, and is **deferred pending measurement** (issue #116): whether component *instantiation* is
cheap enough (µs-scale) to back fine-grained actors, and whether the copy-crossing tax on GC-heap
values is tolerable, are both unquantified in 2026 sources (survey §2a, §6-G2). It stays a named
backend, not the model.

## Why this model (grounded, not instinct)

1. **The platform converged onto it.** WASI-0.3's host-driven cooperative event loop *is*
   scheduler-as-handler at the platform level (survey §1.2). This is the strongest evidence: the
   language model bang already has is the shape the production platform independently arrived at.
2. **It's demonstrated, not speculative.** The seeded `Choice`/`Sched` sim-scheduler passes today
   (`ndet-dst-design.md`); G1's headline is a running artifact, not a plan.
3. **One construct per problem (invariant #1).** Making concurrency an ordinary effect unifies
   components (a) and threads (b) as *backends* of one handler, instead of three competing models. The
   kernel stays at five primitives; no sixth is added.
4. **Immutability already solves the send problem** (G7). bang's kernel values are deep-immutable, so
   `copy ≡ share` holds for the Sendable fragment — a cheap structural predicate dominates Pony-style
   per-reference capabilities (Erlang's 30-year precedent).
5. **The substrate is one-shot, and that suffices** (G5). Concurrency needs no multi-shot machinery;
   the one place multi-shot bites (DST forking) is copy-able and stays parked.

## Rejected alternatives

1. **Components-as-THE-concurrency-model** (a as the language model). *Why not:* component
   instantiation is a coarse deployment/packaging unit (its own memory, heavyweight instantiate cost),
   not a green-thread; and shared-nothing linking copies GC-heap values across boundaries — a real
   semantic tax for a GC-heap-thunk language. Correct as an isolation/distribution **backend** (G2),
   wrong as the intra-program model. Deferred pending the #116 measurement, not adopted-as-model.
2. **Threads-as-THE-model** (shared-memory concurrency with privileged STM as the v1.x plan).
   *Why not:* its wasm substrate (shared-everything-threads + shared GC structs) is CG Phase 1, years
   out (survey §1.4) — the one place bang **cannot** polyfill. Keep the STM privilege reserved (G3);
   do not plan the near-term story around an absent substrate.
3. **Pony-style reference capabilities for `!` payloads** (`iso`/`val`/`ref`/`box`/`tag`). *Why not:*
   ref-caps exist to send *mutable* state safely; bang's values are already deep-immutable, so the
   entire lattice buys nothing the `Sendable` predicate doesn't — a heavyweight per-reference type
   system solving a problem immutability already solved (rejected in `actor-sendable-design.md` §6).
4. **Grading-the-row for concurrency** (a per-label multiplicity/weight/coeffect). *Why not:* breaks
   invariant #2 (rows are *sets*, union = join — ADR-0001/0018). No quantitative-per-label concurrency
   property surfaced (`calm-as-grade-survey.md`). Concurrency is set-membership in the row (G4); the
   only load-bearing grade (resumption 0/1/ω) is on the continuation, not the row.
5. **Always-copy `!` (resolution iii).** *Why not:* discards free in-process sharing to buy a
   uniformity the `copy ≡ share` theorem already gives for free (G7 / `actor-sendable-design.md` §5).

## Consequences

- **NO code change, NO kernel primitive, NO grade axis.** This ADR records direction. Invariants #2
  (rows are sets), #3 (STM privilege — reframed as reserved-and-backend-blocked, not dropped), and #5
  (five primitives) are intact. **Nothing in v1 scope changes**; the Non-Features/PRD boundary stays
  as-is. Implementation is post-v1 and spike-gated.
- The survey's proposed OQ entries become the tracked follow-ons: the `conc`/`Sched` row-label +
  scheduler-handler surface (depends on Stage-7 handler surface, Q38); the WASI-0.3 async ↔ CBPV
  lowering spike (G8); the component-instantiation-cost measurement (G2, issue #116); the shared-heap
  STM substrate watch (G3, ADR-0030 §Revisit-if); and the **new** G6 replay-contract edge below.
- The `!` (actor-send) elaboration gains a static Sendable check at the `!` site when it lands
  (G7) — a `Ty`-level structural predicate, not a runtime gate.

## Open question (filed by this ADR)

- **Q(conc-6) — Replay contract past real IO.** Once production handlers perform real IO, does bang's
  replay guarantee span *schedule-only* (reproduce the scheduling `pick`-sequence) or *recorded-effects*
  (also log-and-replay IO responses)? The v1 sim runtime is schedule-only by construction (no real IO);
  the guarantee's shape past that boundary is the G6 open edge. Blocks the honest framing of the DST
  headline once real IO backends exist.

## Revisit if

- **The shared-everything-threads substrate ships** (shared GC structs across real threads, CG Phase 1
  → shippable) → the STM concurrency privilege (G3, ADR-0030) returns: a runtime-owned shared heap,
  read-set validation, `retry`-wakeup. The G2/G3 backend picture gains a genuine parallel path.
- **Component instantiation proves µs-cheap AND the GC-value copy tax is tolerable** (the #116
  measurement) → components-as-actors (G2) is promotable from isolation-backend toward a fine-grained
  spawn backend. Until measured, it stays deferred.
- **The WASI-0.3 async ABI does NOT compose with grade-directed lowering** (the G8 spike fails) → the
  first production backend target changes; the scheduler-as-handler model (G1) is unaffected (it is
  backend-agnostic), but the near-term production path is re-planned.
- **A concurrency (not model-checking) construct needs resuming one continuation twice** (falsifies
  G5) → the multi-shot question (Q22/Q27, `multishot-survey.md`) moves onto the concurrency critical
  path; none surfaced in OCaml-5-class evidence.
- **The `!` two-backend semantics observably split despite the Sendable fragment** (falsifies G7) →
  re-open the one-surface-two-backends claim; the `copy ≡ share` syntactic core (proven) makes this
  unlikely, but the contextual closure rides the parked LR.
- **Real IO handlers land and the replay guarantee must be pinned** (Q(conc-6)) → decide schedule-only
  vs recorded-effects for the DST replay contract; the v1 sim runtime's schedule-only guarantee is the
  floor, not the ceiling.

## Addendum ① (2026-07-11) — the lowering spike is MET: GO

The one gating spike ran (`tools/bench/wasi-async/`, survey §G8-SPIKE, merged from `b6bbcd2f`):
a WASI-0.3 **async component validated AND ran end-to-end** on wasmtime 45 (`task.return` → 42,
`-W component-model-async=y`); the full async canon-builtin set is implemented in wasm-tools 1.249.
Measured: the async lift is a **fixed ~0.7 µs/call bookkeeping tax** (~2.4× the sync floor),
payload-orthogonal — cheap enough to back cooperative scheduling. Model fit ABI-confirmed: the host
event loop blocks the *task* (not the instance), so the bang handler keeps the `pick` — the
scheduler-as-handler split survives contact with the real ABI, and grade 0/1/ω maps onto
sync-lift / async-lift / no-ABI-path (one-shot by construction; Q22/Q27 stay parked). Named residual:
`stream<T>` per-chunk throughput unmeasured — blocked on guest-std packaging (no nixpkgs
wasm32-wasip3 rust-std yet), NOT on the ABI. Implementation remains post-v1; the gate this ADR
placed on it is discharged.
