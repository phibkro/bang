<!-- note-status: active -->
# Nondeterminism as an effect + a DST handler + the sim-KV hello-world — the first Stage-7 consumer

> Design lane **ndet** (task #28, 2026-07-10). Slices `distributed-story.md` §2 **rung 2**
> (simulation testing / DST) down to its FIRST buildable increment: `Choice` as an ordinary
> user effect, a *seeded deterministic* handler that owns all the nondeterminism, and a
> replicated-KV hello-world run twice (same program, two seeds ⇒ two interleavings — the
> handler-swap demo). **Docs + draft `.bang` programs only.** Voice = the DBMS survey's
> ADR-inputs-not-decisions posture: this note produces evidence + a recommended shape + a
> precise gap list for the surface roadmap; the operator/manager decides.
>
> **SCOPE FENCE (operator-ruled, `distributed-story.md` header + `calm-as-grade-survey.md`):**
> certified CRDTs (rung 1 proof-export), CALM-as-grade (rung 3), the lattice/`lat` store, and
> convergence-as-a-proved-law are **POST-V1** and **out of scope here** — total-only, distinct
> monotonicity lattice, named as later rungs in §6, designed NOWHERE below. This note is rung 2's
> *entry increment*: the nondeterminism effect + the DST handler + the hello-world artifact, all
> expressible (with named honesty about the gaps) on the **v1 Stage-7 surface** (ADR-0095).

---

## 0 · TL;DR

```
the thesis on display : nondeterminism is an ORDINARY user effect (an `effect Choice {…}` decl +
                        a row label). The KERNEL is untouched — invariant #5 is not just respected,
                        it is the DEMO. "The scheduler/network is a runtime, and runtimes are values."
the DST handler       : a SEEDED, DETERMINISTIC handler for `Choice`. Feeding it a seed makes the
                        whole "distributed" run REPLAYABLE with ZERO real IO — no ADR-0084 needed,
                        because the network/scheduler IS a handler, not a syscall. Same program +
                        different seed/handler = different interleaving. THE paradigm-is-a-value proof.
the hello-world       : a replicated KV store (N replicas + simulated clients + simulated message
                        delivery) driven under a `Choice` handler. Run seed A ⇒ assert exact output;
                        run seed B ⇒ a DIFFERENT-but-still-deterministic interleaving. Convergence is
                        OBSERVED (assert replicas equal after quiescence), NOT proved-as-a-law (rung 1/3).
the HARD constraint   : ADR-0095 **D4 ret-shape** — v1 clause bodies are `ret w` ONLY. A stateful
                        seeded PRNG wants compute-then-return + carried-param UPDATE. Neither exists on
                        the v1 surface. §5 designs the HONEST v1 version WITHIN the wall (stateless
                        seed-splitting: derive each op's coin from the op ARGUMENT, no mutable PRNG
                        register) and §7 names EXACTLY which future slice each blocked shape needs.
the surface caveat    : ADR-0095 D1's examples write `$net.read`; the LANDED named-cap perform surface
                        (ADR-0070) is BARE `h.read(x)` — no `$`. Draft programs below use the landed
                        `h.op(arg)` form; §4.1 flags the discrepancy as an ADR-input.
```

The one-sentence differentiator (`distributed-story.md` §1): everyone else *builds a bespoke
simulator*; bang *installs one handler*. This note is the smallest artifact that makes that
sentence executable — and it does so with the kernel closed and the surface at exactly its v1 power.

---

## 1 · `Choice` as an ordinary user effect (the invariant-#5 showcase)

The whole distributed story rides on ONE claim: **nondeterminism is not a language feature, it is a
value.** A program that "makes a nondeterministic choice" performs an effect; a *strategy* for
resolving those choices (seeded-deterministic, random, exhaustive DFS/BFS, adversarial) is a
*handler*. The kernel — thunks, force, effect rows, handlers, STM — never learns any of this exists.

### 1.1 The declaration (landed surface, ADR-0092)

```bang
effect Choice { pick : Int -> Int }
```

Read as: an effect named `Choice` with one operation `pick : Int -> Int`. `pick n` means *"choose a
value in `[0, n)`"* — the sole primitive nondeterministic act. A `Choice` handler DECIDES what `pick n`
returns; the program that performs `pick` is agnostic to the strategy. That is the entire mechanism.

- `effect Choice { pick : Int -> Int }` parses today (ADR-0092 §Status: `effect`-decl landed on main,
  `.effectD` in `Bang/Frontend/Surface.lean:1729`; label allocated `ℓ := 4 + declIndex`; the
  program-derived `EffSig` types `pick` at the user label).
- `pick` is a **fresh** op name (not one of the built-in reserved `raise`/`get`/`put`/`new`/`read`/
  `write`/`pick`… — check: `pick` is NOT reserved, confirmed no collision with the built-in op set in
  `capOpSig`). A future op-namespacing pass (Q34) dissolves this reservation entirely; v1 just needs a
  non-colliding name, and `pick` qualifies.
- The label appears in the row of any computation that performs it: a function that calls `pick`
  has `Choice` in its `with` row. **The row is the census of nondeterminism** — grep the type, see
  every place a choice is made. This is what makes "install the exploring handler" a type-directed
  operation later (the model-checker handler must cover every `Choice` in the row).

### 1.2 Why this is the thesis, not a convenience

`distributed-story.md` §1: *"Nondeterminism is an effect too."* Three consequences fall out for free,
none of which touch the kernel:

```
consequence                         mechanism (all library / handler, zero kernel change)
──────────────────────────────────────────────────────────────────────────────────────────
deterministic replay = a handler    a seeded `Choice` handler replays bit-for-bit (§2). Not a
                                    "replay mode" bolted onto a runtime — a different VALUE installed.
the model checker = a handler       a `Choice` handler that enumerates every branch (DFS/BFS) turns
                                    "run the model checker" into "install the exploring handler."
                                    (POST-v1: needs multi-shot resumption — the ω-channel, §7.)
the network = a handler             message reordering/drop/partition are `Choice`s resolved by a
                                    scheduler handler. The simulator and the real network are two
                                    handlers of the SAME effect (ADR-0084's Net is the real one).
```

The kernel already ships the hard part — identity-keyed dispatch, effect rows as join-semilattices,
handler install/pop — so `Choice` is *just another effect declaration*. The distributed story's entire
rung-2 substrate is **library code the user could have written**. That is the moat made concrete.

---

## 2 · The DST handler — a seeded deterministic scheduler as a value

**Deterministic Simulation Testing (DST)** is FoundationDB's technique: run the whole distributed
system in a single process, with ONE component owning every source of nondeterminism (message order,
drops, partitions, crash/restart, clock), seeded so a failing run replays exactly. In bang, that
"one component" is **a `Choice` handler** — not a framework, not a runtime mode, a value you install.

### 2.1 The shape

```
handle <the whole simulated system>
with Choice as sched {
  pick(n) => ret <the n-bounded coin for this step, derived from the seed>
}
```

The handled body is the *entire* simulated distributed run: replicas, clients, and the message bus,
all performing `Choice.pick` whenever the "real" system would face nondeterminism (which message to
deliver next, whether to drop it, which client acts). The handler `sched` resolves every one of those
picks from a **seed**. Two properties fall out:

```
REPLAYABLE : same seed ⇒ same sequence of pick-results ⇒ same interleaving ⇒ same outputs, every run.
             A failing run is reproduced by re-running with its seed. No real IO ⇒ nothing to flake.
SWAPPABLE  : different seed (or a different handler entirely — random, DFS, adversarial) ⇒ different
             interleaving of the SAME program. `handle body with Choice as sched { … }` is the only
             thing that changes. THE "same program, different runtime" demo (§3.2).
```

No real network, no threads, no clock — the "distributed" system is a single deterministic `bang eval`.
This is why rung 2's entry increment does **not** wait for ADR-0084 (the IO/Net prong): the simulator
handler needs no IO at all. IO is the *other* handler of the same effect, landed later.

### 2.2 The seeded-PRNG problem, and the v1 wall

A textbook seeded scheduler is **stateful**: it holds a PRNG register, and each `pick(n)` (a) reads the
register, (b) computes `next = lcg(register)`, (c) UPDATES the register to `next`, (d) returns
`next mod n`. On the v1 Stage-7 surface this is **triply blocked**:

```
what the stateful PRNG wants          v1 Stage-7 status (ADR-0095)          blocked by
──────────────────────────────────────────────────────────────────────────────────────────────
(a) read a carried seed register      `param` names the carried Val,       OK — read-only param IS v1
                                      READ-ONLY (D1 example)                (ADR-0095 D1)
(b) compute `lcg(seed) mod n`         clause body must be `ret w`, a        D4 ret-shape wall +
    then return it                    compute-then-return body is NOT       ADR-0065 binop typing +
                                      typeable in v1                        Q27 grade surfacing
(c) UPDATE the register to `next`     param-UPDATE (put-like clause) is     ADR-0092 D5 /
    for the next pick                 DEFERRED — v1 param is read-only      ADR-0087 §Open-questions
(d) name the carried param at all     no surface binder for the carried    the carried-param binder
    in a clause head                  param (probe finding 3/4)            slice (probe WALL, §7)
```

So the honest v1 seeded handler **cannot** carry a mutable PRNG register. §5 designs the version that
lives WITHIN the wall (derive each coin *statelessly* from the op argument), and §7 turns this table
into the precise ask on the surface roadmap — arguably this note's most valuable output.

---

## 3 · The sim-KV hello-world

One artifact, walked twice. A replicated key-value store, simulated end to end, run under two seeds.

### 3.1 The pieces (all ordinary bang values, no kernel or runtime magic)

```
piece              what it is                                   how nondeterminism enters
────────────────────────────────────────────────────────────────────────────────────────────────
replicas           N copies of a KV map (v1: last-writer-wins   —  (state lives in the handler-carried
                   per key; NO CRDT merge — that's rung 1)          world; see §5 externalization)
clients            a fixed script of put/get requests            —
message bus        a queue of (from, to, op) messages in flight  `pick` chooses WHICH pending message
                                                                  delivers next ⇒ the interleaving
delivery policy    deliver / drop / reorder                      `pick` chooses drop-vs-deliver ⇒ the
                                                                  fault injection (partition = drop-all)
quiescence check   after the script drains, are all replicas     OBSERVED (assert), not proved —
                   equal?                                         convergence-as-law is rung 1/3
```

The store is deliberately **last-writer-wins with a total order supplied by the scheduler** — NOT a
lattice/CRDT merge. Convergence here is *"the deterministic schedule drove every replica to the same
final map"*, checked by an equality assertion on the outputs, not by a proved join-semilattice law. The
CRDT-merge-law version is rung 1 (§6), explicitly not built here.

### 3.2 The handler-swap demo (the payoff)

```
run 1:  handle <sim> with Choice as sched { pick(n) => ret <coin from seed A> }   ⇒  outputs O_A
run 2:  handle <sim> with Choice as sched { pick(n) => ret <coin from seed B> }   ⇒  outputs O_B
                    └────────── the ONLY thing that changed is the seed ──────────┘
assert: O_A is replayable (re-run seed A ⇒ O_A again, exactly)
assert: O_B ≠ O_A in interleaving (different message order) BUT each replica set is internally consistent
```

Same program `<sim>`. Two runtimes (two seeds). Two interleavings, each deterministic. That is
"paradigm is a value; runtime is a handler installed at the use site" (invariant, ADR-0016) shown on
the distributed axis — with `<sim>` written once and the network's behaviour dialed entirely by the
installed handler.

---

## 4 · Draft `.bang` programs (against the ADR-0095 ruled grammar)

> These are **drafts against a surface that has NOT landed** (Stage-7 `handle e with Name` is not on
> `origin/main` as of `8470d6b`; only the `effect`-decl half is landed). They are written to the
> ADR-0095 ruled grammar so they are ready to validate the instant the surface lands (§8). Full
> programs live in `examples-draft/` on this branch, mirroring the corpus style (`examples/*/main.bang`
> + `README.md` + `expected.txt`), but under `examples-draft/` to signal they do not yet run.

### 4.1 The surface, pinned exactly (with the one live discrepancy)

```
form                       spelling used below            source of truth
──────────────────────────────────────────────────────────────────────────────────────────
effect declaration         effect Choice { pick : Int -> Int }        ADR-0092 (LANDED)
handler install + binder   handle e with Choice as sched { … }        ADR-0095 D1 + D1a (as h MANDATORY)
clause                     pick(n) => ret <w>                         ADR-0095 D1/D3/D4/D5
perform (named cap)        sched.pick(k)      -- BARE, no `$`         ADR-0070 (.dotPerform, LANDED)
```

**★ ADR-INPUT — the `$` discrepancy.** ADR-0095 D1's examples write the perform as `$net.read 1`. The
LANDED named-cap perform surface (ADR-0070, `Bang/Frontend/TypeCheck.lean:1094` `.dotPerform`) is BARE
`h.read(x)` — no leading `$`, args parenthesized. The elab probe (`stage7-elab-probe.md`) already
tested `h.fetch(5)` (bare) end-to-end; nothing in the pipeline consumes `$h.op`. Either ADR-0095's D1
examples are provisional shorthand (the probe note calls the whole D1 example set provisional) or the
surface should re-add `$` before a cap-perform. **Recommendation: the drafts below use the landed bare
`h.op(arg)` form**; the ADR-0095 examples should be corrected to match, OR the discrepancy ruled
explicitly. This is a cheap, concrete surface-roadmap input the first consumer surfaces.

### 4.2 Draft A — the minimal `Choice` tracer (fits v1 EXACTLY, no gaps)

A pick handled by a constant clause: the smallest program proving `Choice`-as-effect works end to end.
This one has **zero** dependence on the blocked shapes — it is the first `#guard` to write when the
surface lands.

```bang
-- examples-draft/choice-min/main.bang
effect Choice { pick : Int -> Int }

let main =
  handle
    sched.pick(10)
  with Choice as sched {
    pick(n) => ret 0        -- the trivial deterministic scheduler: always choose 0
  }
-- evaluates to 0
```

Fits v1 cleanly: clause body `ret 0` is ret-shape (D4 ✓); implicit tail-resume (D5 ✓); one op, curried
single arg (D3 ✓); `as sched` binder present (D1a ✓). **This runs the instant Stage-7 lands** — it is
the `Choice` analogue of ADR-0095's own `read(n) => ret (n*10)` tracer.

### 4.3 Draft B — a two-pick program showing the interleaving is handler-chosen

```bang
-- examples-draft/choice-two/main.bang
effect Choice { pick : Int -> Int }

let main =
  handle
    let a = sched.pick(2) in       -- "which message delivers first" — 0 or 1
    let b = sched.pick(2) in       -- "deliver-or-drop the next"     — 0 or 1
    a + b                          -- a stand-in "observable outcome" of the interleaving
  with Choice as sched {
    pick(n) => ret 1               -- seed-as-constant: this scheduler always picks 1
  }
-- evaluates to 1 + 1 = 2
```

Swap the clause body to `ret 0` and the same program yields `0` — the handler-swap demo in miniature
(§3.2). Still fully v1: two performs, both `ret`-shape constant clauses. The *limitation this exposes*
is the whole point: a **constant** clause cannot make the two picks DIFFER from each other (both return
1). A real scheduler needs the coin to depend on step/seed — which is §5's stateless trick, or (for a
true PRNG) the §7 gaps.

### 4.4 Draft C — the honest sim-KV skeleton (v1-expressible core + NAMED gaps)

The full sim-KV is large; the v1-honest skeleton isolates what runs today from what is blocked. The
replicas/bus "world" is threaded as an ORDINARY value through `let`-bindings (externalized state, §5),
NOT carried in the handler param (which is read-only and unnameable in a clause, §2.2). Each `pick`'s
coin is derived **statelessly from the seed and the step index passed as the op argument** (§5.1), so
no mutable PRNG register is needed.

```bang
-- examples-draft/sim-kv/main.bang   (SKELETON — the scheduler clause is v1; the world-stepping
--                                    body uses only let/if/arithmetic, all v1 surface)
effect Choice { pick : Int -> Int }

-- a stateless seeded coin: coin(seed, step, n) = (lcg(seed + step)) mod n
-- lcg is an ordinary bang function (Div-fragment fold), NOT a handler-carried register.
let lcg = fun x => (x * 1103515245 + 12345)      -- (mod 2^31 elided in skeleton; Int in v1)

let main =
  handle
    -- the "sim": step the world by asking `sched` for each nondeterministic coin.
    -- world = (replica maps, message queue) threaded as a plain value (externalized state).
    let m0 = deliverStep world0 (sched.pick(pendingCount world0)) in
    let m1 = deliverStep m0     (sched.pick(pendingCount m0))     in
    quiescentEqual m1                                 -- 1 if all replicas equal, else 0
  with Choice as sched {
    -- v1-honest scheduler: the coin is a STATELESS function of the op ARGUMENT (the bound `n`,
    -- here carrying the pending-count) and a seed CLOSED OVER from the enclosing let (SEED below).
    -- NO carried PRNG register (that needs param-UPDATE, §7). Clause body is ret-shape (D4 ✓).
    pick(n) => ret ((lcg SEED) mod n)
  }
```

**What is v1-real here vs. skeletal:**

```
part                                         v1 status
──────────────────────────────────────────────────────────────────────────────────────
`effect Choice { pick : Int -> Int }`        LANDED surface ✓
`handle … with Choice as sched { … }`        ADR-0095 ruled grammar ✓ (lands with Stage-7)
`pick(n) => ret ((lcg SEED) mod n)`          ret-shape body — BUT `(lcg SEED) mod n` is a
                                             compute-then-return arithmetic body ⇒ HITS D4 (§7).
                                             The v1-CLEAN form returns a precomputed value (Draft B);
                                             this line is the shape that MOTIVATES the D4 lift.
`deliverStep`/`pendingCount`/`quiescentEqual`ordinary Div-fragment functions over an immutable
                                             world value (let-threaded) — v1 library code ✓
seed varies per run                          the handler-swap: change `SEED` (or the clause) ⇒
                                             different interleaving (§3.2) ✓
```

Draft C is deliberately the one that STRADDLES the wall: its scheduler clause `ret ((lcg SEED) mod n)`
is exactly a compute-then-return body (D4-blocked), which makes it the concrete carrier of the §7 ask.
Drafts A and B are the parts that run unchanged the moment the surface lands.

---

## 5 · Designing WITHIN the v1 ret-shape wall (the honest version)

The wall (§2.2): no compute-then-return clause body (D4), no carried-param UPDATE (ADR-0092 D5), no
clause-head binder for the carried param (probe WALL). Two moves make a *usable* seeded scheduler
anyway, both staying inside the v1 surface:

### 5.1 Stateless seed-splitting — derive the coin per-op, not from a register

Instead of a mutable PRNG register threaded pick-to-pick, make each pick's coin a **pure function of
(seed, a per-op nonce)**. The nonce is carried IN THE OP ARGUMENT: redefine `pick`'s argument to bundle
the bound `n` with a step counter the *caller* threads (the caller already threads the world value, so
threading a step index costs nothing):

```
stateful (blocked):   register r;  pick(n) => { c = lcg(r); r := next; ret (c mod n) }   -- needs D5 update
stateless (v1):       pick(n) => ret (lcg(seed ⊕ callerStep) mod n)                      -- seed closed over,
                                                                                          -- callerStep in the arg
```

The scheduler becomes a **splittable-PRNG** style function (the Haskell `splitmix`/`random` idiom): the
caller owns the step index (part of the world it already threads), the handler owns the seed (closed
over from the enclosing `let SEED = … in handle …`), and `coin = f(seed, step)` is a pure, replayable
function. This is genuinely how deterministic simulators avoid a global mutable RNG — it is not a
hack around the wall, it is a legitimate design that the wall happens to force us toward. **Replay and
seed-swap both work**: same seed ⇒ same `f(seed, step)` for every step ⇒ same run.

The ONE thing still blocked: `lcg(seed ⊕ step) mod n` is a compute-then-return body (arithmetic in the
clause), which is D4. See §7 — but note the *shape* is now register-free, so when D4 lifts (binop
typing + grade surfacing), the stateless scheduler is immediately expressible with NO further param
machinery. The stateless design **decouples the v1 ask down to just D4**, dropping the D5 param-update
dependency entirely. That is a real simplification the wall bought us.

### 5.2 Externalized world state via let-threading (not the handler param)

The replicas + message queue are threaded as an ordinary immutable value through `let`-bindings in the
handled body (`let m0 = step world0 … in let m1 = step m0 … in …`), the same idiom `state`-free code
already uses. The handler carries only the SEED (read-only param, or closed-over `let`), never the
mutable world. This sidesteps the carried-param-UPDATE (D5) and carried-param-binder gaps entirely for
the world: **only the seed lives near the handler, and the seed never changes** (§5.1 makes the coin a
function of seed+step, so the seed is constant). Externalization is the v1-honest substitute for a
stateful handler, and it costs only what functional state-threading always costs — explicitness.

### 5.3 What this v1 version CAN and CANNOT demonstrate

```
CAN (v1, once Stage-7 + D4 land):                CANNOT (needs the §7 future slices):
─────────────────────────────────────           ──────────────────────────────────────────────
• Choice as an ordinary effect (§1) — TODAY      • a stateful PRNG register carried in the handler
  (effect-decl half is already landed)             (needs param-UPDATE, D5)
• seeded deterministic replay (§5.1)             • the model-checker handler that EXPLORES every
• handler-swap: seed A vs seed B ⇒ two             branch (needs multi-shot / ω-resumption, Q22/Q27)
  deterministic interleavings (§3.2)             • convergence proved AS A LAW (rung 1 + Q43)
• observed convergence (assert replicas equal)   • CALM: CAS typed coordination-demanding (rung 3)
```

The v1 story is complete AS A DEMO of the thesis (nondeterminism-as-value, runtime-as-handler,
replayable-sim-with-no-IO) — it just isn't the model checker or the certified CRDT yet, and it says so.

---

## 6 · Scope fence — what is POST-V1 and designed NOWHERE here

Operator-ruled (`distributed-story.md` header 2026-07-09; `calm-as-grade-survey.md` §0/§ADR-INPUTS):
the distribution axis is **post-v1**, total-only, with a **distinct** monotonicity lattice (not the
0/1/ω Mult channel). This note designs the rung-2 *entry* increment ONLY. The following are named as
later rungs and get NO design here:

```
rung                         what it adds                        why NOT here
────────────────────────────────────────────────────────────────────────────────────────────
1 · certified CRDTs          per-key CRDT registers (LWW/OR-set) the sim-KV here is LWW-by-schedule,
   (NEAR)                     with `merge` PROVED a join-         NOT a proved-merge CRDT. Rung 1 is
                             semilattice (lawInstancesOf + #60,   the law-export hop (Q43), a separate
                             lifted to Lean by Q43)               lane. §3.1 deliberately avoids merge.
2 · DST (THIS NOTE's rung)   seeded scheduler handler owning all  ← the entry increment IS §1–§5.
                             nondeterminism; convergence OBSERVED  The multi-shot exploring handler and
                             (assert), forking = multi-shot        the forking model-checker are the
                             ω-channel for the model checker       POST-v1 half of rung 2 (Q22/Q27).
3 · CALM as a grade          monotone ops typed coordination-FREE; a DISTINCT monotonicity lattice
   (RESEARCH)                the row flags which ops (CAS) need    (calm-survey §0). Genuinely novel,
                             consensus                            post-v1, designed in the CALM survey.
4 · mechanized consensus     Raft/Paxos refinement proofs         FAR (Verdi territory). Named only.
```

The CAS key from `distributed-story.md` §4 (the one op CALM flags non-monotone) is **rung 3** — this
note's sim-KV is LWW and has no CALM story. Do not build the `coord` label or the `lat` store here.

---

## 7 · The gap list — the first real consumer's demands on the surface roadmap (the ADR-input)

This is the note's most valuable output (per the brief). Each row is a concrete shape the DST handler
wants, its v1 blocker, the future slice that unblocks it, and how central it is to the demo.

```
#  the shape the DST handler wants          blocked by (v1)                unblocked by             centrality
─────────────────────────────────────────────────────────────────────────────────────────────────────────────
G1 compute-then-return clause body:         ADR-0095 D4 ret-shape wall     ADR-0065 binop typing    CORE — the
   `pick(n) => ret (lcg(seed⊕step) mod n)`  (clause body must be `ret w`,  + Q27 grade surfacing    seeded coin
   — arithmetic in the clause               a computed body isn't          (the compound D4 exit    IS a computed
                                            typeable)                      gate ADR-0092 D3 names)  body. §5.1.
─────────────────────────────────────────────────────────────────────────────────────────────────────────────
G2 carried-param UPDATE (`put`-like):       ADR-0092 D5 / ADR-0087         the param-update slice   AVOIDED by
   a stateful PRNG register the handler     §Open-questions (v1 param is   (D5)                     §5.1's
   mutates each pick                        READ-ONLY)                                              stateless
                                                                                                    trick — NOT
                                                                                                    needed for v1.
─────────────────────────────────────────────────────────────────────────────────────────────────────────────
G3 a clause-head BINDER for the carried     the carried-param binder gap   the carried-param        AVOIDED by
   param (name the seed IN the clause head, (probe finding 3/4, WALL:      binder slice (probe      §5.2
   `pick(n, p) =>` or an ambient `param`)   `handleCustomS` binds param    names it as the single   externalizing
                                            under an UNWRITABLE `#param`   most concrete open Q      the world;
                                            sentinel)                      for the ADR)             seed via `let`.
─────────────────────────────────────────────────────────────────────────────────────────────────────────────
G4 multi-shot / first-class resumption:     v1 one-shot pin (ADR-0085 D2); Q22 (closure cap-rep)    POST-v1 —
   the model-checker handler forks a run    D5 reserves `resume` but v1    + Q27 (resumption        the EXPLORING
   at each `pick` (the ω-channel)           is implicit tail-resume only   grades); the rq22        handler, rung-2
                                                                          ω-channel               back half. §5.3.
─────────────────────────────────────────────────────────────────────────────────────────────────────────────
G5 the `$`-vs-bare perform discrepancy      ADR-0095 D1 writes `$net.read`;— rule it: bare `h.op`   CHEAP — a
   (§4.1)                                    landed surface (ADR-0070) is   is landed; correct the   one-line ADR
                                            bare `h.read(x)`               D1 examples OR re-add $   correction.
```

**The distilled ask, ranked by leverage for THIS consumer:**

1. **G1 (compute-then-return, D4) is the ONE blocker on the critical path.** With §5.1's stateless
   design, the seeded scheduler needs *only* D4 to lift — not D5, not the param binder. Every other
   stateful-handler gap (G2, G3) is DESIGNED AROUND by externalization + seed-splitting. So the first
   real consumer's headline demand is narrow and specific: **land binop typing (ADR-0065) + grade
   surfacing (Q27) so a clause body can compute-then-return.** That single lift turns Draft C's
   scheduler from skeleton to runnable.
2. **G5 is free and should be ruled now** (bare-vs-`$` perform) — the drafts already assume the landed
   bare form; the ADR-0095 examples want a one-line correction.
3. **G2/G3 are NOT on the v1 critical path** — the stateless externalized design retires them for the
   DST use case. They return as *ergonomic* improvements (a stateful handler is nicer to write) and for
   OTHER consumers, not as blockers here. This is a genuine finding: the DST handler, designed
   honestly, needs *less* surface than it first appears.
4. **G4 (multi-shot) is the boundary between rung-2's two halves** — the seeded *replay* scheduler (this
   note) is one-shot and v1-shaped; the *exploring* model-checker is multi-shot and post-v1. Naming G4
   pins exactly where v1 stops.

---

## 8 · If the surface lands while this is in flight (the validation plan)

The brief's item 6: a draft that RUNS beats a draft that should. If Stage-7 `handle e with Name` lands
on `origin/main` before this note is done, the plan is:

```
1. fetch origin/main; confirm `handleCustomS` (or its final name) is in Bang/Frontend/Surface.lean.
2. move examples-draft/choice-min → examples/choice-min (Draft A, §4.2) — the zero-gap tracer.
3. run `lake exe bang run examples/choice-min/main.bang`; assert it prints 0.
4. do the same for Draft B (§4.3) — assert 2, then swap the clause body and assert 0 (the handler-swap).
5. report ACTUAL outputs (not "should be") to team-lead; downgrade any prediction that the real
   `bang eval` contradicts. Draft C stays in examples-draft/ until G1 (D4) lifts.
```

As of this lane's done-call, Stage-7 is NOT landed (`origin/main` at `8470d6b`; only the `effect`-decl
half is on main — verified `no handleCustomS in Bang/`). So the drafts are validated against the ruled
grammar (ADR-0095) and the LANDED perform/effect-decl surface, not a live `bang eval`. The moment the
surface lands, steps 2–5 above make Drafts A and B real.

---

## Sources

Local (read this lane, on `design-ndet-dst` off `origin/main` `8470d6b`):
- `docs/notes/distributed-story.md` — the arc being sliced (§2 rung 2 = DST; §4 KV hello-world; the
  post-v1 header ruling this note fences to).
- `docs/notes/calm-as-grade-survey.md` — the POST-V1 fence (§0 verdict, §6 scope; the `lat` store +
  `coord` label + CALM-as-grade all ruled post-v1, distinct lattice — designed NOWHERE here).
- `docs/decisions/0095-stage7-handler-surface.md` — the ruled grammar: D1 (`handle e with Name { op(x)
  => body }`), D1a (`as h` MANDATORY), D3 (curried), D4 (ret-shape wall — the hard constraint), D5
  (implicit tail-resume, `resume` reserved). The drafts target this.
- `docs/notes/stage7-elab-probe.md` — the real mechanics gotchas: bare `h.op` perform (not `$h.op`),
  the carried-param binder WALL (G3), the label-rewrite slot, reserved-op parse behaviour.
- `docs/decisions/0092-stage3-typing-user-effects-program-derived-effsig.md` — the `effect`-decl surface
  (LANDED); the D3 ret-shape wall's origin; D5 param-update deferral (G2).
- `docs/decisions/0070-surface-named-capabilities.md` — the LANDED named-cap perform surface (`with … as
  h`, bare `h.op(arg)`), the `.dotPerform` lowering the drafts assume (G5).
- `examples/{handle,state,stm,effect-op-arith}/` — the corpus style the `examples-draft/` programs mirror.

External (the technique being sliced, from `distributed-story.md`'s own citations — not re-verified this
lane):
- FoundationDB deterministic simulation testing — the "one component owns all nondeterminism, seeded for
  replay" technique §2 is bang's handler-shaped restatement of.
- `distributed-story.md` §2's rung-2 mechanism note (multi-shot ω-channel for the exploring handler,
  rq22) — the G4 boundary.
