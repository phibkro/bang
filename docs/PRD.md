# bang-lang — Product Requirements (v0)

> The product definition. Volatile at the edges, stable at the spine. Pairs with `ROADMAP.md`
> (the *how/when*) and `CONTEXT.md` (current position). Established 2026-06-22 via the
> product-zoom-out session (decisions logged in §8).

## 1. What bang-lang is

A **multi-paradigm programming language whose paradigms and runtime are values, not language
features** — built on one small kernel (thunks · effects · handlers · STM), formally verified in
Lean, and compiled through a verified two-hop pipeline to WebAssembly.

```
source(.bang) → graded-CBPV semantics → CalcVM (Bahr-Hutton) → WasmFX (Benton-Hur LR)
                └─────────── every hop kernel-checked correct ───────────┘
```

Imperative, reactive, actor, transactional — each is **ordinary library code** over the kernel, not
a built-in. A program is a **description** until forced (`$`); a paradigm is **which effects are in
a function's row**; a runtime is **a handler installed at the use site**.

## 2. The differentiator (the moat)

Three claims, in increasing distance-from-done:

1. **Paradigms are values.** One kernel; mutability/reactivity/actors/transactions are libraries.
   (Partially demonstrated in v0.1.)
2. **Evaluation stage & location are tunable** (§5). "Everything is a thunk" means *when* a value is
   forced — compile-time · runtime · dev-time — and *where* — local · at-the-data — are developer-
   controlled dimensions of the same model. Multi-stage programming unified through force, not bolted on.
3. **Proof by construction.** Correctness you get *structurally*, like Rust's memory safety —
   generalized to the **laws/relations between operations** on user-defined data objects. The
   verified kernel makes this real rather than asserted. **This is the north star; it is the
   least-built thing** (absent in v0.1; lang-bang has a verified kernel but no user-facing
   proof-by-construction yet). Honesty: v1 ships the *kernel's* guarantees **plus a minimal
   user-facing demonstration** — a verified data structure whose operation-laws are load-bearing
   (§6 rung 2); the *full* law-language is post-v1.

bang-lang is **not** "another effect-typed language." The moat is (2)+(3): a verified substrate that
turns paradigm-and-stage flexibility into *guarantees*, not conventions.

## 3. Users & use case

**Audience: software developers — human *and* agent.** The verified, proof-by-construction substrate
is uniquely valuable as a **target for AI code generation**: the language enforces correctness the
author (human or agent) might not — illegal states are *unrepresentable*, not merely linted. "A
language that is safe to generate into" is a distinct, modern positioning, and it compounds with the
moat (§2): an agent writing bang-lang gets the kernel's guarantees for free.

**North-star validation — the "golden test": a verified operating system written in bang-lang.** An
**xv6** reimplementation, in the lineage of **seL4** and **CertiKOS** (verified OS kernels). This is
the *herculean* far-target, **not v1** — but it is what gives the verification investment its reason:
you don't need proof-by-construction for a CRUD app; you need it for an OS kernel. The OS golden test
**characterizes the domain — correctness-critical systems programming — and justifies the moat (§2).**

### 3.1 The ladder (MVP → golden test)

The rungs between the first run and the OS are now **named** — each forces exactly one new language
capability, so the ladder doubles as a **feature-priority order**:

| rung | program | forces (new capability) | validates |
|---|---|---|---|
| 0 | tracer bullet | pure + throws | the language *runs* |
| — | **── v1 MVP ──** | | |
| 1 | State counter | State handler | paradigm-as-library |
| 2 | **verified stack** | user types + **load-bearing algebraic laws** | ★ the **moat**, minimal, *inside* v1 |
| 3 | ledger | STM + recovery (invert → rollback) | transactions |
| 4 | reactive cell | thunk re-fire (`=`/live) | reactivity *falls out* |
| — | **── post-v1 systems frontier ──** | | |
| 5 | memory allocator | **QTT grades surfaced** (use-once, no double-free) | ★ the **hinge** into systems |
| 6 | cooperative scheduler | one-shot handlers, **no preemption** | concurrency w/o the multi-shot frontier |
| 7 | toy filesystem | event-store State + at-the-data staging | persistence + location axis (§5) |
| 8 | device driver | effects at the IO edge | the effect/runtime seam |
| 9 | **xv6** | all of the above | the golden test — the WHY |

**Cooperative, not preemptive** (rung 6 — a deliberate constraint, CertiKOS precedent): composition is
far harder to prove under preemption, and *"programs as verification, not only computation"* is the
whole point — so we bite that bullet. This keeps the **multi-shot / actor frontier (ADR-0015) BESIDE
the xv6 path, not on it**: xv6's processes + scheduler need only one-shot handlers. (Likely a future
ADR when rung 6 is reached.)

The post-v1 rungs (5–8) are **sketched, not specified** — each gets scoped when reached. Don't
over-plan beyond rung 4 before the MVP runs.

## 4. The two repos & the convergence decision

| | v0.1 (`/srv/share/projects/bang-lang`, TS/Effect-TS) | lang-bang (this repo, Lean) |
|---|---|---|
| runs end-to-end | ✅ parse→infer→codegen→Effect-TS→stdout (`hello.bang`) | ✅ surface→graded-CBPV `Comp`→`Source.eval`→VALUE (rungs 0–4, from source text) |
| surface syntax | ✅ real `.bang` files, `!`-force UX | ✅ parser + `state`/`get`/`put`/stm/reactive demos run from source |
| paradigms | state/`mut` ✓ · reactive `on` ✓ · `transaction` (interp-only) ◑ · user-types ✓ · actors ✗ | ✅ State · STM (transactional, **verified** law) · reactive (**verified** liveness) · user-types (**verified**/tested laws) — rungs 1–4; actors post-v1 |
| guarantees | ❌ asserted (Effect-TS, no proofs) | ✅ **proven** (type/effect/resource safety, axiom-clean) |

**Decision (B): lang-bang grows its own surface.** lang-bang IS the product — surface-to-WasmFX, one
verified stack. **v0.1 is the design reference**, not the artifact: we mine its syntax, its `!`-force
UX, and its paradigm constructs, and *rebuild them verified*. v0.1 is the spec for what the surface
should feel like.

## 5. The evaluation-stage/location dimension (first-class)

"Everything is a thunk" + `$`/`!` (force) make evaluation **explicit**. The product treats *when* and
*where* a thunk is forced as a **developer-controllable axis**, not a runtime accident:

```
WHEN (stage)                          WHERE (location)
  compile-time  $comptime → inline    local        force here
  runtime       normal force          at-the-data  ship the description (bare name), force at the data
  dev-time      force while editing                 (enabled by D3: no implicit capture → serializable thunks)
                (live/incremental)
```

- **Reactivity falls out of this**, not a separate paradigm: a reactive value is a forced thunk that
  re-fires when a dependency thunk changes (`=` with a live RHS; ADR-0005/0006). How *far* reactivity
  goes (glitch-freedom, scheduling) is a dial on the stage policy, deferred per appetite.
- v0.1 already has `comptime { }` (compile-stage forcing) — evidence the axis is real and ergonomic.
- **v1 scope on this axis:** runtime + compile-time staging. Dev-time (live) and at-the-data
  (distributed) are post-v1 frontiers.

## 6. v1 / MVP scope

**v1 = the thinnest *multi-paradigm* proof that runs end-to-end on the verified kernel.**

| in v1 (the floor) | why |
|---|---|
| **imperative / State** (`mut`, KV store) | one State *effect*, **two handlers** — event-store (history, verifiable; the **default**) vs in-place (destructive, fast; **opt-in** when you don't need the history). The handler swap *is* "runtime is a value." Verification gets the event store; performance (invariant #7, later) gets in-place |
| **a verified data structure** (stack/queue; rung 2) | ★ the **minimal moat** — proof-by-construction is core value-prop (§2), so it must appear *inside* v1, even with the full law-language deferred. Laws between operations are *load-bearing*, not decorative |
| **transactions / STM** | the one privileged kernel primitive (the "everything is a handler" ceiling) |
| **reactivity** (basic) | *falls out* of thunks + the stage axis (§5); ship the basic form, dial deferred |
| **runtime + compile-time staging** | the two main `when`s |
| **a real surface** (parser → graded-CBPV) | the product spine (decision B); pulled forward (§7) |

| explicitly OUT of v1 (post-v1 libraries over the same kernel) |
|---|
| actor concurrency / message-passing (needs multi-shot — the reification frontier, ADR-0015) |
| full reactive streams / pub-sub / sinks |
| the **full** law-language (rich relations between operations) — the **minimal** load-bearing laws ship in v1 (verified stack, rung 2); the general surface is post-v1 |
| dev-time (live) + at-the-data (distributed) evaluation stages |
| **polymorphism** — v1 is **monomorphic** (concrete types; rung 2's stack is `Stack Int`). Hindley-Milner, then System F + effect-row + grade polymorphism, are staged post-v1 (ADR-0027) |

Two paradigms (imperative + STM) on one verified kernel **is** the multi-paradigm thesis, proven
thin; a verified stack (rung 2) shows the moat minimally so v1 isn't all promise. Reactive (basic)
rides along for free from the thunk model. Actors + the full law-language validate "it generalizes"
*after* v1.

## 7. The tracer bullet (pulled forward — green-lit)

The roadmap parked "anything runs end-to-end" at ◊5. Decision B makes the surface the *spine*, so we
pull a thin slice forward NOW, in parallel with the verification backbone:

```
TRACER BULLET (build before/alongside ◊3):
  one tiny .bang program (a State counter, or a Throws-guarded computation)
    → minimal parser (small construct subset)
    → graded-CBPV Comp
    → Source.eval
    → a VALUE, shown.

proves:   (1) bang-lang RUNS a program (the language is real)
          (2) the surface→kernel lowering works (de-risks the biggest unknown — invisible until tried)
          (3) gives a concrete artifact to grow, vs. more mid-pipe proofs
backbone: ◊3 CalcVM → ◊4 LR → ◊5 compiler continues IN PARALLEL as the verified spine
```

The full bullet (same program → CalcVM → WasmFX → wasm engine → same value) lands incrementally as
the backbone reaches it. The degenerate version (surface → `Source.eval` → value) is the near-term goal.

## 8. Decisions on record (this session)

1. **bang-lang is the LANGUAGE**, not the methodology. (The verified compiler is the *means*; a
   usable multi-paradigm language is the *end*.)
2. **Convergence = B**: lang-bang grows its own surface; v0.1 is the design reference. (§4)
3. **v1 = multi-paradigm MVP**: imperative/State + STM floor; reactivity falls out of thunks. (§6)
4. **Evaluation stage/location is a first-class, developer-tunable dimension.** (§5)
5. **Tracer bullet pulled forward** as an early parallel workstream. (§7)
6. **The MVP→golden-test ladder is named** — 9 rungs, each forcing one capability; doubles as
   feature-priority order. (§3.1)
7. **State = one effect, two handlers** — event-store (verifiable; default) vs in-place (fast; opt-in);
   the swap is "runtime is a value." (§6)
8. **The moat ships minimally in v1** (verified data structure, rung 2); full law-language post-v1. (§2, §6)
9. **Cooperative scheduling, not preemptive** (CertiKOS precedent) — keeps multi-shot/actors *beside*
   the xv6 path, not on it. (§3.1)

## 9. Open questions / risks

- ~~The ladder from MVP to the OS golden test is undefined.~~ **RESOLVED (§3.1)** — 9 rungs named,
  each forcing one capability. Residual: the post-v1 systems rungs (5–8) are *sketched, not specified*
  — each needs its own scoping when reached (the allocator's grade discipline, the scheduler's yield
  protocol, the filesystem's event-store layout). Don't over-specify before rung 5 runs.
- **Proof-by-construction depth.** What does user-facing "laws/relations between operations" actually
  look like in the surface? (the moat; post-v1, but its shape should be sketched so v1 doesn't
  foreclose it.)
- **Surface↔kernel lowering** is the biggest technical unknown — the tracer bullet exists to surface
  it early.
- **Roadmap reshape.** §7 pulls the surface ahead of its ◊5 slot; `ROADMAP.md` should be updated to
  show the surface tracer-bullet as an early parallel track (a follow-up, not done here).
- **Reactivity appetite.** How far (glitch-freedom, scheduling) — a dial, decide when it bites.

## 10. Non-goals (v1)

Performance optimization (invariant #7 — slow-but-correct beats fast-but-unverified); a package
ecosystem; IDE tooling beyond a minimal REPL/runner; the distributed (at-the-data) and live (dev-time)
evaluation stages; multi-shot handlers / actors; the **full** user-facing law-language (the minimal
verified-data-structure demo, §6 rung 2, *is* in v1).
