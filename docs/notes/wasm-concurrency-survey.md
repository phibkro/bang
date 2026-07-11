<!-- note-status: active -->
# Wasm components + concurrency — how bang should model concurrent execution (design survey)

> Operator's question (2026-07-11, verbatim): *"Grill the design question of utilising wasm
> features like components for concurrent execution. How should we model that in the language?"*
> This survey GROUNDS a design grill: it gathers the 2026-current wasm evidence, frames the
> forks, and recommends. It does **not** decide. Concurrency is POST-V1 (invariant #3 /
> ADR-0030 defer the shared-heap privilege); nothing here is v1 scope.
>
> Sibling surveys this rides on (don't duplicate): [`distributed-story.md`](distributed-story.md),
> [`ndet-dst-design.md`](ndet-dst-design.md), [`calm-as-grade-survey.md`](calm-as-grade-survey.md),
> [`os-inspiration-survey.md`](os-inspiration-survey.md), [`memory-management-survey.md`](memory-management-survey.md),
> [`multishot-survey.md`](multishot-survey.md), [`effect-algebra-survey.md`](effect-algebra-survey.md).

## §1 · The wasm facts, 2026-current (every row web-verified, dated)

The single most important 2026 fact: **WASI 0.3 shipped native async (2026-06-11) built on the
Component Model's OWN async ABI + a host-managed event loop — NOT on stack-switching.** Concurrency
arrived at the platform as a *cooperative, single-threaded, host-scheduled* effect, exactly the
handler shape bang already has — see §4. [BA-WASI03][techbytes-wasi03][wasi-roadmap]

| feature | phase / status (2026-07) | what it gives | engines | source |
|---|---|---|---|---|
| **Wasm 3.0 core** (GC · tail-call · exceptions · typed-fn-refs · memory64 · relaxed-SIMD · multi-mem) | **Finished / spec 3.0** (standardized 2025-09) | the whole ADR-0059 backend floor | wasmtime, V8, SM | [wasm-finished] |
| **Component Model** | CG **Phase 1** *formally*; tooling ships "1.0-track" (BA milestone, NOT a W3C phase) | shared-nothing linking, canonical ABI, resource types, `world` | wasmtime, jco | [wasm-inprog][road-cm10] |
| **WASI 0.3.0** (native async) | **Released 2026-06-11**; 0.3.x on a bimonthly train | `async func` · `stream<T>` · `future<T>`; host-managed shared event loop | wasmtime 43+, jco | [BA-WASI03][wasi-roadmap] |
| **Stack switching** (WasmFX / typed continuations) | CG **Phase 3** (implementation); x64+ARM64 backends upstreaming; SpecTec in progress | `cont.new`/`suspend`/`resume`/`switch` — green threads, coroutines, generators | wasmtime, Wizard (ref) | [wasm-inprog][ss-explainer][wasmfx] |
| **Shared-everything threads** | CG **Phase 1** (feature proposal) | true OS-thread spawn + **shared GC structs** across threads | V8 implementing; not shippable | [wasm-inprog][set-overview] |

Four facts that reshape the bang mapping:

1. **Component instances are shared-nothing.** A component *may not export a memory*; values are
   **copied** across the interface boundary via the canonical ABI (lift/lower), never shared by
   pointer. Each instance is an independently-sandboxable box that communicates *only* through
   typed function interfaces. GC-heap and linear-memory languages interoperate precisely *because*
   nothing is shared. [why-cm][ss-linking]
2. **WASI-0.3 concurrency is intra-instance and cooperative.** "Arbitrary numbers of guest tasks
   run concurrently in the **same** component instance"; the **host** drives one event loop; a
   blocking call suspends *that task* and lets the component keep running. No OS threads, no
   stack-switching used. [medium-hypercharge][BA-WASI03]
3. **Stack-switching continuations are one-shot by construction.** `resume`/`resume_throw`/
   `switch`/`cont.bind` **destructively modify** the continuation; any second use **traps**.
   Single-shot (linear) is the design, not an accident — no `cont.clone` exists. [ss-explainer]
4. **Cross-thread GC sharing is Phase 1** — years out, gated on shared-everything-threads. A
   GC-language wanting shared mutable heap across real threads has *no shippable path* in 2026;
   the only shippable multi-thread story is shared *linear* memory (the old threads proposal). [set-overview]

## §2 · The three mapping hypotheses (verdicts)

### (a) COMPONENTS-AS-ACTORS — one component instance per actor, `!` crosses the canonical ABI

**Argues FOR strongly on isolation.** Shared-nothing linking IS actor semantics made structural:
no shared mutable state, communicate only by typed messages (copied, not aliased). `!` actor-send
(ADR-0007) crossing the canonical ABI is a near-exact fit; a component's `world` (its import/export
interface) IS a typed mailbox contract; row-attenuation (§3) = the component's allowed row =
its `world`. Immutable-value sharing is *safe by copy* — the ABI copies, so no GC-heap-sharing
problem for messages.

**Where it strains (the real costs):**
- **Spawn dynamism.** Actors want cheap dynamic `spawn`; component *instantiation* is a
  coarse, relatively heavyweight unit (instantiate-a-module cost, its own memory), not a
  green-thread. Millions of actors ≠ millions of component instances. Unverified at the
  per-spawn-µs level in 2026 sources — flag as an open measurement.
- **No shared GC heap across instances** — by design (§1.1). Large immutable structures shared
  by *reference* between actors (bang's thunks/closures on the WasmGC heap, `memory-management-survey.md`)
  can't cross a component boundary by pointer; they'd be *copied*. For a language whose values are
  GC-heap thunks this is a real semantic tax, not free.
- Component instantiation is a *deployment/packaging* boundary more than an *intra-program
  concurrency* primitive.

**Verdict:** **A DEPLOYMENT/ISOLATION BACKEND, not the intra-program concurrency model.** Components
are the right unit for *coarse-grained, security-isolated actors across a trust boundary* (the
plugin/sandbox/distributed story — pairs with `os-inspiration-survey.md`'s pledge-as-a-type and
`distributed-story.md`'s network-as-handler). They are the WRONG unit for fine-grained in-process
concurrency (green threads). Keep as backend (c-iii), don't make it the language model.

### (b) THREADS + STM — shared-memory concurrency inside one component, privileged STM over the shared heap

**The seat the kernel already reserves** (invariant #3, ADR-0030: privilege = concurrency-only;
the shared-heap STM form *returns* post-v1). Classic, well-understood, and STM is genuinely the
right privileged primitive for it.

**What 2026 actually gives a GC-language here:** *almost nothing shippable.* Shared mutable **GC
structs** across threads are Phase 1 (shared-everything-threads, §1.4) — years out. The only 2026
shippable shared-memory is shared **linear** memory (old threads proposal), which a GC-heap
language like bang doesn't use for its values. So the privileged-shared-heap-STM story is blocked
on a proposal that *hasn't landed* and is the one place bang cannot polyfill (a handler cannot
conjure a runtime-owned heap that survives across independent computations — ADR-0030 §Why).

**Verdict:** **THE RESERVED SEAT, BUT BACKEND-BLOCKED UNTIL SHARED-EVERYTHING-THREADS SHIPS.**
Correct to keep the STM privilege named and reserved. Wrong to plan the *v1.x* concurrency story
around it — its wasm substrate is Phase 1. STM-as-a-*handler* (the transactional handler, ADR-0030,
already v1) covers single-threaded transactional semantics *now*; the privileged parallel form
waits on the substrate.

### (c) THE HANDLER-SWAP STORY AS THE UNIFIER — concurrency ops as an ordinary effect, handlers = schedulers

Concurrency surface ops (`spawn`/`yield`/`await`/`send`) become one **ordinary effect** (extend the
`Choice`/`Sched` effect already demonstrated in `ndet-dst-design.md`). Handlers ARE schedulers:
- **deterministic-sim handler** = the DST story, *already shipping* (`examples/ndet-*`, the seeded
  replayable `Choice` handler — same seed ⇒ same interleaving ⇒ byte-identical output);
- **real wasm-backed scheduler** = a second handler of the SAME effect, targeting the WASI-0.3
  host event loop (§1.2) for cooperative tasks, or components (a) / threads (b) for isolation/parallelism.

This is *exactly* the moat thesis ("runtimes are values") on the concurrency axis, and it makes
(a) and (b) **two backends of the real-scheduler handler**, not competing language models. The
2026 platform *converged onto this shape*: WASI-0.3's host-driven cooperative event loop IS a
scheduler-as-handler at the platform level (§1.2).

**Verdict:** **THE BANG-NATIVE ANSWER. Adopt as the language model; (a)/(b) are its backends.**
The strongest evidence is that it's not speculative — the sim-scheduler handler is *demonstrated
and passing* today, and the production platform (WASI-0.3) independently arrived at the same
cooperative-scheduler-as-host-loop structure.

## §3 · Row / grade placement

Concurrency should enter primarily the **ROW**, with the coordination question deferred to the
CALM `coord` label (already surveyed) — **not** a new grade axis. Reasoning:

- **`spawn`/`await`/`send` are effects** → a `conc` (or `Sched`) **row label**, exactly like
  `Choice` today. No new primitive (invariant #5 intact); handlers dispatch it.
- **Coordination is the CALM `coord` label** (`calm-as-grade-survey.md` arm (i)): non-monotone ops
  carry `coord`; a `coord`-clean row licenses the coordination-free replication handler. This is
  the *distributed* face of the same row story.
- **Grading-the-row is REJECTED** (`calm-as-grade-survey.md` arm (ii)): a per-label
  multiplicity/weight breaks invariant #2 (rows are *sets*, union = join — ADR-0001/0018). Do not
  reach for a "concurrency grade axis." The one grade that IS load-bearing is the **resumption
  grade** (0/1/ω — `multishot-survey.md` / Q27), and that's about the *continuation*, not the row.
- **What typing buys at the component boundary:** a component's `world` = its allowed row.
  **Row-attenuation** (`os-inspiration-survey.md`, `drop-to {…} in c`) IS the interface contract —
  pledging a component to a narrower row is `pledge`/`seccomp`-as-a-type, and it's the same
  mechanism whether the boundary is a component instance or an in-process handler scope.

## §4 · Determinism / DST

bang's reference semantics is **deterministic**; nondeterminism enters at *exactly one seam*: the
**scheduler handler's `pick`** (the `Choice` effect, `ndet-dst-design.md`). This is already the
ndet-design answer and is *demonstrated*:

- **Always-available sim runtime.** The seeded, stateless-seed-splitting `Choice` handler is
  replayable by construction (same seed ⇒ same run). DST (FoundationDB-style simulation) is not a
  bolt-on — it's the *default* scheduler handler. Every concurrent bang program is replayable-by-default;
  you *opt into* real nondeterminism by swapping to the wasm-backed scheduler.
- **The platform preserves this.** WASI-0.3's host event loop is cooperative and single-threaded
  (§1.2) — the nondeterminism is *scheduling order*, which the `Choice`/`Sched` handler already
  models as a `pick`. A deterministic replay of a production trace = feed the recorded pick-sequence
  to the sim handler. No new mechanism.
- **Real threads (b) would break replay** — genuine parallelism reintroduces nondeterminism the
  handler can't fully own (data races on shared memory). This is another reason (b) stays reserved,
  not default: the cooperative/component paths keep the DST-always-available property; the
  shared-heap-threads path trades it away for parallelism.

## §5 · Continuation requirements (the machinery question)

**One-shot + the WasmGC frame-chain SUFFICES for green-threads-on-wasm. Multi-shot is NOT
required for concurrency.** Evidence, converging from three directions:

- **The platform is one-shot.** Wasm stack-switching continuations are one-shot by construction
  (§1.3): `resume`/`switch` destructively consume; second use traps. Green threads, coroutines,
  async/await are *explicitly* the use-cases the one-shot proposal targets. [ss-explainer]
- **OCaml 5 precedent** (`multishot-survey.md`): one-shot is *sufficient for concurrency* and buys
  O(1) fiber switch + linear-resource safety. bang is deep, one-shot already.
- **bang's v1 backend already covers it without WasmFX.** `memory-management-survey.md`: v1 needs
  only abort→exception + tail→call on stock Wasm 3.0; the WasmGC frame-chain (managed `struct`
  frames linked by `.parent`) IS the general-resumption runtime. WasmFX `switch` is a *post-standardization
  fast-path for the `general` slot only*, never a v1 requirement. Green-threading a cooperative
  scheduler = suspend/resume of one-shot continuations = exactly what the frame-chain (or, later,
  WasmFX one-shot `switch`) provides.
- **Where multi-shot WOULD be needed** — DST *execution-forking* (explore both branches of a
  `pick` from the same state, `distributed-story.md` rung 2). That's the `multishot-survey.md`
  ω-channel, and its verdict stands: stay one-shot + explicit-copy by default; if ever needed,
  the hybrid (labelling for 0/1, closure/reify for a *statically-marked* ω-channel — Koka `fun`/`ctl`)
  is the endgame, gated by Q22/Q27. Concurrency (spawn/await) does **not** force it; model-checking
  *forking* is the only thing that might, and even that is copy-able.

## §6 · THE GRILL SHEET — the sharpest questions to grill, with evidence-backed default answers

**G1 · Is concurrency a language model or a backend?**
*Default:* Language model = **scheduler-as-handler** (§2c); components (§2a) and threads (§2b) are
two *backends* of the real-scheduler handler. *Falsified if:* a workload needs fine-grained
in-process parallelism that a cooperative single-instance scheduler can't express AND components
are too coarse to stand in — i.e. if the shared-heap-threads seat (b) turns out to be on the
critical path *before* its wasm substrate ships. Evidence says no: 2026 platform converged on
cooperative-scheduler (§1.2).

**G2 · Do we bet on components-as-actors as THE concurrency primitive?**
*Default:* **No** — components are a *deployment/isolation/distribution* boundary (coarse,
shared-nothing, copy-crossing), not an intra-program spawn primitive. *Falsified if:* component
instantiation proves cheap enough (µs-scale) to be a green-thread AND the copy-crossing tax on
GC-heap values is tolerable. Both are *unverified in 2026 sources* — this is the top thing to
web-check-again before the grill, and the top OQ (§7).

**G3 · Does the STM privilege stay reserved, or get de-scoped?**
*Default:* **Stays reserved** (invariant #3, ADR-0030) but is **backend-blocked** — its wasm
substrate (shared-everything-threads + shared GC structs) is Phase 1, years out (§1.4). The
transactional *handler* covers single-threaded STM now. *Falsified if:* we decide bang's parallel
story will ride shared *linear* memory (old threads) rather than shared GC — but that fights the
GC-heap value model (`memory-management-survey.md`).

**G4 · Row or grade for concurrency?**
*Default:* **Row** (a `conc`/`Sched` label; coordination = CALM `coord` label). NOT a grade axis
— grading-the-row breaks invariant #2 (§3). The only load-bearing grade is the *resumption* 0/1/ω
grade, which is about the continuation, not the row. *Falsified if:* a concurrency property is
found that is genuinely *quantitative per-label* (a coeffect) and not expressible as set-membership
— none surfaced in `calm-as-grade-survey.md`.

**G5 · Do spawn/await need multi-shot continuations?**
*Default:* **No** — one-shot + frame-chain suffices; the platform's own green-thread mechanism is
one-shot (§5). Multi-shot is only ever about DST *forking*, and that's copy-able and Q22/Q27-gated.
*Falsified if:* a concurrency (not model-checking) construct is found that *requires* resuming one
continuation twice — none in OCaml-5-class evidence.

**G6 · Is DST-replay a default or an opt-in?**
*Default:* **Default** — the seeded `Choice` handler is replayable by construction; production
nondeterminism is the *opt-in* (swap to the wasm scheduler). This is bang's headline
differentiator and it's *already demonstrated* (§4). *Falsified if:* the shared-heap-threads path
(b) becomes default, which trades replay away — a reason to keep (b) non-default.

**G7 · Does `!` (actor-send) bind to the component ABI or to the in-process scheduler?**
*Default:* **Both, at different boundaries** — `!` to an in-process actor is a `send` op the
scheduler handler resolves; `!` across a *component* boundary lowers to a canonical-ABI call
(copy-crossing). Same surface, two handler backends (the §2c unification applied to `!`).
*Falsified if:* the two semantics can't share a surface (e.g. copy-vs-reference makes them
observably different in a way the type can't hide) — plausible; worth grilling.

**G8 · Do we target WASI-0.3 async as the production concurrency backend NOW-ish?**
*Default:* **Yes, as the cooperative-scheduler backend** — it's shipped (2026-06-11), it's the
handler shape bang already has, and it needs no stack-switching. *Falsified if:* the WASI-0.3
async ABI (task/subtask/stream/future) doesn't compose with bang's effect-row lowering — needs a
spike; the async ABI is new and its fit to graded-CBPV lowering is *unverified*.

## §7 · Proposed OPEN_QUESTIONS entries (framed, NOT filed)

- **Q(conc-1) — Component instantiation cost as a spawn primitive.** Is component instantiation
  cheap enough (µs) to back fine-grained actors, or only coarse isolation? Measure on wasmtime 43+.
  Blocks G2. *No 2026 source quantifies this — the survey's biggest evidence gap.*
- **Q(conc-2) — The `conc`/`Sched` row label + scheduler-handler surface.** Pin the effect signature
  (`spawn`/`yield`/`await`/`send`) and its relation to the existing `Choice` effect. Depends on
  Stage-7 handler surface (Q38).
- **Q(conc-3) — WASI-0.3 async ABI ↔ graded-CBPV lowering.** Does `async func`/`stream<T>`/`future<T>`
  compose with the ADR-0059 grade-directed lowering? Spike required. Blocks G8.
- **Q(conc-4) — `!` across the component boundary vs in-process.** Copy-crossing vs reference — can
  one surface `!` cover both without an observable semantic split? Blocks G7.
- **Q(conc-5) — Shared-heap STM substrate watch.** Track shared-everything-threads (Phase 1) +
  shared GC structs; the privileged-STM form (ADR-0030) can't ship before its substrate. Reframe
  the invariant-#3 debt against a moving proposal.

## §G2-MEASURED — component instantiation cost + canonical-ABI copy tax (2026-07-11)

Issue #116. The §G2 deferral rested on two *unverified* numbers; this section
supplies them. Measured on **wasmtime 45.0.0** (CLI round-trip) / **wasmtime crate
34.0.2** (the timing driver, Cranelift, component-model + WasmGC on); components built
with **wasm-tools 1.249.0**; single machine (workstation, x86-64, Linux 6.18). The
engine is built once and each component compiled once — the driver times only
`Instance::new` / a single component call, so process + JIT startup do not pollute
the µs figures. Re-runnable: `tools/bench/g2-components/run.sh`.

**(1) Instantiation cost** — warm µs/instance (a fresh `Store` per iteration = the
honest "spawn a new instance" cost), N=10 000:

| allocator | trivial component | stateful (mem + table + global) |
|---|---|---|
| default (mmap/instance) | ~0.7 µs | ~9 µs |
| pooling (pre-reserved slots) | ~1 µs | ~2–3 µs |

Cold (first) instantiation: 8–26 µs. All figures are **single-digit-to-low-tens µs** —
3–5 orders of magnitude below a millisecond. Instantiation is *not* a ms-scale
deployment cost; it is green-thread-plausible. The pooling allocator (the config a
spawn-primitive would actually use) makes the stateful case ~3× cheaper by reusing
memory mappings.

**(2) Canonical-ABI copy tax** — µs/call, callee re-compiled once, N≥3 000:

| payload crossing the boundary | µs/call |
|---|---|
| empty (floor: `func() -> u32`) | ~0.15 µs |
| small flat message (`tuple<u32,u32>`, by-value) | ~0.20 µs |
| `list<u32>` copy-in only (callee returns len), n=1 000 | ~4–6 µs |
| `list<u32>` copy-in only, n=100 000 | ~400–420 µs |

The copy-in is a **linear ~4 ns/element** memcpy-class cost (confirmed two ways:
copy-only scales 4–6 µs → ~420 µs across 1k→100k; and `copy+sum` minus a `no-cross`
baseline — same sum with the list built *inside* the callee, no boundary — leaves a
~3.8 ns/element boundary-attributable delta). Correctness was checked every run
(`sum[0..1000)=499500`, `sum[0..100000) mod 2³²=704982704`).

**Verdict: the G2 deferral STANDS, and is now quantified rather than asserted.**
- Instantiation being **µs-cheap does *not* by itself make components the spawn
  primitive** — it clears the *first* gate (G2's "cheap enough (µs)") but the copy
  tax gate is the deciding one.
- A component boundary is **free for small flat messages** (~0.2 µs, at the floor)
  but pays a **linear per-element tax on collection/GC-heap payloads** (~4 ns/elem;
  ~0.4 ms for a 100k-element list). This is exactly the shared-nothing,
  copy-crossing cost model the survey assumed [why-cm]. So the boundary is the right
  shape for a *coarse actor / distribution / isolation* seam (small messages, or
  amortized bulk transfers) and the *wrong* shape for fine-grained in-process spawn
  that shares large mutable GC structure — which is precisely why the in-process
  cooperative scheduler (seat a, §1.2) stays the default concurrency primitive and
  `!`-across-a-component-boundary (G7) lowers to this copy-crossing call.

**Caveats / what was NOT measured.** Single machine, no cross-run statistics beyond
2–3 repeats (the claim is orders-of-magnitude, not benchmarketing). The list payload
is `u32` (4 B/elem); a `list<record>` or `list<string>` pays more per element
(pointer-chasing + nested realloc) — the ~4 ns/elem floor is a *lower* bound on real
GC-value crossings. **The component-model async lift/lower** (WASI-0.3 `async func` /
`stream<T>` / `future<T>`, G8) was **not** measured — those add task/subtask
bookkeeping and backpressure on top of the raw copy, and their fit to graded-CBPV
lowering is still the Q(conc-3) spike. Hand-written WAT `record` lift did not validate
on this toolchain (wasm-tools 1.249 quirk); `tuple<u32,u32>` is the ABI-identical flat
proxy used for the small-message row.

## Citations

**bang-side** (ADR/note): ADR-0007 (force explicit; `!` = actor-send) · ADR-0016/0059 (two-hop arch;
Wasm 3.0 backend, grade-directed lowering) · ADR-0030 (STM = transactional handler; privilege =
concurrency-only) · invariants #2 (rows are sets), #3 (STM privilege), #5 (five primitives) ·
`ndet-dst-design.md` (`Choice` effect, seeded stateless-split replay) · `distributed-story.md`
(scheduler-as-handler, DST, CRDT/CALM ladder, replicated-KV demos) · `calm-as-grade-survey.md`
(`coord` label; grading-the-row rejected; `lat` SPU) · `os-inspiration-survey.md` (row-attenuation =
pledge-as-a-type) · `memory-management-survey.md` (WasmGC frame-chain = resumption; v1 = abort→exn +
tail→call; WasmFX = post-std fast-path; U grade 0/1/ω; closures = only heap escapers) ·
`multishot-survey.md` (one-shot sufficiency; OCaml-5 precedent; Q22/Q27; hybrid endgame).

**wasm-side** (all web-verified 2026-07):
- [BA-WASI03] Bytecode Alliance, "WASI 0.3 Launched" — https://bytecodealliance.org/articles/WASI-0.3
- [wasi-roadmap] WASI.dev Roadmap — https://wasi.dev/roadmap
- [techbytes-wasi03] "WASI 0.3 and Beyond [2026]" — https://techbytes.app/posts/wasi-0-3-and-beyond-webassembly-interfaces-2026/
- [wasm-finished] WebAssembly finished-proposals (spec 3.0) — https://github.com/WebAssembly/proposals/blob/main/finished-proposals.md
- [wasm-inprog] WebAssembly proposals (phase table) — https://github.com/WebAssembly/proposals
- [ss-explainer] Stack-switching Explainer (one-shot destructive semantics) — https://github.com/WebAssembly/stack-switching/blob/main/proposals/stack-switching/Explainer.md
- [wasmfx] WasmFX — http://wasmfx.dev/
- [set-overview] Shared-everything-threads Overview — https://github.com/WebAssembly/shared-everything-threads/blob/main/proposals/shared-everything-threads/Overview.md
- [why-cm] "Why the Component Model?" (shared-nothing, copy-crossing) — https://component-model.bytecodealliance.org/design/why-component-model.html
- [ss-linking] Component-model shared-nothing linking — https://github.com/WebAssembly/component-model/blob/main/design/mvp/Linking.md
- [road-cm10] "The Road to Component Model 1.0" (BA milestone ≠ W3C phase) — https://bytecodealliance.org/articles/the-road-to-component-model-1-0
- [medium-hypercharge] "Why WASI 0.3 and Composable Concurrency" (arbitrary tasks / same instance) — https://medium.com/wasm-radar/hypercharge-through-components-why-wasi-0-3-and-composable-concurrency-are-a-game-changer-0852e673830a
