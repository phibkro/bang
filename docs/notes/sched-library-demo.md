<!-- note-status: active -->
# Scheduler-as-handler, as ordinary library code — the ADR-0101 flagship demo

> Lane **sched-demo** (task #139, H2, 2026-07-12). ADR-0101 ratified the DIRECTION
> (concurrency is a row label, a scheduler is a handler) as post-v1/spike-gated;
> nothing in v1 scope changed as a result. This note builds the ONE piece of that
> direction that *is* v1-expressible today: a cooperative round-robin scheduler,
> written entirely as `.bang` library code over the existing sim runtime — no
> `Bang/**`/`Main.lean` change, by design. That "by design" is the thesis on
> display: bang does not need a concurrency-shaped LANGUAGE FEATURE to demonstrate
> "runtimes are values" on the concurrency axis; it needs a `data` declaration, an
> `effect` declaration, and a recursive driver — all ordinary v1 surface.

---

## 0 · TL;DR

```
what shipped     : examples/sched-roundrobin, examples/sched-swap-dfs,
                    examples/sched-seeded-lcg — three corpus-enrolled whole programs,
                    all green in `just verify`. Sched.bang (a plain module file, NOT
                    a bundled std/ module — see §2) declares `spawn`/`next`; Task.bang
                    encodes a "task" as a Step coroutine (data, not a continuation).
the headline demo : the SAME driver body, byte-identical, under THREE different
                    installed Sched handlers, produces THREE different — but each
                    fully deterministic — interleavings:
                      round-robin : 123123123
                      depth-first : 111222333
                      seeded LCG  : 221131233  (replays bit-for-bit every run)
                    One clause in a `with … as sched { … }` block changed each time.
                    Nothing else did. ADR-0101 §G1 ("scheduler-as-handler") shown as
                    a runnable diff, not asserted in prose.
what needed NOTHING
from the compiler : the whole demo is `effect`/`data`/`handle…with`/`let rec` — every
                    piece already on `origin/main` before this lane started. This
                    note required ZERO edits to Bang/** or Main.lean. That is the
                    strongest form of the ADR-0101 claim: the language didn't need to
                    grow a "concurrency feature" to host a working scheduler.
what waits for
post-v1           : true SUSPEND-AND-RESUME of an in-flight call frame (a captured
                    continuation) — v1 has none (ADR-0025 D1), so "yield" here is
                    STRUCTURAL (a task returns a `More`-wrapped thunk for its next
                    step) rather than a language-level suspension. Also waiting: a
                    handler-carried mutable PRNG register (ADR-0092 D5), and the
                    model-checker's multi-shot exploring handler (Q22/Q27, ADR-0101
                    §G5/G4-consequence). None of these blocked this demo — see §5.
walls hit          : four real surface frictions (§4) worth a future ADR-input pass,
                    plus one GC-EMISSION-path refusal (§6, orthogonal to Sched itself).
```

---

## 1 · The shape: two ordinary declarations, one recursive driver

`examples/sched-roundrobin/Sched.bang` (identical across all three example dirs — a
small, self-contained corpus convention, `examples/json`/`examples/calc`'s style):

```bang
pub effect Sched { spawn : Int -> Int, next : Int -> Int }
```

Two ops. `spawn` registers a task and echoes back a caller-chosen id (§5.2 explains
why the id can't be allocated INSIDE the handler in v1). `next` is the entire
scheduling policy surface: the driver calls `sched.next(round)` once per round with a
plain round COUNTER, and the handler decides which runnable task index goes next. That
one op is the whole "scheduler" — everything else is ordinary recursion.

`examples/sched-roundrobin/Task.bang`:

```bang
pub data Step = Fin(Unit) | More((Unit -> Step ! {Div}))

pub let rec makeTask : Int -> Int -> Step ! {Div} =
  fun tid => fun stepsLeft =>
    if stepsLeft == 0 then Fin(())
    else More(({fun u => ($makeTask) tid (stepsLeft - 1)} : Thunk (Unit -> Step ! {Div})))
```

A "task" is a value of type `Step`: either `Fin` (done) or `More(k)`, where `k` is a
THUNK for the task's next step. Forcing and calling `k` runs the task forward by
exactly one step and returns its new `Step` — cooperative by CONSTRUCTION, since the
only way to make progress is for something outside the task (the driver) to call `k`.

`examples/sched-roundrobin/main.bang`'s `drive` function is the scheduler's
INTERPRETER LOOP: it holds three `(taskId, Step)` slots, and each round either
advances the only runnable slot (no choice needed) or asks `sched.next(round)` when
two-or-three slots are runnable, appending the chosen task's id to a base-10
accumulator. **The accumulator IS the interleaving trace** — the program's numeric
output literally spells out which task ran in which order, which is what makes three
different `Sched` handlers over the same driver produce three visibly different,
independently-verifiable outputs.

---

## 2 · Why a plain module file, not a bundled `std/` module

`std/Io.bang` (ADR-0104) is served by a **hardcoded lookup table baked into
`Main.lean`**:

```lean
def stdModules : List (String × String) := [("Io", include_str "std/Io.bang")]
```

Adding `("Sched", include_str "std/Sched.bang")` there is a `Main.lean` edit — exactly
the change this lane's write scope forbids ("if the demo needs a compiler change,
STOP and report; the whole point is that it doesn't"). It genuinely doesn't need one:
bang's **ordinary same-dir-then-root file import** (`resolveModulePath`, ADR-0093 D1)
already resolves `import Sched` to a sibling `Sched.bang` with zero driver
involvement — exactly the mechanism `examples/json` (`Json.bang`/`Parse.bang`/
`Print.bang`) and `examples/calc` (`Ast.bang`/`Lexer.bang`/…) already use for
multi-file example projects. So `Sched.bang`/`Task.bang` live as **plain sibling
`.bang` files inside each `examples/sched-*/` directory** (duplicated per directory,
matching the self-contained-example-directory convention every multi-file corpus
entry already follows), not as a bundled `std/` name.

This is itself a small piece of evidence for the ADR-0101 thesis: `Console`/`Clock`
needed the `std/` bundling machinery because they cross the HOST boundary (a program
must `import Io` to acquire a capability that isn't ambient, ADR-0104's
least-authority argument) — that machinery exists for the *authority* story, not
because effects-in-general need compiler support. `Sched` is a *pure* library effect
(no host boundary, no `--allow` grant, no `Main.lean` driver arm) and needed nothing
beyond the plain module system every multi-file bang program already has.

---

## 3 · The handler-swap beat, as a diff

`examples/sched-swap-dfs/main.bang` is `examples/sched-roundrobin/main.bang` with
ONE clause changed:

```
                     sched-roundrobin/              sched-swap-dfs/
next clause:         round - (round / 3) * 3        0
policy:              round-robin (round mod 3)       depth-first / run-to-completion
output:              123123123                       111222333
```

`examples/sched-seeded-lcg/main.bang` swaps in a THIRD handler — the same driver,
whose `next` clause resolves each pick from a precomputed seeded-LCG table (§5.2
explains the precomputation) — producing `221131233`, a pseudo-random-looking trace
that nonetheless **replays byte-for-byte on every run** (verified: ran the compiled
binary twice, identical output both times). This is `ndet-dst-design.md`'s
"deterministic replay is a handler, not a runtime mode" thesis, now demonstrated on a
genuine cooperative-task interleaving rather than a single delivery-order coin
(`examples/dst-rounds-lcg`'s prior demonstration) — the *scheduler itself* is the
seeded component, exactly as ADR-0101 §G6 names it.

Three handlers, one driver, three genuinely different (verified pairwise-distinct)
interleavings. Nothing about `drive`'s control flow, the task set, or the effect row
changed between any of the three programs — only the value installed at the `with`
site.

---

## 4 · Surface frictions hit while building this (worth a future ADR-input pass)

None of these blocked the demo — each was worked around inside v1 — but each cost
real time bisecting, and future consumers of `handle`/`data`/module-import will hit
the same walls. Named here so this note earns its "what waits" section honestly
rather than silently.

```
# friction                              symptom                        workaround used
────────────────────────────────────────────────────────────────────────────────────────
1 function-typed data-ctor fields       `data Step = More(Unit -> Step)`  declare the field's
  need an EXPLICIT row annotation       silently types the field PURE    row directly in the
  (no inference from a Thunk           ({}), so a Div-performing thunk   ctor decl:
  ascription on the constructed         payload hits "effect row         `More((Unit -> Step
  value)                                mismatch" — the ascription       ! {Div}))`. §Task.bang.
                                        `(… : Thunk (T ! {Div}))` on the
                                        VALUE passed to `More(…)` is
                                        NOT enough; the field's OWN
                                        declared type must carry the row.
────────────────────────────────────────────────────────────────────────────────────────
2 `match (f x) { … }` — a match on an   parse error: expected '{', got   bind the scrutinee to
  INLINE APPLICATION scrutinee —        '(' (the applied-call form       a name first:
  does not parse                        confuses the match/app Pratt    `let r = ($k) () in
                                        interaction, cf. the #26-class   match r { … }`
                                        "operation feeds pOp" lesson in
                                        CLAUDE.md, but for match+app
                                        rather than binop+app)
────────────────────────────────────────────────────────────────────────────────────────
3 an `if`/`match` ARM whose body is a   parse error: expected an         wrap the branch body
  `let`-chain needs explicit parens     identifier, got keyword 'let'    in parens: `if c then
  around the branch — bare `let` as    (a bare `let` head is not a      (let x = … in …) else
  the FIRST token of a then/else/arm    legal branch-body start token)  …`. Every corpus example
  body does not parse                                                   that needed a multi-step
                                                                         branch already avoids
                                                                         this by pulling the
                                                                         logic into a PRECEDING
                                                                         `let` (ndet-sim-kv-a's
                                                                         style) rather than
                                                                         nesting — this demo's
                                                                         driver genuinely needs
                                                                         nested branches (the
                                                                         match/if tree per round),
                                                                         so it hit the case the
                                                                         corpus had quietly never
                                                                         exercised.
────────────────────────────────────────────────────────────────────────────────────────
4 imported names need TWO DIFFERENT     `unbound variable sched`         effect ops: reference the
  qualification conventions depending   (effect referenced bare)  /     TYPE/effect as `Mod_Name`
  on what's being referenced (effect    silently works OR needs         (`with Sched_Sched as
  labels vs. functions vs. types)      `Mod.name` depending on          sched`, `! {Sched_Sched}`
                                        position                        in a row); functions:
                                                                        `Mod.name` (`$(Task.
                                                                        makeTask)`); this matches
                                                                        the pre-existing memory
                                                                        note "imported-effect
                                                                        names need Mod_Eff
                                                                        everywhere" — confirmed,
                                                                        not new, but this demo is
                                                                        a second independent
                                                                        confirmation.
```

None of these are Sched-specific; #1–#3 are general surface gaps a future
non-scheduler consumer (e.g. any program encoding a coroutine/generator/lazy-list as
a `data` type with a function-typed field) will hit identically. #4 is already a
named memory/finding elsewhere.

---

## 5 · Design decisions made WITHIN the v1 wall (and why they're honest, not hacks)

### 5.1 Why `Step` (data), not a captured continuation

ADR-0025 D1: v1 has no reified continuations; `handle` clauses are implicit
tail-resume only (ADR-0095 D5). A "real" coroutine wants to suspend an IN-FLIGHT call
frame and resume it later at the exact suspension point — that needs a first-class
continuation value, which the surface doesn't have. `Step` sidesteps this entirely:
there is no suspended frame to resume, because a task never actually blocks
mid-computation. Instead, EVERY yield point is a normal function return whose result
happens to be `More(nextStepThunk)` — the task's "continuation" is just ordinary data
(a thunk), constructed and returned like any other value. This is the same idiom
functional coroutine libraries in continuation-less languages use (a "step function"
/ "trampoline" encoding) — not a bang-specific workaround, a standard technique this
demo confirms composes cleanly with bang's effect rows and handlers.

**What this buys, and what it costs, honestly:** it buys everything THIS demo needs
(cooperative interleaving, cheap to reason about, no kernel change). It does NOT buy
suspend-in-the-MIDDLE-of-an-expression semantics — a task can only yield at points its
OWN code chose to return `More` from, which is exactly the granularity real
cooperative schedulers (green threads, `async`/`await`) also expose to the
programmer (you don't yield mid-expression there either; you yield at an `await`
point you wrote). So the `Step` encoding is not a lesser demo of the same thing —
it's the *right* granularity for cooperative scheduling, coincidentally also the only
granularity v1 can express.

### 5.2 Why `spawn` echoes an id instead of allocating one

A "real" spawn primitive would have the handler mint a fresh id (a monotonic counter
in handler-carried state) and return it. v1 handler `param` is **read-only**
(ADR-0092 D5 is the deferred param-UPDATE slice) — a handler clause literally cannot
carry a counter forward across calls. So `spawn(n) => n` (echo) is not a corner cut
for THIS demo; it is the honest v1 ceiling for "a handler mints an id." The design
still earns the name "spawn is an effect" (a resource-limited handler COULD refuse a
spawn — return a sentinel instead of echoing — even though none of these three demos
exercise refusal), which is the property that matters for ADR-0101 §G1's claim.

### 5.3 Why the seeded scheduler precomputes its pick table

§3's `sched-seeded-lcg` wanted `next(round) => (lcgStep (seed + round)) mod 3` —
calling the recursive `Div`-performing `lcgStep` INSIDE the clause body. That hits
the ADR-0095 D4 ret-shape wall: even though simple arithmetic on an ALREADY-COMPUTED
value types today (`examples/dst-rounds-lcg`'s `(s/64) - ((s/64)/2)*2`, and this
demo's own `next(round) => round - (round/3)*3`), CALLING `lcgStep` itself inside the
clause is a compute-then-return body that still needs the general CTR lift
(`ctr-design.md`'s G1). The workaround — precompute the 9-entry pick table OUTSIDE
the handler (via nine ordinary top-level `let`s), close over it, and have the clause
do `if round == k then … else …` dispatch on plain arithmetic — is EXACTLY
`ndet-dst-design.md` §5.1's stateless seed-splitting idiom, extended from "a single
per-round coin" to "a table of them, sized to the driver's known round bound." It's
honest work, not a trick: it's more code than a mutable-PRNG handler would need, and
that ergonomics gap is precisely what `ctr-design.md`'s G1 lift buys back when it
lands (this demo becomes the concrete before/after benchmark, as `dst-rounds-lcg`'s
own README already names for the delivery-order case).

### 5.4 The two independent knobs (a finding, not just a footnote)

The demo surfaces something `ndet-dst-design.md`'s `Choice`-only design didn't need
to distinguish: a cooperative scheduler's observable behavior is determined by BOTH
(a) the Sched handler's `next` policy AND (b) the driver's OWN loop shape (which slots
it tracks, in what order it checks them, how it re-queues). Here (b) is fixed (three
named slots, checked in a fixed a→b→c order) and only (a) varies across the three
demos — but a driver with a genuinely dynamic queue (not this demo's fixed 3 slots)
would let (b) vary too (FIFO vs. LIFO re-queueing, for instance), giving a SECOND axis
of "runtime is a value," independent of the handler. Named as a future extension,
not built here (see §7).

---

## 6 · The emission attempt (bonus leg, honestly reported)

`tools/emit-rung5-effects-diff.sh` auto-discovers every `examples/*/` with an
`expected.txt` and gates it against the WasmGC emission path (rung 5 — effects
compile since ◊5.5). Running it with all three `sched-*` demos present: **all three
REFUSE**, with the SAME diagnostic —

```
LOWER-ERROR: 'drive': a use leaves a type variable unresolved — annotate the argument
(e.g. `(drive arg : List Int)`) so ADR-0103's monomorphization pass can close it
```

This is a **frontend lower-error, orthogonal to `Sched` itself** — the same class of
wall `calc`/`json` already hit in the harness's pre-existing `KNOWN_REFUSALS` (a
polymorphic-use monomorphization gap, ADR-0103), not a Sched-effect-specific gap. It
fires on `drive`'s own self-recursive calls (a 9-parameter curried `let rec`, five of
whose arguments are `Step`/`Int` pairs) — plausibly the curried arity or the `Step`
data type's own self-reference interacting with ADR-0103's monomorphization pass, but
this note does NOT diagnose further: a compiler-side fix is out of this lane's write
scope (no `Bang/**` edits). The three refusals are named in
`tools/emit-rung5-effects-diff.sh`'s `KNOWN_REFUSALS` table (matching the harness's
own discipline: an unnamed refusal is a gate failure, a named one is an honest,
tracked wall) — **`tools/emit-rung5-effects-diff.sh` now passes green with these
three additions**, which is the honest bonus-leg result: attempted, hit a real wall,
reported and gated rather than silently skipped or hidden.

---

## 7 · What this demo does NOT claim, and what a future lane could add

```
NOT claimed here:                              future lane (named, not designed):
──────────────────────────────────────────────────────────────────────────────────
a DYNAMIC task queue (spawn growing an          a `data Queue = QNil | QCons(Entry,
  arbitrary-length, runtime-determined            Queue)` driver (spiked in this lane's
  set of tasks) — all three demos fix N=3         scratch work, confirmed to typecheck
  tasks at compile time, matching the             and run — see the scratch12/18 shape)
  corpus's small-hand-verifiable-example          replacing the fixed 3-slot `drive`;
  style (dst-rounds' 16 rounds, gen-seed's        would let a task's OWN step spawn a
  3 picks)                                        NEW task mid-run — a genuine dynamic
                                                   test of "spawn" as a live effect.
a task that spawns OTHER tasks (nested            same Queue extension — a `More` variant
  spawn from inside a running task)                carrying `Spawn(newTask, k)` alongside
                                                   `Fin`/`More`, so the driver's match adds
                                                   a case that both advances the CURRENT
                                                   task and appends to the queue.
the multi-shot exploring/model-checker            genuinely POST-v1 (Q22/Q27,
  handler (fork a run at EVERY `sched.next`,       ADR-0101 §G5/G4-consequence) — needs a
  explore every interleaving via DFS/BFS)          continuation to CLONE, which v1 doesn't
                                                   have. Named, not attempted.
a real `!` (actor-send) between tasks             ADR-0101 §G7 (Sendable fragment) is
  (this demo's "tasks" never communicate,          itself post-v1/unimplemented on the
  they only interleave)                            surface — a future lane pairing this
                                                   scheduler with a landed `!` would be
                                                   the natural next demo.
WASI-0.3 async as a REAL backend (this            named as the first production target
  demo's Sched is the sim/library scheduler        by ADR-0101 §G8, spike-gated MET
  ONLY — no wasm component, no real                (Addendum ①) — a genuinely separate,
  concurrency, no host event loop)                 much larger lane (the WASI-0.3
                                                   lowering, not library-code work).
```

---

## Sources

Local: `docs/decisions/0101-concurrency-model-scheduler-as-handler.md` (the ADR this
demo makes concrete — §G1 model, §G5 one-shot sufficiency, §G6 replay-as-default, §G7
Sendable (not exercised here), Addendum ① the WASI-0.3 spike); `docs/notes/wasm-
concurrency-survey.md` (§the-model, the grill sheet); `docs/notes/actor-sendable-
design.md` (the `!` fragment, not exercised here — no actor-send in this demo);
`docs/notes/ndet-dst-design.md` (§5.1 stateless seed-splitting, the direct precedent
for §5.3's precomputed pick table; §2.2's "the v1 wall" table, the same wall this demo
re-confirms for a 9-round scheduler rather than a 3-pick generator);
`examples/dst-rounds-const`/`dst-rounds-lcg` (the closest structural relative — a
recursive driver performing through a lexically-captured capability, the pattern this
demo's `drive` extends from a fixed 2-arg seed-thread to a 3-task/9-round queue);
`examples/gen-seed-a`/`gen-seed-b` (the minimal `Choice`-handler-swap precedent);
`docs/decisions/0025-...` (D1, no reified continuations — the wall §5.1 designs
around); `docs/decisions/0095-stage7-handler-surface.md` (D4 ret-shape, D5 implicit
tail-resume — the two clause-body constraints this demo's handlers stay inside);
`docs/decisions/0092-...` (D5, param-update deferral — §5.2's spawn-echo rationale);
`docs/decisions/0103-forall-generalization.md` (the monomorphization pass §6's
emission refusal traces back to); `docs/decisions/0104-host-io-environment.md` (the
`std/` bundling machinery §2 explains why this demo does NOT use); `docs/notes/ctr-
design.md` (G1, the compute-then-return lift §5.3's precomputed table works around).
