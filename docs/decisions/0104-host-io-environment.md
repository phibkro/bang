# ADR-0104 · Host IO as effects + handlers, driven by an environment seam with record/replay conformance

<!-- adr-frontmatter -->

- **Status**: Accepted (host-io-wedge lane, 2026-07-11 — Console/Clock wedge landing)
- **Summary**: Host IO (Console, Clock now; Fs, Net later) is an ORDINARY `effect` in the row,
  realized by a swappable handler — the moat thesis ("runtimes are values") on the host axis, adding
  NO kernel primitive (invariants #4/#5 intact). The host effects live in a bundled `std/Io.bang`
  module imported EXPLICITLY (least-authority: `main`'s row is the capability manifest), NOT the
  always-open prelude. The DEFAULT runtime is a pure SIM handler (`--env=sim`, verified-core
  semantics); a `--env=real` + `--allow=<labels>` CLI surface grants the REAL host handler
  deny-by-default (Deno's model, "but in the type system"). The real handler crosses the IO boundary
  so it has NO oracle by construction — its conformance is a RECORD/REPLAY gate: a real run records a
  Sendable `(label,op,payload,result)` trace, and REPLAY runs the same program under a trace-built sim
  handler on the pure oracle; byte-identical output is invariant-#1 compliance for the tested-stratum
  host handler. The pause/resume seam that hands a host perform to the IO shell lives in `Main.lean`'s
  driver, leaving BOTH evaluators (`Source.eval`, `EnvMachine.evalE`) pure. This rules Q(conc-6):
  bang's replay is RECORDED-EFFECTS, not schedule-only. The compiled backend (◊5+) realizes host
  handlers as WASI imports (`--allow` = the component's imported world). It slots alongside ADR-0084's
  slice B (`{Net}` + mock) as the general host-IO frame.
- **Depends-on**: 0084 (IO-as-paradigm; slice-A echo-mock, the mock-now/real-later line), 0092/0095
  (user-effect surface: `effect` decls + handler clauses), 0093 (file-modules; D5 = main's row is the
  capability manifest), 0094 (the env machine = default engine, where the seam sits), 0063
  (escapedCap = the fail-loud terminal the seam narrows), 0101 (G5 one-shot / G7 Sendable / Q(conc-6)),
  0016/0059 (two-hop + Wasm 3.0 backend, the WASI mapping)
- **Relates-to**: `docs/notes/host-io-design.md` (the design survey this ADR ratifies),
  `docs/notes/ndet-dst-design.md` (seeded-sim = replay-by-a-handler, the precedent this generalizes),
  `docs/notes/actor-sendable-design.md` (the Sendable fragment the trace serializes),
  `docs/notes/os-inspiration-survey.md` §1 (row-attenuation = pledge; no ambient authority),
  `std/Io.bang` (the bundled Console/Clock module), `examples/hostio-echo/` (the sim-corpus demonstrator),
  `tools/test-hostio.sh` (the record/replay battery gate)

- **Layer**: R (runtime / tooling — where host IO enters: the driver + the grant surface, not the kernel)
- **Date**: 2026-07-11

## Status

Accepted on landing (host-io-wedge lane, 2026-07-11), Console/Clock wedge. The DIRECTION (host IO as
effects + handlers, record/replay conformance, the least-authority module + grant surface) is ratified;
the v1 IMPLEMENTATION is the Console/Clock wedge — `Fs` read-only and `Net` are named-but-deferred
(§Scope). Nothing in the kernel or `Spec.lean` changes (invariants #4/#5).

## Context

Programs need filesystem/network/ambient IO. The moat thesis (ADR-0084) already answers HOW in
principle — IO is a paradigm-as-library, an ordinary effect realized by a handler — and three prior
pieces de-risk it: user-defined effects (ADR-0092/0095, LANDED), the seeded-sim replay-by-a-handler
precedent (ndet-dst, PASSING), and the file-module capability-manifest (ADR-0093 D5). What was genuinely
new: (1) the pause/resume seam that lets a pure evaluator hand a host perform to the IO shell and take
back a result, and (2) the trace-replay conformance gate that gives the oracle-less host handler an
oracle. `docs/notes/host-io-design.md` surveyed both; this ADR ratifies its rulings.

## Decision

### 1. Host effects live in a bundled `std/Io.bang`, imported explicitly — least-authority

The host effects are plain `pub effect` decls in a NEW `std/Io.bang` module, `include_str`-baked into
the binary (matching `Prelude.bang`'s convention) and served as a SECOND module search root ahead of
the filesystem probe. v1 wedge:

```
pub effect Console { print : Str -> Unit, readLine : Unit -> Str }
pub effect Clock   { now : Unit -> Int }
```

A program must `import Io` to name these — so its `main` row is the capability manifest (ADR-0093 D5):
a reader sees `{Console, Clock}` and knows exactly which host surface the program may touch. This is the
opposite of ambient authority (os-inspiration §1): host IO is NOT in the always-open prelude, so a
dependency cannot quietly acquire it — the acquisition would change its signature and every caller's row.

Separate labels per effect (NOT one monolithic `effect IO {…}`): each label is a separately-grantable
capability (row-attenuation). Payloads are Sendable (`Str`/`Int`/`Unit`) — critical because the trace
(§3) serializes only Sendable values, and an op carrying a thunk/cap would be an escape channel out of
the handler.

### 2. The grant surface — `--env` + `--allow`, deny-by-default (Deno's model, in the type system)

```
bang run prog.bang                                 -- no host env: a host perform ⇒ escapedCap (today)
bang run --env=sim  prog.bang                       -- the SIM environment: pure, deterministic (the DEFAULT for tests)
bang run --env=real prog.bang                       -- grant ALL host labels the real handler
bang run --env=real --allow=Console,Clock prog.bang -- grant a SUBSET (the pledge surface)
```

`--allow` is row-attenuation as a CLI flag: a label not in `--allow` gets no host handler, so a perform
on it hits `escapedCap` (fail-loud, ADR-0063). The DRIVER resolves the `--allow` NAMES to their
allocated labels via the merged program's effect table (labels are `4 + effect-decl-index`, decl-order,
NOT fixed — so the resolution is by name, not a hardcoded `Nat`). Because the checker knows `main`'s row,
an under-granting `--allow` can be a STATIC refusal, not a runtime escape. The structural contrast with
Deno (which enforces at runtime by intercepting syscalls, discovering requirements by running): bang's
row makes the requirement STATIC — the type declares what a program may perform, checked before it runs,
and the grant is the handler installation. "Deno's permissions, but in the type system."

### 3. The conformance gate — record/replay is the tested-stratum host handler's oracle

Invariant #1: proof rides the reference; anything that runs is diff-tested against the oracle. The host
handler runs real IO — no oracle BY CONSTRUCTION. Record/replay is how it gets one:

```
RECORD (real run, --env=real)              REPLAY (--env=sim, PURE Source.eval oracle)
──────────────────────────────            ───────────────────────────────────────────
the driver logs each satisfied host        feed the trace to a SIM handler whose clause for
perform as an ordered row                  (ℓ,op) yields the next recorded result; run the
  ⟨label, op, payload, result⟩             SAME program under Source.eval. output == the
→ a Sendable ndJSON trace                  recorded run ⇒ CONFORMS (invariant #1 met for IO).
```

This is the ndet-dst move generalized: `Choice`'s seed is one `pick`; the IO trace is the host's whole
answer-sequence, and the sim handler is an ordinary bang handler whose equality check runs under the
VERIFIED `Source.eval`. All four trace fields are Sendable (⇒ `Val.Closed` ⇒ serializable); a
non-Sendable field would have no faithful serialization and break replay.

**Q(conc-6) ruling — recorded-effects.** ADR-0101 G6 asked: is bang's replay schedule-only or
recorded-effects? For IO: recorded-effects. The trace captures the host's RESULTS, not just scheduler
picks, so replay reproduces the run despite a nondeterministic host. Schedule-only (ADR-0101's v1 sim,
no real IO) is the empty-trace special case; with concurrency + real IO the full trace is schedule picks
interleaved with host results — one ordered log pinning both nondeterminisms.

**Honest limits.** Replay reproduces a run only for the host answers the trace recorded: it does not
predict a FUTURE run (tomorrow's `Clock.now` differs), and it checks the PROGRAM's observable output,
not the world's (a `writeFile`'s bytes are not re-emitted). The gate is "did this recorded run match the
pure model," not "will every run."

### 4. The seam — a `Main.lean` driver over a pure evaluator sibling (the replay-prefix)

The host boundary CANNOT live in `Source.eval` or `evalE` — both are pure Lean with no `IO`, and
poisoning them with `IO` would destroy the "prover interpreting the object language" property (the
stratification principle) and `#guard`-testability. The IO monad exists only in `Main.lean`. So the seam
is a DRIVER in `Main.lean` (the only IO site): it runs the pure evaluator, observes an escaped host
perform, does the REAL IO in Lean's `IO` monad, records the `(label, op, payload, result)` row (§3), and
RE-RUNS the pure evaluator with the host answers accumulated so far — the big-step "handler via a growing
response prefix." Each host perform is deterministic given the prefix (the evaluator is a pure function),
so the run advances one host request per re-run until it completes. Both evaluators stay pure (invariants
#4/#5), and — the load-bearing elegance — RECORD and REPLAY are the SAME construct: replay is this exact
driver with the prefix pre-filled from the trace. One-shot suffices (ADR-0101 G5): the driver consumes
the prefix, never re-enters a continuation. The O(#host-performs²) re-eval is bounded by a fail-loud
`--max-host-requests` ceiling (naming the flag, not a silent quadratic).

**The DESIGN-NOTE DEVIATION (recorded here — one decision home).** `host-io-design.md` §2 specified the
seam as a fourth `MOutcome` (`msuspended`) + a `resumeE`/`k'.resume` driver loop. That shape presupposes
a machine with a REIFIED CONTINUATION. Verified from code: the DEFAULT engine (`EnvMachine.evalE`,
ADR-0094) is BIG-STEP — its stack is Lean's call stack, so no continuation object exists to hand a driver
and resume. The note conflated the big-step `evalE` with the CalcVM `exec` (`AbstractMachine.lean`, which
DOES reify `Code`/`Stack` — "the stack IS the continuation" is true THERE). The replay-prefix is the
big-step-faithful realization; `host-io-design.md` §2 carries a correction header pointing here.

**The realization fork trail** (the trail is the value — a future session must not relitigate it):

```
B  · replay-prefix driver, evalE stays pure.  ADOPTED as the mechanism.
   │
   ├─ B1 · thread the response prefix THROUGH evalE (one construct, no sibling).
   │       REFUTED at condition-1's MEASURED re-key: threading `rs` grows evalE's
   │       result tuple, rippling the PROVEN `evalE_agrees_evalD_gen` (ADR-0094)
   │       across 22 destructure + 31 statement sites — a proven-spine re-key, not a
   │       mechanical re-green. (The claim "mechanical" was RETRACTED on this measurement.)
   │
   └─ B2 · a sibling `evalEHost`, evalE BYTE-IDENTICAL + untouched.  ADOPTED.
           Differs from evalE in ONE leaf (the perform host-inject arm). Cost: a
           ~1-leaf-different copy of a 100-line mutual. Mitigated three ways:
             (i)   a CI DRIFT GATE — `#guard`s pinning `evalEHost … [] ≡ evalE …` on the
                   full witness corpus, so an un-mirrored edit turns CI RED (the
                   derivation-ladder "test" rung, standing in where "generate"/one-def is
                   unreachable — unifying needs the very B1 re-key we refuted);
             (ii)  a LOUD edit-both banner on the def;
             (iii) TEMPORARY BY DESIGN — the future door (below) retires it.
```

The B2 sibling keeps the ADR-0094 headline's axioms exactly `{propext, Classical.choice, Quot.sound}`
(re-gated on a force-rebuilt olean). The seam is NARROW: only a perform on a `--allow`-granted host label
that escapes σ→τ→κ is serviced; everything else keeps today's `escapedCap` fail-loud, and a user
`with … as h {…}` still catches its effect lexically.

**Rejected: A (reify `evalE` to CK) / C (move the seam to the CalcVM `exec`).** A rewrites the default
engine to a small-step/CK machine so a continuation can be captured — the largest change, rippling the
proven headline + 28 call sites, and NOT wedge-warranted. C moves the seam to `exec` (whose `OP n op v ::
c` DOES keep the resume continuation `c`) but touches the clean-set spine's axiom gate
(`compile_correct`/`compile_forward_sim`) AND `exec` isn't the default engine, so the user-facing `bang
run` path still wouldn't get host IO without also doing A or B — worst of both. Both are REJECTED, not
refuted-forever: the future door (below) brings the suspendable engine A gestures at, for the RIGHT reason
(concurrency), at which point the replay-prefix is subsumed.

**THE FUTURE DOOR (framed for one-construct honesty over time).** ADR-0101's concurrency substrate will
eventually need a genuinely SUSPENDABLE engine (a scheduler suspends tasks). When it arrives, that engine
SUBSUMES the replay-prefix: a host perform becomes an ordinary task suspension, the re-eval + the sibling
+ this ceiling all retire together. The replay-prefix is the WEDGE-HONEST mechanism, not the forever
mechanism; B2's sibling is explicitly temporary (its banner says so). A future session reading this should
see B as "the right v1 wedge" and A as "deferred to the concurrency era," NOT B as permanent or A as
wrong.

**OPEN — the host-provision reach (the NEXT slice, cross-lane).** The seam services an escaped host
perform, but a normal program installs its OWN `with Io_Console as con {…}`, which catches every Console
op LEXICALLY — so the host seam is the outermost fallback ONLY for a perform NO user handler catches.
Reaching it needs the program to leave the host effect UNHANDLED and the RUNTIME to provide the outer
handler. The v1 surface has no smooth spelling for that (verified: a `perform` needs a bound cap; `Io.print
x` elaborates as a module-qualified private reference, not a perform; `.dotPerform` requires the receiver
resolve to `.cap ℓ`; a cap-param `main` isn't a runnable entry). The chosen reach is **a module-qualified
host perform** (`Io.print x` → a perform on a RUNTIME-minted `Io_Console` cap, reached by the seam) — a
narrow elaboration affordance, deliberately the RUNTIME's own ambient authority (right where the design
REJECTS ambient authority for USER code, os-inspiration §1). That is a surface/elaboration slice
(cross-lane), named here as the NEXT step. Until it lands, the v1 wedge ships the SIM runtime (the program
writes its `with` sim clauses, corpus-green) plus this engine+driver mechanism, READY for the reach.
Rejected for the reach: recording the SIM's own performs (vacuous — a deterministic sim has no host
nondeterminism to pin, so the conformance gate would be toothless).

### 5. The compiled backend — host handlers are WASI imports

The ◊5+ backend (ADR-0059) realizes host handlers as WASI Preview 2 imports; a program's row becomes its
component world (WASI worlds = row-attenuation). `Console` → `wasi:cli/stdout`·`stdin`, `Clock` →
`wasi:clocks/*`, `Fs` → `wasi:filesystem` + preopens (the grant IS the preopen), `Net` →
`wasi:sockets/*` (post-v1). `--allow` maps directly to the preopen/grant model: an ungranted interface is
simply absent from the imported world, so the linker refuses it — attenuation enforced by the platform.
Host ops being one-shot tail-resumptive, a host perform lowers to a DIRECT import call (the cheapest
lowering slot), not general GC-frame resumption.

### 5. The compiled backend — host handlers are WASI imports

The ◊5+ backend (ADR-0059) realizes host handlers as WASI Preview 2 imports; a program's row becomes its
component world (WASI worlds = row-attenuation). `Console` → `wasi:cli/stdout`·`stdin`, `Clock` →
`wasi:clocks/*`, `Fs` → `wasi:filesystem` + preopens (the grant IS the preopen), `Net` →
`wasi:sockets/*` (post-v1). `--allow` maps directly to the preopen/grant model: an ungranted interface is
simply absent from the imported world, so the linker refuses it — attenuation enforced by the platform.
Host ops being one-shot tail-resumptive, a host perform lowers to a DIRECT import call (the cheapest
lowering slot), not general GC-frame resumption.

## Scope (v1 = the Console/Clock wedge)

| tier | effect | v1 status |
|---|---|---|
| **wedge** | `Console` + `Clock` | THIS ADR — no resource handles, pure Sendable ops, host side ~3 lines of Lean IO |
| next | `Rand` | identical shape to `Choice.pick`; reuses the ndet-dst seeded handler as its sim. Free once the wedge lands |
| next | `Fs` read-only | one resource kind (opaque-`Int` handle), fixed-map sim; deferred |
| last | `Net` | ADR-0084 slice B; needs connection handles + (post-v1) `listen`/`accept` = the concurrency substrate |

## Rejected

- **IO in the prelude** — ambient authority; `main`'s row stops being its capability manifest. The
  least-authority discipline (an explicit `import Io`) is the whole point.
- **One monolithic `effect IO {…}`** — collapses the row's census; separate labels are separately
  attenuable capabilities (row-attenuation).
- **FD-as-payload** — leaks a non-Sendable host resource into a value, breaking trace serialization; the
  opaque-`Int` token keeps the Sendable fragment closed.
- **IO inside a monadic `Source.eval` / an FFI table threaded through `evalE`** — both poison the pure
  oracle with `IO`, destroying the stratification principle and `#guard`-testability. The IO lives ONLY
  in `Main.lean`.
- **A pre-collected "IO plan" run after evaluation** — cannot express data dependence (a `readFile`
  whose path came from a prior `readLine`); the suspend/resume driver exists precisely so the
  continuation carries that dependence.
- **Schedule-only replay** — insufficient for a nondeterministic host; the trace must pin the host's
  RESULTS (Q(conc-6) recorded-effects), not just scheduler picks.

## Consequences

- No kernel change (invariant #5 — five primitives) and no `Spec.lean` change (invariant #4 — the
  machine stays calculated). Host IO is entirely elaborator-surface + driver + grant plumbing.
- The sim runtime inherits `Source.eval`'s correctness; the real host handler is tested-stratum by
  construction, its oracle the replay of its own trace (§3). Descent is explicit (`--env=real` marks it).
- `Fs`/`Net`/`Rand` are named-but-deferred with known shapes (§Scope), not design dead ends.
- The WASI mapping (§5) is the compiled backend's free version of the interpreter's seam — flagged for
  ◊5+, not v1 work.

## Revisit if

- Concurrency lands: the trace becomes schedule-picks interleaved with host results (Q(conc-6)'s
  composite artifact); the driver's one-shot resume composes with the scheduler-as-handler (ADR-0101).
- Mutable handler state lands (ADR-0092 D5 param-update): a stateful sim (scripted `readLine` feeding
  successive lines, an in-memory `Fs` map) becomes expressible — the v1 fixed-source sims relax.
- The compiled backend reaches the host rung: §5's WASI-import lowering gets its own spike (ADR-0059's
  tail→direct-call slot), possibly its own ADR if the canonical-ABI payload lowering is non-trivial.
