<!-- note-status: active -->
# Host-IO environment design — filesystem/network/ambient IO as effects + handlers

> Design survey (operator-posed 2026-07-11: "an environment extension to give programs filesystem,
> network and ambient IO access"). Docs-only; feeds an ADR at implementation dispatch, alongside
> ADR-0084 slice B. Half-reserved already: ADR-0084 (IO-as-paradigm, echo-mock = slice A) + #44
> (user-defined effects, LANDED) + ndet-dst (seeded-sim = replay-by-a-handler, PASSING) leave three
> genuinely new pieces: the pause/resume seam, the trace-replay gate, the WASI mapping.

## 0 · TL;DR

```
the thesis         : IO is a paradigm-as-library — an ordinary `effect Fs {…}` in the row,
                     realized by a swappable handler. Nothing kernel-new. (ADR-0084, moat)
the ONE new seam   : a HOST FRAME in the ENV machine (NOT Source.eval) suspends on a
                     perform at a host label, hands (label,op,payload,resume) to Main.lean,
                     which does the real IO in Lean's IO monad and resumes. One-shot (G5).
the conformance    : every real run RECORDS a Sendable trace of (label,op,payload,result); the
gate               : trace REPLAYS as a pure sim handler under Source.eval (the oracle). Replay
                     reproduces the run ⇒ invariant #1 met for IO — the tested-stratum diff test.
Q(conc-6) ANSWER   : bang's replay guarantee is RECORDED-EFFECTS, not schedule-only. The
                     trace pins exactly the host nondeterminism the sim can't reproduce.
the v1 wedge       : Console (print/readLine) + Clock (now) — two ops, no resource handles,
                     Sendable payloads. Fs read-only next; Net last (ADR-0084 slice B).
static residue     : Lean upstream has NO musl/static target (#2931 closed not-planned);
                     the real static story is compiled-wasm output (a WASI component).
```

## 1 · The effect interfaces (where they live, op signatures, the v1 slice)

**Recommendation.** Host effects are ordinary `effect` decls (ADR-0092 surface, LANDED) in a **new
`std/Io.bang` module** imported explicitly (ADR-0093 file-modules), NOT the always-open `Prelude.bang`.
Rationale: the prelude is ambient authority — every program would carry `{Fs,Net,…}` in scope for free,
the opposite of least-authority (os-inspiration §1: "no ambient authority"). A program must *import* IO
to name it; its `main` row is then the capability manifest (ADR-0093 D5).

```
std/Io.bang  (each is a plain `effect` decl; ops are single-arg, curried — ADR-0095 D3)
─────────────────────────────────────────────────────────────────────────────────────
effect Console { print : Str -> Unit,  readLine : Unit -> Str }
effect Clock   { now : Unit -> Int }                        -- ms since epoch
effect Rand    { gen : Int -> Int }                         -- SAME shape as Choice.pick
effect Fs      { readFile : Str -> Str,  writeFile : (Str, Str) -> Unit }   -- v1: read only
effect Net     { recv : Handle -> Str,   send : (Handle, Str) -> Unit }     -- ADR-0084 slice B
```

**Payloads are Sendable** (ADR-0101 G7 fragment: `unit`/`int` + sum/prod/μ, no `U`/`arr`/`cap`).
`Str` is `μ`-data (`Prelude.bang`), so Sendable — critical because (a) the trace serializes only
Sendable values (§3), and (b) an op carrying a thunk/cap would be an escape channel out of the handler.
**A resource handle (`Fs.File`, `Net.Conn`) is Sendable-by-encoding**: an opaque `Int` token the *host
handler* maps to a real FD, never the FD itself crossing — the op surface stays first-order.

**Single-arg constraint (v1).** ADR-0095 D3 curries effect ops (`writeFile : (Str,Str)` = a curried
clause; performed `$fs.writeFile path body`). Note the ret-shape wall (ADR-0095 D4): a v1 *sim*
clause body must be `ret w`. Pure-op sims (Clock replaying a recorded timestamp) are trivially
ret-shape; mutable-state sims (an Fs tracking an in-memory file map) want carried-param UPDATE
(ADR-0092 D5 / ADR-0087 open), so the **v1 sim Fs reads from a fixed map** — the ndet-dst §5
"honest v1 within the wall" discipline.

**The v1 slice (sized).**

| tier | effect | why this order | cost |
|---|---|---|---|
| **wedge** | `Console` + `Clock` | no resource handles, pure Sendable ops, host side is 3 lines of Lean IO (`IO.println`/`(← IO.monoMsNow)`); Clock is the canonical "same program, different answer per run" — its trace is one `Int` | S |
| next | `Rand` | *identical shape to `Choice.pick`* — reuses the ndet-dst seeded handler as its SIM; the host handler is `IO.rand`. Free once the wedge lands | S |
| next | `Fs` (read+write+exists) | **LANDED (hostio-widen lane, 2026-07-12 — see ADR-0104 §Addendum)**: `readFile`/`writeFile`/`exists`, whole-file (NO handle — the path is the token, so this row's opaque-`Int`-handle framing was unneeded for the whole-file surface); `writeFile : Str * Str -> Unit` is ONE pair-arg (`Io.writeFile((p,b))`, single-arg ops D3); sim = the record/replay TRACE (not a fixed map — a stateful map wants D5); `listDir`/typed-errors deferred | M |
| last | `Net` | ADR-0084 slice B verbatim; needs connection handles + (post-v1) `listen`/`accept` multiplexing = the concurrency substrate (ADR-0030/0101) | L |

**Rejected.** *(a) IO in the prelude* — ambient authority; `main`'s row stops being its manifest.
*(b) One monolithic `effect IO {…}`* — collapses the row's census: separate labels = separately
attenuable capabilities (row-attenuation, os-inspiration §1). *(c) FD-as-payload* — leaks a non-Sendable
host resource into a value; the opaque-`Int` token keeps the fragment closed.

## 2 · The host-handler mechanism — the pause/resume seam in the ENV machine

> **CORRECTION (ADR-0104 supersedes the mechanism below).** This section's `msuspended`-fourth-`MOutcome`
> + `resumeE`/`k'.resume` seam presupposes a machine with a REIFIED CONTINUATION. Verified at
> implementation: the default engine (`EnvMachine.evalE`, ADR-0094) is BIG-STEP — its stack is Lean's call
> stack, so there is no continuation object to hand a driver and resume. "The env machine's stack IS the
> continuation" is true of the CalcVM `exec` (`AbstractMachine.lean`), NOT the big-step `evalE` named here
> — the two got conflated. The realized seam is the **replay-prefix driver** (re-run the pure evaluator
> with the host answers accumulated so far), realized as a byte-identical-except-one-leaf sibling
> `evalEHost` (B2, after B1's proven-spine re-key was refuted). See **ADR-0104 §4** for the mechanism, the
> full fork trail (B/B1/B2), the rejected A/C, the future door (the concurrency-era suspendable engine
> subsumes the replay-prefix), and the **H1 host-provision reach (#126, LANDED)**. The interfaces (§1), grant surface
> (§2a), trace/conformance (§3), and WASI mapping (§4) below stand as designed.

> **H1 STATUS (2026-07-11, hostio-reach lane) — LANDED, with a nearness correction.** A module-qualified
> host perform (`Io.print x`) now elaborates and reaches the driver's grant surface — the `hostPerformS`
> Surf former + its ~18-arm traversal ripple (Surface.lean/TypeCheck.lean/Query.lean/Rewrite.lean/
> Format.lean). Ships LABEL-ONLY AMBIENT dispatch: a lexically-enclosing `with Io_Console` does NOT
> catch the call (measured, refuting this doc's own §2a "nearest handler" framing for the H1 case
> specifically) — the full mechanism-vs-name-lookup analysis, the `#guard` gap it surfaces, and the
> named H1b follow-up (lexical nearness, a deferred design pass) live in **ADR-0104 §4** (the
> authoritative correction; do not duplicate the analysis here). `examples/hostio-echo/ambient.bang` +
> `tools/test-hostio-seam.sh` §6 demonstrate the shipped semantics end-to-end against real IO.

**The load-bearing constraint (verified from code):** the host boundary CANNOT live in `Source.eval`.
`Source.eval` (`Eval.lean`, the kernel oracle) is pure Lean, no `IO`; the env machine (`EnvMachine.lean`,
ADR-0094, default engine) is *also* pure — `evalE : … → Option (MOutcome × …)`. The IO monad exists
only in `Main.lean`, which calls `runComp`/`runEnv` then `IO.println`s the *returned pure value*.
Today a `perform (vcap n ℓ)` dispatches by identity `n` through σ→τ→κ (EnvMachine.lean:235); a host
label reaches NO frame → `escapedCap` (fail-loud, ADR-0063, Eval.lean:226). **The seam turns that
specific escape into a suspension.**

**Recommendation — the pause/resume shape:** add a fourth `MOutcome` alongside `mterm`/`mraised`:

```
inductive MOutcome
  | mterm   : MTerm → MOutcome                       -- ret / lam  (today)
  | mraised : Nat → OpId → MVal → MOutcome            -- an unhandled raise (today)
  | msuspended : HostReq → MContinuation → MOutcome   -- NEW: a host perform reached the top
```

where `HostReq = (Label × OpId × MVal)` is a Sendable request and `MContinuation` is the suspended
machine state (the `evalE` stack/env at the perform focus — the env machine's stack IS the
continuation). `evalE`'s perform arm gains one case: *if `ℓ` is a designated host label AND σ→τ→κ
finds no frame, return `msuspended (ℓ,op,arg) k` instead of `none`→escapedCap.*

**The driver loop moves to `Main.lean` (the only IO site):**

```
partial def runWithEnv (env : HostEnv) : MContinuation → IO Result
  | k => match resumeE k with
    | .mterm (.mret v)        => pure (.done v)              -- program finished
    | .msuspended (ℓ,op,arg) k' =>
        let result ← env.perform ℓ op arg                    -- the REAL IO, in Lean's IO monad
        recorder.log ⟨ℓ, op, arg, result⟩                    -- §3: append to the trace
        runWithEnv env (k'.resume result)                    -- one-shot RESUME with the host reply
    | .mraised .. | .mterm _  => pure (.escapedCap /-etc-/)  -- unchanged fail-loud terminals
```

`k'.resume result` is a **one-shot** resume — G5 says that suffices (the machine consumes `k'`, never
re-enters it), matching `dispatchOn`'s existing one-shot tail-resume for custom handlers
(Dispatch.lean:165). No multi-shot machinery, no kernel change: purely env-machine + Main.lean.

**How the CLI grants the environment — least-authority:**

```
bang run prog.bang                    -- NO host env: any host perform ⇒ escapedCap (today's behavior)
bang run --env=sim[:seed] prog.bang   -- the SIM environment: pure, no real IO, deterministic (the DEFAULT for tests)
bang run --env=real prog.bang         -- refused: real mode needs explicit --allow
bang run --env=real --allow=Console,Clock prog.bang   -- named trusted effect grants
bang run --env=real --allow=Fs --allow-fs-read ./in --allow-fs-write ./out prog.bang
bang run --env=real --allow=all prog.bang             -- explicit built-in + unrestricted-Fs grant
```

`--allow` is row attenuation as a CLI flag (os-inspiration §1: "pledge-as-a-type"). #169 makes
real/record default-deny, reserves exact `all` as the only grant-all spelling, and separates trusted
service recognition from authorization so an omitted label gets a precise pre-IO diagnostic. Fs
adds an independent host-resource intersection: repeatable read roots cover `readFile`/`exists` and
write roots cover `writeFile`. Replay consumes its trace purely and rejects authority flags. The
resolver, not an effect-name heuristic in the service, identifies declarations originating in the
bundled `Io` module before module flattening erases provenance.

**escapedCap interaction.** `escapedCap` stays the terminal for a genuinely-unhandled label. The
seam is *narrow*: only a perform on a CLI-designated host label that also escapes σ→τ→κ suspends;
everything else keeps today's fail-loud semantics. A user `with Net as h {…}` catches a perform
performed ON `h` (`h.op(…)`, the ordinary `.dotPerform` cap-threading spelling) lexically — the host
frame is the *outermost* fallback, reached only when no user handler does. **[H1 scope note, ADR-0104
§4: this sentence describes the pre-existing `.dotPerform`/named-cap path, UNCHANGED by H1. It does
NOT extend to the NEW module-qualified AMBIENT spelling (`Io.print` with no receiver) — that path
reaches the driver unconditionally regardless of an enclosing `with`, measured and corrected in the
ADR; see the H1 STATUS note above.]**

**Rejected.** *(a) IO inside a monadic `Source.eval`* / *(b) an FFI table threaded through `evalE`* —
both poison the pure oracle with `IO`, destroying the "prover interpreting the object language"
property (the stratification principle) and `#guard`-testability. *(c) A pre-collected "IO plan" run
after evaluation* — cannot express data dependence (a `readFile` whose path came from a prior
`readLine`); suspend/resume exists precisely so the continuation carries that dependence.

### 2a · The Deno prior art (operator-named; the grant surface's reference model)

Deno's permission model is the named inspiration for the grant surface, and the census it
validated: developers WANT deny-by-default with explicit, fine-grained allows. The mapping:

| Deno | bang | note |
|---|---|---|
| deny-by-default | the default `--env=sim` (real IO never ambient) | stronger: sim is a WORKING runtime, not a refusal |
| `--allow-net=host:port` | `--allow=Net` (+ per-resource scoping in the GRANT, host-side) | per-resource stays grant-side policy in v1 — the ROW tracks the effect, the grant scopes the resource; pushing paths/hosts into the type is deliberately out of scope |
| `--allow-read` / `--allow-write` | `--allow=Fs` ∩ `--allow-fs-read ROOT` / `--allow-fs-write ROOT` | effect authority and physical directory-root authority are explicit independent axes |
| prompt-on-first-use | NOT adopted for v1 | the CLI is agent-driven/non-interactive-first; a prompt mode can arrive with a TTY check later |
| `Deno.permissions` (runtime query) | `bang query effects <fn>` | EXISTS TODAY — and it's static: the answer comes from the type, not from probing the runtime |

**The structural contrast (copy-kit material):** Deno enforces permissions at RUNTIME by
intercepting syscalls — the program's requirements are discovered by running it. bang's effect
row makes the requirement STATIC: the type declares what the program may perform, checked before
it runs, and the grant is the handler installation. A dependency cannot quietly acquire network
access — the acquisition would change its SIGNATURE and every caller's row with it (effect creep
is diff-visible via `bang rewrite annotate`). "Deno's permissions, but in the type system."

## 3 · THE CONFORMANCE STORY — record/replay as invariant-#1 compliance (load-bearing)

Invariant #1: *proof rides the reference; anything that runs is diff-tested against the oracle.* The
host handler runs real IO — **no oracle by construction**. Record/replay is how it gets one.

```
RECORD (real run, --env=real)          REPLAY (--env=sim, PURE Source.eval)
──────────────────────────────         ──────────────────────────────────────
run under the host env; the driver     feed the trace to a SIM handler: a plain
loop (§2) logs each satisfied host      user handler whose clause for (ℓ,op) pops
perform as a row:                       the next recorded result for that (ℓ,op).
  ⟨label, op, payload, result⟩          Run the SAME program under Source.eval
→ an ordered trace (JSONL, Sendable     (the oracle, no IO). If replay's output
   values only)                         == the recorded run's output ⇒ CONFORMS.
```

**Why this is exactly the ndet-dst move.** `ndet-dst-design.md` already ships a seeded `Choice`
handler making a "distributed" run replayable with zero real IO — a *different value installed*, not
a replay mode bolted on. The IO trace generalizes the seed: `Choice`'s nondeterminism is one `pick`;
IO's is the *host's answers*, and the trace is the recorded answer sequence. The sim handler is an
ordinary bang handler, and the equality check runs under the **verified** `Source.eval`.

**Trace format decision:** newline-delimited JSON, one row per satisfied host perform, fields
`{label, op, payload, result}` — **all four Sendable** (why §1 insists on Sendable payloads +
opaque-`Int` handles). Sendable ⇒ `Val.Closed` ⇒ serializable by existing `valPretty`/JSON; a
non-Sendable field (thunk, cap) has no faithful serialization and breaks replay. Ordered by
perform-satisfaction within a single-threaded run (concurrency adds the schedule trace — Q(conc-6)).

**Where recording lives:** the `Main.lean` driver loop (§2), NOT the machine — the machine stays
pure; the recorder is an IO sink the loop appends to after each `env.perform`. Replay needs no
machine change: it is the *same `.bang` file* run under a trace-built sim handler on the pure engine.

**Q(conc-6) — the answer this design gives.** ADR-0101 G6 named the open edge: is bang's replay
*schedule-only* or *recorded-effects*? **For IO, recorded-effects.** The trace captures the host's
*results*, not just the scheduler's picks, so replay reproduces the run despite a nondeterministic
host. Schedule-only (ADR-0101's v1 sim, no real IO) is the empty-trace special case. With concurrency
+ real IO, the full trace is *schedule picks interleaved with host results* — one ordered log pinning
both nondeterminisms. This closes Q(conc-6) recorded-effects, naming the composite trace the artifact.

**Honest limits (the trace pins EXACTLY the host nondeterminism).** Replay reproduces a run *only
for the host answers the trace recorded*: it does not predict a *future* run (tomorrow's
`Clock.now` differs — the trace fossilizes one run), and it checks the *program's* observable output,
not the world's (a `writeFile`'s bytes are not re-emitted). A host returning different results for
identical (label,op,payload) between record and replay is exactly what the trace pins — replay uses
the *recorded* result, faithful to *that* run by construction. The gate is "did this recorded run
match the pure model," not "will every run."

## 4 · The wasm/WASI mapping

Compiled programs (the ◊5+ backend, ADR-0059) realize host handlers as **WASI imports**; a program's
row becomes its **component world** (wasm-concurrency-survey §3: WASI worlds = row-attenuation, the
canonical ABI = the perform boundary). §2's suspend/resume seam is the *interpreter's* version of what
the backend gets free: a host `perform` lowers to an **import call**, and the wasm host IS the loop.

```
bang effect (row label)   →  WASI Preview 2 interface (the component's imported world)
─────────────────────────    ────────────────────────────────────────────────────────
Console.print / readLine  →  wasi:cli/stdout · wasi:cli/stdin
Clock.now                 →  wasi:clocks/wall-clock · monotonic-clock
Rand.gen                  →  wasi:random/random
Fs.readFile / writeFile   →  wasi:filesystem/types + preopens (the capability grant IS the preopen)
Net.recv / send           →  wasi:sockets/*  (post-v1; ADR-0084 slice D)
```

The `--allow=Console,Clock` surface (§2) maps *directly* to WASI's preopen/grant model: an ungranted
interface is simply absent from the component's imported world, so the linker refuses it — attenuation
enforced by the platform (os-inspiration §1 "pledge-as-a-type", cashed at the wasm layer).

**What the emission arc needs (rung 5-ish, per `emission-rung1-probe.md`):** the pure-⊥ rung already
emits `.wat` (4/4 == `Source.eval`); the host rung adds *perform-at-host-label → import call* — emit
`call $wasi_import`, payload lowered via the canonical ABI, bind the result. Host ops being one-shot
tail-resumptive (§2), this is a *direct call*, not general GC-frame resumption — the cheapest lowering
slot (ADR-0059: tail→direct-call). WASI-0.3 async is the concurrent-IO target (ADR-0101 G8); v1 host
IO is synchronous, needs only the direct import call.

## 5 · Verification stratification (ADR-0026 ladder terms)

```
level          verified core                 tested superset              seam
──────────────────────────────────────────────────────────────────────────────────────────
IO semantics   the SIM handler + the         the HOST handler (real IO    the TRACE-REPLAY
               trace-replay equality,        in Main.lean's IO monad;     GATE (§3): replay
               run under Source.eval          NO oracle by construction)   under Source.eval
               (the oracle)                                                == the recorded run
```

The sim handler inherits `Source.eval`'s correctness. The host handler is **tested-stratum by
construction**: crossing the IO boundary, it can have no proof; its oracle is *the replay of its own
trace against the pure model*. Descent is explicit (`--env=real` marks it), and the differential test
is the trace-replay gate, not a stubbed green — the trace watches the exact host boundary end-to-end.

## 6 · Static-linking residue (short)

- **Upstream Lean musl/static watch item.** Verified 2026-07-11: **no upstream target, no active
  tracking issue.** The one dedicated request, `leanprover/lean4#2931` ("RFC: release musl binaries"),
  is **CLOSED — not planned** (2024-10-25); the platforms doc lists only glibc/macOS/Windows/wasm (no
  musl/static); elan v4.2.3 ships glibc `-gnu`. So `distribution-survey.md`'s "static-linking: Not
  available" verdict is confirmed and stable — nothing to watch upstream, the RFC was declined.
- **The `pkgsMusl` one-shot probe (describe, don't run).** A cheap falsification: overlay the Lean
  derivation onto `pkgsMusl` (`nix build --impure --expr 'pkgsMusl.callPackage …'`) to see whether the
  runtime even *compiles* against musl. Expected outcome given #2931: link failures in the runtime's
  glibc assumptions. A single timeboxed spike to *document the failure mode*, not a supported path.
- **The reframe (cite `distribution-survey.md`).** The real static story is **compiled-wasm output**,
  not a static ELF. A bang program compiled to a **WASI component** (§4) is portable AND
  least-authority: one `.wasm` on any wasmtime/jco host, no glibc floor, no ELF interpreter,
  capability-attenuated by its world — strictly *better* than the static tarball (Zig's gold standard
  the native binary can't reach). Native glibc-dynamic stays the dev-loop artifact
  (`distribution-survey.md` rung 0); the wasm component is the distribution artifact once ◊5+ lands.
  **One line: bang can't ship a static ELF (Lean won't), but its compiled-wasm component beats a tarball.**

## ADR-input paragraph (feeds an ADR at implementation dispatch)

*When host IO is taken up, one ADR should record:* host effects as `std/Io.bang` decls (NOT the
prelude — least-authority); the pause/resume seam as a fourth `MOutcome` (`msuspended`) driven by a
`Main.lean` loop, leaving `Source.eval`/`evalE` pure (invariants #4/#5 intact — no kernel primitive,
machine still calculated); the `--env={sim,real}` + `--allow` CLI surface; the **trace-replay gate**
as the invariant-#1 oracle for the tested-stratum host handler (JSONL Sendable trace); the
**Q(conc-6) ruling: recorded-effects replay**; and the WASI-import compiled mapping. It slots
alongside ADR-0084's slice B (`{Net}` + mock) as the general host-IO frame — `Net` is one instance,
`Console`/`Clock`/`Fs` the others. Reject: IO-in-prelude, IO-in-`Source.eval`, FD-as-payload, and a
pre-collected IO plan (rationale above).

## Proposed issues (do not file)

1. **`std/Io.bang` + the Console/Clock wedge** — two-op host-effect module + sim handlers; no engine
   change (both ops sim-replayable). *Cheapest slice; proves the module shape.*
2. **The `msuspended` seam + `Main.lean` driver loop** — the `MOutcome` extension + `--env=real` for
   Console/Clock only. *The one engine change; gated on a Sendable-payload trace.*
3. **The trace-replay differential gate** — record under `--env=real`, replay under `--env=sim`,
   assert output-equality, wire into `just verify`. *The invariant-#1 oracle.*
4. **`Fs` read-only** — one resource kind, opaque-`Int` handle, fixed-map sim. *Depends on 1–3.*
5. **(assess-only) WASI-import lowering probe** — extend the `.wat` emitter with one host-perform →
   `call $wasi:cli/stdout`. *Rung-5 spike; gated on ◊5+.*

## Citations

- ADR-0084 (IO-as-paradigm; slice-A echo-mock) · ADR-0101 G5/G6/G7/G8 + Q(conc-6) · ADR-0063 (escapedCap)
- ADR-0093 (file-modules; D5 = main's row is the capability manifest) · ADR-0095 (effect handler surface)
- `ndet-dst-design.md` (seeded-sim = replay-by-a-handler; §5 within-the-wall) · `actor-sendable-design.md` (Sendable; `copy≡share`)
- `wasm-concurrency-survey.md` §3 (WASI worlds = row-attenuation; canonical ABI = perform boundary)
- `os-inspiration-survey.md` §1 (row-attenuation = pledge; no ambient authority) · `distribution-survey.md` §4 (glibc-dynamic verdict)
- `Bang/Backend/EnvMachine.lean` (`evalE`/perform arm/`MOutcome`) · `Main.lean` (IO shell) · `Eval.lean` (`escapedCap`)
- `leanprover/lean4#2931` (musl RFC, closed not-planned) · Lean platforms doc (no musl/static)
