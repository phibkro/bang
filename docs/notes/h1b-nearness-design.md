<!-- note-status: active -->
# H1b — lexical nearness for module-qualified host performs (design pass, #127)

> Design-probe deliverable, no implementation. Isolated clone `lang-bang-probes/h1b-design`,
> branch `design-h1b-nearness`, off `main@0fbececd`. Answers: SHOULD a lexically-enclosing user
> `with Io_Console` intercept a module-qualified ambient host perform (`Io.print x`) — and if
> yes, by what mechanism? **Verdict: NO — close #127 as status quo CORRECT.** The status quo's
> concrete loss is real but narrow (§1), every mechanism that would grant it either duplicates a
> capability the driver already provides for free (§2) or reintroduces a dispatch discipline bang
> already build-refuted for the identical shadow shape (§3), and no peer language's effect-handler
> precedent does it either (§4). §5 recommends closing #127 with this note as the record; §6 is the
> ADR-input paragraph if the operator wants it recorded formally instead of closed silently.

## 0 · TL;DR

```
question         : should `with Io_Console` catch `Io.print x` (ambient) by lexical proximity?
verdict           : NO. Status quo is correct. Recommend CLOSE #127, no implementation.
what (a) loses    : a --env-free way to unit-test a program using ONLY the ambient spelling.
                     WITNESSED (§1): Io.print inside a with Io_Console block still prints to the
                     REAL terminal under --env=real, ignoring the mock. Concretely real, but
                     narrow: swap Io.print → con.print (the pre-existing named-cap spelling) and
                     the SAME program is already driver-independent, TODAY, zero new mechanism.
why (b) is wrong  : name-based nearness needs "the nearest same-label with" to have one answer.
                     WITNESSED (§3): bang ALREADY admits two simultaneously-live Io_Console
                     handlers (nested `with`), typechecks + runs today. "Nearest" is exactly the
                     dynamic/nearest-label discipline ADR-0052 build-PROVED diverges from bang's
                     canonical lexical/identity dispatch on this shape (the evalD/kernel witness).
                     get/put's "nearness" is a DIFFERENT mechanism (name→de-Bruijn-var lookup
                     through a SINGLE reserved sentinel, never more than one live binder per
                     sentinel) — not a precedent for resolving among MULTIPLE live same-label
                     instances. §3 shows the analogy the original ADR-0104 text drew was invalid
                     at the mechanism level, not just unimplemented.
why (c) is moot   : record/replay (Q(conc-6), ADR-0104 §3) ALREADY gives a program-transparent
                     mock path with no with-interception at all: replay under --env=sim runs the
                     UNMODIFIED ambient-spelled program against a trace-fed sim handler. Any
                     "explicit opt-in ambient mocking" design duplicates what --env=sim/--replay
                     already does, worse (per-with plumbing vs one CLI flag, and it would need
                     its own soundness story where record/replay already has one).
peer precedent    : Effekt (bang's own closest structural analog per q38-handler-surface-survey,
                     "dispatch-by-identity ≈ capabilities") requires EXPLICIT capability-passing
                     for a handler to intercept anything — no ambient nearness. Koka's effect rows
                     are lexically scoped by the handle construct itself (an ambient call outside
                     any handle is a compile error, not a runtime nearness search). Deno's
                     permission model (bang's own cited precedent for --allow) has NO notion of a
                     "nearer" grantor either — permissions are process-global. No surveyed peer
                     grants what H1b would add.
```

## 1 · Candidate (a) — status quo: ambient = driver-only, in-program swap = cap-threading

**Mechanism (read from code, unchanged by this probe).** `Io.print x` lowers via `hostPerformS`
(`Bang/Frontend/Surface.lean:753-772`) to `.perform (.vcap hostCapId ℓ) op arg` — a **literal**,
fixed-identity capability (`hostCapId := 999999999999`, `Surface.lean:543`), independent of any
lexical `env`. `con.print x` (the pre-existing named-cap spelling, `.dotPerform`) lowers to
`.perform (← lowerV env recv) op arg` where `recv` resolves `con` through the ordinary lexical
`env : List String` — an actual bound variable, shifting with each enclosing binder like any
other name.

**What is concretely lost — witnessed, not asserted.** A program that calls the AMBIENT spelling
inside a `with Io_Console` block is NOT mocked by it:

```bang
-- scratch/h1b/witness-a-status-quo.bang
import Io
let main =
  handle
    Io.print(SCons(Char(104), SCons(Char(105), SNil)))   -- ambient spelling, NOT con.print
  with Io_Console as con {
    print(s) => (),
    readLine(u) => SCons(Char(104), SNil)
  }
```

```
$ bang run --engine=oracle scratch/h1b/witness-a-status-quo.bang            (no --env)
error: a capability escaped its handler … (escapedCap, ADR-0063)

$ bang run --engine=oracle --env=real --allow=Console scratch/h1b/witness-a-status-quo.bang
hi                                                          -- REAL terminal output — the "mock" never ran
()
```

The enclosing `with Io_Console as con {...}` never fires; the perform reaches the driver
unconditionally whenever the label is granted, exactly as ADR-0104 §4's correction documents.
**This is real: a test harness cannot make the ambient spelling obey a local mock by wrapping it
in `with` — it must reach for `--env`.**

**But the loss is narrow — witnessed contrast.** The SAME shape using the pre-existing
`con.print` spelling is ALREADY driver-independent, with zero new mechanism:

```bang
-- scratch/h1b/witness-a2-cap-thread-works.bang — identical except con.print, not Io.print
import Io
let main =
  handle con.print(SCons(Char(104), SCons(Char(105), SNil)))
  with Io_Console as con { print(s) => (), readLine(u) => SCons(Char(104), SNil) }
```

```
$ bang run --engine=oracle scratch/h1b/witness-a2-cap-thread-works.bang          -- no --env
()                                                          -- mock ran, no real IO attempted

$ bang run --engine=oracle --env=real scratch/h1b/witness-a2-cap-thread-works.bang   -- even WITH --env=real
()                                                          -- STILL the mock — driver never reached
```

So the honest framing of what (a) "loses" is: **the ambient (`Mod.op`) and cap-threaded
(`cap.op`) spellings are, and were always designed to be (ADR-0104 §4), two DIFFERENT
constructs** — "ask the runtime" vs "ask this specific installed handler" — not two spellings of
one nearness-resolved call. A test harness that wants driver-independence already has the tool:
write the function under test to take its `Io_Console` capability as a parameter (or install it
via `with … as con`) and call `con.print`, not `Io.print`. That is the existing idiom, it costs
nothing new, and — the load-bearing point for closing #127 — **record/replay (§2 below) covers
the remaining case** (a program the operator does NOT want to rewrite, using the ambient spelling
throughout) without any `with`-interception mechanism at all.

## 2 · Does bang already have the capability H1b would add? (record/replay)

ADR-0104 §3 / Q(conc-6): every real run under `--env=real` records a Sendable
`(label,op,payload,result)` trace; `--env=sim` (or `--replay`) re-runs the **same, unmodified**
program — ambient spellings included — against a trace-fed sim handler under the pure
`Source.eval` oracle. This already gives "run this ambient-IO program against canned answers,
no real IO" — the exact capability a test harness reaching for `with`-interception is actually
after. The difference from H1b:

| | H1b (name-based nearness) | record/replay (shipped) |
|---|---|---|
| granularity | per-`with` block, in-program | per-run, at the CLI (`--env=sim`/`--replay`) |
| needs a trace/fixture first? | no | yes (or a hand-authored fixture via `--replay`) |
| soundness story | NEW — needs its own (§3 shows it's the wrong one) | EXISTING — Source.eval is the oracle, ADR-0104 §3 |
| changes the elaborator? | yes (env-shape change, §3) | no |
| works for data-dependent IO (`readFile` on a computed path)? | yes, same as any `with` | yes (the replay-prefix driver handles it, ADR-0104 §4) |

Record/replay is coarser-grained (whole-run, not per-block) but it is **already shipped, already
proof-obligated, and does not touch the elaborator or cap-soundness at all**. A test harness
wanting the H1b property today reaches for `--replay` with a small fixture trace, not a new
in-language construct. This is why (a)'s loss, though real, does not by itself justify (b).

## 3 · Candidate (b) — name-based nearness: REJECTED, same discipline ADR-0052 already killed

**The proposed mechanism** (ADR-0104 §4's H1b note, and the assignment brief): widen the lowering
`env : List String` to `env : List (String × Option Label)` (or reserve per-label sentinels
mirroring `capState`), so `.handleCustomS`'s install pushes a per-label alias `hostPerformS`'s
lowering can find BEFORE falling back to the literal cap — i.e., resolve `Io.print` to whichever
`with Io_Console` is lexically nearest, exactly like `get`/`put` resolve to the nearest `state`.

**The get/put analogy is invalid at the mechanism level — witnessed.** `get`/`put` lower to
`.perform (.vvar (lookup env capState)) op v` (`Surface.lean:568-573`) — an ordinary **de Bruijn
variable** resolved through the lexical `env`, using **one reserved sentinel name** (`capState`)
pushed exactly once per `state … in` binder (`Surface.lean:580`, `handleS`-style). Confirmed:

```bang
-- scratch/h1b/witness-c-getput-shadow-is-fine.bang
let main = state 1 in state 20 in get
```
```
$ bang run --engine=oracle scratch/h1b/witness-c-getput-shadow-is-fine.bang
20
```

This "nearness" is genuinely just variable shadowing: `get` never NAMES which `state` it means,
so there is only ever one binder in scope competing for the sentinel slot at any lexical position
— the same mechanism that resolves any shadowed local. There is no point where TWO
simultaneously-live `state` frames both claim the unqualified `get` and something has to
adjudicate between them by proximity-search over runtime identities; the de Bruijn index already
picked one, at ELABORATION time, before any identity exists.

`Io_Console`, by contrast, is a **user-named, freely-instantiable** effect. Multiple
simultaneously-live instances is the ordinary case, not a corner case — confirmed:

```bang
-- scratch/h1b/witness-b-shadow-risk.bang
import Io
let main =
  handle
    handle con_inner.print(SCons(Char(105), SNil))
    with Io_Console as con_inner { print(s) => (), readLine(u) => SCons(Char(50), SNil) }
  with Io_Console as con_outer { print(s) => (), readLine(u) => SCons(Char(49), SNil) }
```
```
$ bang run --engine=oracle scratch/h1b/witness-b-shadow-risk.bang
()                                                          -- typechecks, runs — TWO live Io_Console frames
```

Today this is fully sound because each perform NAMES its handler explicitly
(`con_inner.print`/`con_outer.print`) — dispatch-by-identity (ADR-0055) resolves each cap to
exactly the handler that minted it, no ambiguity, ADR-0063's escape story intact. **A name-based
nearness mechanism for the AMBIENT spelling would have to answer, for a bare `Io.print` inside
this shape, "which of the two live `Io_Console` frames does this bind to?"** — and the only
candidate answer under "nearness" is *the lexically closest one*, i.e. `con_inner`'s frame.

**That is precisely the nearest-label discipline ADR-0052 build-proved diverges from bang's own
canonical semantics.** ADR-0052's witness (`handle (state 1 10) (handle (state 1 20) (perform
cap=1 1 "get"))`) showed the kernel's LEXICAL/identity dispatch (cap names ITS handler,
answer `10` — outer, because the cap in that witness was minted by the outer handler) disagrees
with a NEAREST-LABEL dispatch discipline (answer `20` — inner, nearest same-label frame) on a
well-typed same-label-shadowing program, and **REJECTED nearest-label as bang's semantics for
exactly this reason** — "typing is by label, dispatch is by identity" (the glossary's core
principle) exists BECAUSE nearest-label was tried and found unsound-feeling / inconsistent with
the rest of the design (ADR-0052's route-B: re-derive the CalcVM reference to match lexical
dispatch, not the other way around). ADR-0055 then independently hardened identity dispatch
further (global-fresh counter, never depth-reused) specifically to kill a same-depth **impostor
collision** — a cap resolving to a same-shaped handler that is NOT the one that minted it.

H1b's name-based nearness would reintroduce the identical shape for the ambient spelling
specifically: `Io.print` would resolve not to "the cap this call was written to reference" (there
is no such cap — that's the whole point of ambient syntax) but to "whichever `with Io_Console`
happens to be textually closest at elaboration time" — a **structural**, not merely unfortunate,
reintroduction of nearest-label resolution into a language that spent two ADRs (0052, 0055)
establishing the opposite discipline for named handlers. The fact that the *ambient* spelling
has no cap identity of its own to check against is not a loophole that makes nearness safe here;
it is the reason nearness is the ONLY available resolution rule for it, which is exactly the
rule already rejected.

**Cap-soundness consequence, if built anyway.** Even setting aside the ADR-0052 precedent: making
`with Io_Console` interceptable by an ambient call means a user handler can now observe/capture
performs it never received a named cap for. Combined with ADR-0063's laundering finding (a
handler's answer type can be free enough to let a live cap escape through a re-handle by label,
not identity) this widens the exact attack surface ADR-0063 narrowed — a handler could capture
state across performs it has no lexical relationship to, purely by being "nearest" at the moment
of an unrelated program's `import Io` call. This was not deeply probed (out of scope for a
design-only pass with no kernel change proposed), but it is a second, independent reason to
expect (b) is expensive to make sound, not merely expensive to implement (ADR-0104 §4 already
prices the implementation at a genuine env-shape change through the whole `lowerC`/`lowerV`
mutual — ~18 arms across 5 files).

## 4 · Candidate (c) — explicit opt-in, and peer precedent

**No surveyed peer effect-handler language does ambient-nearness dispatch either.**

- **Effekt** — bang's own closest structural analog (`docs/notes/q38-handler-surface-survey.md`:
  "Effekt: caps 2nd-class ⟹ can't escape"; "rows (Koka) and capabilities (Effekt) are two
  modalities of ONE calculus," Tang & Lindley POPL'26, already cited in-repo). Effekt capabilities
  are **passed explicitly**; there is no ambient effect operation that resolves itself to "the
  nearest handler of the right type" without a capability argument at the call site. bang's own
  `cap.op` spelling is already the Effekt-shaped construct; `Mod.op` (H1) is the thing Effekt
  doesn't have at all — bang added it deliberately for the driver-as-outermost-handler shape
  (ADR-0104 §4's H1 "built-in-ambient" framing, following get/put), not as an Effekt feature.
- **Koka** — effect operations are lexically scoped by the `handle`/`with` construct that installs
  them; calling an effect operation with no enclosing handler for its effect is a **compile-time**
  effect-row error, not a runtime nearness search. Koka's rows are the label-typing half of the
  same split bang uses (`q38-handler-surface-survey.md` §"rows ≈ bang's typing-by-label"); Koka
  never needed a runtime "nearest" rule because absence of a handler is caught by the type, and
  presence of exactly one enclosing handler is guaranteed by the row discipline at the call site —
  a property H1's ambient `Mod.op` deliberately gives up (it types by label but resolves to a
  RUNTIME-provided handler regardless of lexical position, which is the entire feature).
- **Deno** — the CLI-level precedent ADR-0104 §2 already cites for `--allow`. Deno's permission
  grants are **process-global**; there is no notion of "a nearer grantor" — a `with`-shaped
  in-program mock is exactly NOT how Deno's model works (Deno's test mocking is done by injecting
  a different implementation at the module-import boundary, i.e. dependency substitution, closer
  to bang's cap-threading idiom than to lexical interception).
- **OCaml effect handlers** — dispatch is dynamic-nearest-handler by **effect identity**
  (OCaml's `perform`/`match … with effect E k -> …` finds the innermost handler for `E`), which
  IS a nearest-X-wins discipline — but OCaml has no separate "ambient" vs "named-capability" split
  at all; every effect in OCaml is ambient by construction (there is no OCaml equivalent of bang's
  `cap.op`). Citing this as precedent for (b) would be importing OCaml's single mechanism
  wholesale, not adding nearness to bang's TWO-mechanism (label-typed + identity-dispatched)
  design — a different, larger change (collapsing `Mod.op`/`cap.op` into one construct) explicitly
  out of scope here and in tension with ADR-0052's own reasoning for why bang chose identity over
  nearest-match in the first place.

No peer offers a "ambient call, resolved by lexical proximity to a named handler instance"
mechanism as a THIRD option alongside static rows and identity-passed capabilities. The
explicit-opt-in shape closest to what's being asked for (c) is: a handler installer marks itself
as "also willing to serve ambient performs of label ℓ." That is not a nearness mechanism at all —
it is a way of minting `hostCapId`-equivalent identity FROM a `with` block, which collapses back
into either (i) making `with Io_Console` install AT `hostCapId` (a global singleton identity,
defeating the purpose of user-named handler instances and reintroducing exactly one collision
per program) or (ii) the driver's `--allow` surface deciding at the OUTERMOST level which handler
serves ambient calls — which is just `--env=real`/`--env=sim` again, already shipped.

## 5 · Recommendation

**Close #127. Status quo is correct; no implementation warranted.** The concrete loss (§1) is
narrow and already has a zero-cost workaround (spell the call `cap.op` instead of `Mod.op` when a
program wants `with`-driven testability) plus a shipped coarser-grained mechanism that covers the
harder case (record/replay, §2). The proposed fix (§3) is not merely unimplemented but
**structurally re-derives a dispatch discipline bang already build-refuted** (ADR-0052's
nearest-label divergence) for the identical same-label-shadow shape, demonstrated live today with
`Io_Console` specifically (§3's witness). No surveyed peer language does ambient-nearness dispatch
either (§4); the two real options in the literature are static lexical scoping (Koka — bang
already has this for the row/typing half) and explicit capability-passing (Effekt — bang already
has this as `cap.op`). bang's H1 ambient spelling is a genuine third, deliberate design point
(driver-as-outermost-handler, following get/put's *lexical-variable* nearness, not
identity-nearness) — and it is coherent as shipped. The two spellings staying "deliberately
different constructs" (ADR-0104 §4) is not an unfinished feature; it is the correct resting state.

**If the operator wants a lighter-weight per-block mock than record/replay**, the design space
worth a SEPARATE, smaller design pass (not H1b, not filed here) is: extending `--replay` to accept
a fixture scoped to a specific `with` block's lexical region rather than a whole-program trace —
that stays entirely within the shipped record/replay soundness story (§2) and adds no dispatch
mechanism. Naming it here only as a pointer; not scoped or costed, since nothing in this probe's
evidence suggests it is currently needed (no consumer asked for finer granularity than a
whole-run trace).

## 6 · ADR-input (if the operator wants the closure recorded formally)

*If #127 is closed via an ADR rather than silently:* record that H1b was investigated and
REJECTED — bang's dispatch-by-identity discipline (ADR-0055) plus the lexical-dispatch ruling
(ADR-0052) together forbid resolving an ambient host perform by proximity-to-a-named-handler,
because the identical resolution question (which of N same-label live frames wins) was already
answered in favor of identity over nearness, build-provenly, for user handlers generally; H1's
ambient spelling stays a deliberate third construct (driver-as-outermost, get/put-style *lexical
variable* nearness for the get/put case specifically, not identity-nearness for named effects);
record/replay (ADR-0104 §3) is the shipped answer to the test-mocking need that motivated the
question. Reject: name-based env-widening (ADR-0052/0055 precedent), an ambient-serving `with`
marker (collapses to either a global singleton identity or the existing `--env` surface), and
unifying `Mod.op`/`cap.op` into one OCaml-style nearest-handler construct (a strictly larger
change reversing ADR-0052's own rationale). No kernel change, no `Spec.lean` change either way —
this was a pure surface/elaboration question, resolved by NOT implementing.

## Citations

- ADR-0104 (`docs/decisions/0104-host-io-environment.md`) §4 — the correction section, the H1b
  naming, the mechanism-vs-name-lookup analysis this note verifies and extends
- ADR-0052 (`docs/decisions/0052-effect-dispatch-is-lexical-calcvm-re-derive-evald.md`) — the
  build-proven nearest-label-vs-lexical divergence witness this note shows applies directly to H1b
- ADR-0055 (`docs/decisions/0055-global-fresh-capability-identity.md`) — global-fresh identity
  minting, the collision/impostor risk a proximity-resolved ambient cap would reopen
- ADR-0063 (`docs/decisions/0063-capability-escape-is-a-defined-fail-loud-for-v1.md`) — the
  escape/laundering territory this question sits in; the answer-type-free-handler attack surface
- `docs/notes/host-io-design.md` §3, Q(conc-6) — record/replay as the shipped mock-without-nearness
  mechanism (§2 of this note)
- `docs/notes/q38-handler-surface-survey.md` — Effekt/Koka/rows-vs-capabilities census (§4)
- `Bang/Frontend/Surface.lean:289,458-460,532-543,547-773` — `hostPerformS`/`get`/`put`/
  `handleCustomS` lowering, read-only (verified, not modified)
- `Bang/Core/Semantics/Eval.lean` — `idDispatch`/`escapedCap` (identity-first dispatch, unmodified)
- witness programs (this probe): `scratch/h1b/witness-{a-status-quo,a2-cap-thread-works,
  b-shadow-risk,c-getput-shadow-is-fine}.bang`, run via `bang run --engine=oracle` (+ `--env=real
  --allow=Console` for witness-a) on the built `.lake/build/bin/bang`, 2026-07-11
