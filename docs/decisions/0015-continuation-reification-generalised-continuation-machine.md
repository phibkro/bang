# ADR-0015 · Continuation reification — a flat generalised-continuation machine (`CalcReify`); multi-shot / non-tail handlers

- **Status:** Accepted (machine + demonstrators verified; cross-checked vs an
  independent TS CPS interpreter on 2k+ random programs; in-Lean general theorem is
  the named next step)
- **Date:** 2026-06-01
- **Related:** 0011/0012/0013/0014 (all deferred reification — this is that frontier),
  0004 (calculate, don't hand-design), 0009 (one construct at a time), 0008 (the
  free-monad `eval`), roadmap K3 + §8 reading canon (Tsuyama 2024)

## Context

Every prior effect machine deliberately avoided **continuation reification**: Throws
is zero-shot (discards the continuation), State resumes only *in tail position*. A
*general* handler hands its operation clause the **resumption** as a first-class
value, to be invoked **zero, one (non-tail), or many times** (nondeterminism,
generators, backtracking). This is the genuine frontier (Hillerström–Lindley–Atkey,
*Effect handlers via generalised continuations*; Tsuyama et al. 2024).

Two facts settled the machine's shape:

1. **Reification *is* defunctionalization — and Lean proves it.** A resumption can't
   be a meta-level function value: `vcont : (Value → …) → Value` fails Lean's
   strict-positivity check. That failure is not an obstacle but the *reason*
   reification exists — the continuation must be made **data**.
2. **It forces the machine flatten** that ADR-0011/0012/0013/0014 each predicted. The
   closure machines reduce a subterm via a *nested meta-`exec`*; a resumption cannot
   be captured across that meta-boundary. So reification needs a **flat** machine
   whose continuation is explicit data — a genuinely different shape.

## Decision

Calculate a **flat generalised-continuation machine**, `Bang/CalcReify.lean`,
following the Hillerström–Lindley–Atkey representation: the continuation `Kont` is a
list of frames (`clause = some` ⇒ a handler frame; `clause = none` ⇒ a pure-return
frame), and a **reified resumption is a captured prefix of that list**, held in a
`vcont` value as data `(capturedCode, capturedEnv, capturedStack, clause, clauseEnv)`.

- **`perform e`** evaluates `e`, captures the current pure continuation up to the
  handler as a `vcont`, and runs the clause with `(payload, vcont)` (payload @0,
  resumption @1).
- **`resume k v`** **splices** the captured continuation back: it re-installs the
  handler around it (so the resumed body is re-handled — *deep* handlers) and pushes a
  pure frame carrying the clause's own continuation, so the resumption's result flows
  back to the clause. `resume` is therefore a *call that returns* (non-tail by
  nature), and calling it twice runs the captured continuation twice (multi-shot).
- **Scope kept minimal so it stays provable** (ADR-0009): arithmetic + `let` + one op
  + `handle`/`resume`; **single handler depth** (a `perform` is handled by the
  innermost handler frame; forwarding through pure-return frames to an *outer* handler
  is the documented follow-up); **no closures/CBN** (composing reification with the
  closure core is a separate step).

## Status / what is verified

The machine (`exec`, `compile`, `run`) is built and its **core behaviours are
statically verified by `rfl`** in the build (seven demonstrators):

| program | demonstrates | result |
|---------|--------------|--------|
| `handle (resume@1 7 + 100) (perform 5 + 1000)` | **one-shot, non-tail** | 1107 |
| `handle (resume@1 7) (perform 5 + 1000)` | one-shot, tail | 1007 |
| `handle (resume@1 7 + resume@1 20) (perform 5 + 1000)` | **multi-shot** (resumed twice) | 2027 |
| `handle 999 (perform 5 + 1000)` | **zero-shot** (continuation discarded) | 999 |
| `handle (var0) 42` | normal return passes through | 42 |
| `handle (resume@1 7) (perform 1 + perform 2)` | **re-handling** (perform inside a resumption) | 14 |
| `let x=5 in handle (x + resume@1 3) (perform x)` | payload reaches the clause | 8 |

This is a genuine, working reified-handler machine — the capability all five prior
machines avoided. The file is `sorry`-free: it asserts exactly what it proves.

**Foundation proven.** `exec_succ` / `exec_mono` (fuel monotonicity) are proven,
`sorry`-free — the bedrock any correctness simulation needs (every machine step,
including the empty-code return-through, `PERFORM`, and `RESUME`, decreases fuel).

**Independent empirical cross-check landed.** Because there is no in-Lean reference
`eval` for this machine (a reference would itself be a second abstract machine — see
below), `execreify` is diff-tested against an **independent** TS CPS interpreter
(`harness/src/reify-cps.ts`): a direct free-monad interpreter of the *same* `Src`
where a resumption is a **real JS closure** `(w) => Comp` — exactly the representation
Lean's strict positivity forbids, hence a genuinely different implementation.
Capture is `op`-node construction; splice is `bind`; the deep handler re-installs
itself around the resumption; single-handler-depth is modelled by *sealing* a
clause's own standing `perform` to stuck. The two agree on the seven demonstrators,
the notok (stuck) shapes, **and 2000 random multi-shot / non-tail programs per CI run
(stressed to 20 000 at depth 5 locally with zero disagreements)** —
`harness/test/calc-reify.test.ts`. This is the "run the real journey" cross-check:
the hand-built `Kont`/`Frame` splicing matches the textbook closure semantics.

**Named next step — the general theorem.** Unlike the prior five machines, the
*general* `exec ∘ compile ≡ eval` is **not yet proven** here, and the honest
assessment is that it is **research-grade**, for a *fundamental* reason: strict
positivity forces any reference to defunctionalize the resumption into data, so the
reference is a **second abstract machine** (a Src-frame generalised-continuation
machine), related to `exec`'s `CodeKont` only through `compile`. The proof is then a
**bisimulation** between the two machines (the continuation-correspondence invariant
`CodeKont = compile <$> SrcKont` preserved across `PERFORM`/`RESUME`) — the kind of
abstract-machine-correctness result that is a paper section (Hillerström–Lindley), a
*different* shape than the equality-style big-step sims the other eight machines use.
There is no denotational shortcut: `Comp` may hold functions, but `Value` cannot, so
first-class resumptions must be data on both sides. The standard empirical
cross-check — a harness fuzz against an **independent** TS CPS interpreter (JS
closures are real resumptions — no positivity problem) — **has now landed** (see
above), so the machine is empirically validated against a different implementation;
what remains open is only the in-Lean *machine-checked* bisimulation.

## Rationale

- **Faithful to the literature** (ADR-0004): the generalised continuation and the
  capture/splice rules are Hillerström–Lindley–Atkey's machine; nothing is
  hand-designed beyond linearizing it into instructions.
- **Honest about the proof boundary** (the project's "prove only what you can; never
  fake" rule): the demonstrators are `rfl`-real; the general theorem is named, scoped,
  and planned rather than asserted or `sorry`-faked.
- **Minimal, to stay tractable**: single op, single handler depth, no closures —
  isolating the *new* mechanism (capture + splice + re-install) from the orthogonal
  concerns (forwarding, closures), each a later increment.

## Rejected alternatives

| option | why not |
|--------|---------|
| **meta-function resumptions** (`vcont` holds `Value → …`) | fails Lean positivity — and that *is* the point: reification must defunctionalize to data |
| **extend a prior (nested-meta-`exec`) machine** | a resumption can't cross the meta-`exec` boundary; reification requires the flat machine |
| **full multi-handler + closures now** | research-grade; would ship a large partial proof. Isolate the mechanism first (ADR-0009) |

## Revisit if

- The general theorem is proven → update status to Accepted-proven and record the
  proof shape in the playbook.
- A second op / outer-handler **forwarding** is needed → generalise `perform` to
  unwind through pure-return frames, capturing them into the `vcont` (the full
  generalised continuation; needs `vcont` to hold a frame list — a mutual inductive).
- Reification must compose with **closures/CBN** → fold the flat machine's frames over
  the closure core (the hardest composition; a separate ADR).
