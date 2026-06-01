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

**Bisimulation — reference built + pure core proven.** The open theorem is now
being attacked directly, in two committed, `sorry`-free pieces:
- `Bang/CalcReifyRef.lean` — the denotational reference *exists in Lean*. The
  positivity escape is concrete: **CBPV** (values vs computations split) + a **free
  monad** `Comp` whose resumption `Int → Comp` sits in *positive* position, plus
  fuel for the non-structural `k w` re-runs. It is `rfl`-validated against the same
  seven demonstrators — a second in-Lean cross-check.
- `Bang/CalcReifySim.lean` — the **pure core** of the bisimulation: the
  continuation-passing simulation (cf. `CalcCBN.sim`) for the `val`/`add`/`var`/
  `let` fragment, with the handler stack `K` and data stack carried as passengers,
  proven by structural induction (`pure_sim`/`pure_correct`). Crucially `eval_pure`/
  `pure_correct_ref` prove the structural denotation `pden` *is* the `ret`-fragment
  of the real fuel-indexed reference `CalcReifyRef.eval` — so the pure core is a
  genuine **machine-vs-reference** agreement (both `CalcReify.run` and
  `CalcReifyRef.run` yield `n` on a closed pure program), not a parallel
  definition. The proven fragment now also covers **`handle` over a pure body** —
  an *unfired handler is transparent* — which brings the machine's `INSTALL`
  instruction and the return-through-a-handler-frame path into the proof (via
  `handleC_ret`), still with no `vcont ↔ ek` relation needed (the handler is
  installed but its clause never runs). The value relation `RelVal`/`RelEnv`
  scaffolding is in place (int case); the `vcont ↔ ek` case — a step-indexed
  logical relation for resumptions — is the remaining residual. **Two firing
  results now exist in Lean, sorry-free:**
  - **`fire_agree` — the first ∀-quantified *firing* theorem.** For *any* pure
    payload `e` and *any* pure non-resuming `clause`, machine and reference agree on
    `handle clause (perform e)`: both yield the clause's denotation under the
    payload. The clause genuinely runs with the captured continuation (zero-shot /
    payload-threading). Two ingredients made it provable: (i) an
    *environment-independent* structural fuel bound `fuelOf : Src → Nat` (replacing
    `eval_pure`'s `∃F`), which breaks the circularity the reference's fuel-capturing
    resumption closure would otherwise create; (ii) a partial `RelEnv.consK`
    constructor relating an opaque machine `vcont` slot to a reference `ek` slot —
    sound here because the clause never reads it. This is the genuine first step
    *into* the `vcont ↔ ek` frontier.
  - **`Agree` — machine-checked agreement on *specific* harder programs.** `run =
    some (vint k) ∧ CalcReifyRef.run = some k`, proven by `⟨rfl, rfl⟩` for the
    non-tail, multi-shot (incl. triple), re-handling, and payload demonstrators —
    program-specific, but covering the *resuming* behaviours `fire_agree` does not
    yet generalise, both sides *in-Lean* (strictly stronger than the TS fuzz).

  - **The step-indexed `vcont ↔ ek` relation is now *formalized* in Lean,
    sorry-free** (the `Resuming` section of `CalcReifySim`). The partial `consK`
    stub is replaced by a real `def RelV : Nat → Value → Entry → Prop` carrying the
    resumption agreement (with `RelEnvI`, `observe`, `RefK`), and Lean accepts it —
    so the #1 risk (that the relation is not even *expressible* under strict
    positivity) is retired. The escape, machine-checked: a **`def`** (not an
    inductive) by **structural** recursion on the index (the `vcont↔ek` clause at
    `i+1` refers to `RelV` only at `i`), with the resumption `g : Int → Comp`
    occurring only *applied*. It integrates with the existing pure scaffolding
    (`relEnvI_lookup`, reference `bind_mono`, a forgetful map `relEnvI_forget` to
    the old `RelEnv`, and `pure_sim_indexed`). What remains is `capture_relates` —
    that an actual PERFORM-capture *satisfies* `RelV` — and the firing theorem on
    it. (See the playbook's K3 section for the four definability decisions and two
    sharpenings of where the difficulty lives.)

  - **Four ∀-quantified *resuming* firing theorems are now proven**, sorry-free:
    `fire_resume_tail` (`handle (resume (var 1) v) (perform e) ≡ ⟦v⟧` — tail resume,
    empty captured continuation), `fire_resume_nontail_body`
    (`handle (resume (var 1) v) (add (perform e) rest) ≡ ⟦v⟧ + ⟦rest⟧` — non-tail
    body, *non-empty* captured continuation; the 1007 demonstrator, now ∀-general),
    `fire_multishot` (`handle (add (resume@1 v1) (resume@1 v2)) (perform e) ≡
    ⟦v1⟧ + ⟦v2⟧` — the resumption invoked **twice**, the signature reification
    capability; demonstrator `27`), and **`fire_deep`**
    (`handle (resume (var 1) v) (add (perform e1) (perform e2)) ≡ w1 + w2` — genuine
    **deep re-handling**: the resumed continuation itself performs and re-fires the
    handler; the 14 demonstrator, now ∀-general). These are the first results where
    the resumption is genuinely **invoked** generally (stronger than `fire_agree`,
    non-resuming; stronger than the `Agree` `rfl`-demonstrators, program-specific),
    all by **direct inside-out construction** (machine side like `machine_fire`;
    reference side via a clean `eval_*` reduction + `handleC`).

  The remaining residual splits along a sharper axis than "deep vs. shallow"
  (correcting an earlier framing): **(A) fixed control-flow skeleton, ∀-general over
  pure subterms** — including *deep / re-handling* (✅ `fire_deep`) — is
  **direct-constructible**, because the language has no recursion/loops, so a closed
  program's firing count is bounded by its skeleton. The remaining (A) leaves
  (non-tail clause, multi-shot × non-empty continuation, deeper skeletons) are *more
  of the same* — longer chains, no new ideas. **(B) ∀-general over *all* `Src`** (the
  full `exec ∘ compile ≡ run`) is the **remaining frontier** — the part that must
  invoke `RelV`'s agreement (`capture_relates`). **Progress into (B), sorry-free:**
  `capture_relates_tail` and `capture_relates_add` prove an actual PERFORM-captured
  `vcont` **satisfies `RelV`** for every *one-shot* capture (empty + non-empty pure)
  — the first proof `RelV` is inhabited by real captures (non-vacuous; contravariance
  does not bite). This also **fixed a design bug** (`RefK` was `Int → Comp → Comp`;
  corrected to `Comp → Comp` — the clause continuation consumes the resumption's
  *result*, not its payload), with `pure_sim_back` as new reusable infrastructure.
  What remains: the *inductive* deep `capture_relates` (a captured continuation that
  itself performs re-fires the handler, the fresh capture related at the predecessor
  index by the IH) and a **general inductive simulation** consuming `RelV` at resume
  nodes — both needing the continuation-correspondence infrastructure (machine `Kont`
  ↔ reference eval-context), the paper-section that remains. Key realisation: `RelV`
  transfers *machine-halts ⇒ reference-agrees*, so it is needed only in the general
  ∀-`Src` induction, not the closed firing theorems (which prove termination *and*
  agreement by direct construction). (See the playbook's K3 section for the (A)/(B)
  distinction, per-fire-env caveat, reusable proof shapes, and the
  contravariance/downward-closure caveat.)

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
