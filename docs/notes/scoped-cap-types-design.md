<!-- note-status: active -->
# Scoped capability types — the post-v1 door ADR-0063 named, now concretely motivated (#134)

> Design probe (2026-07-12, `design-scoped-cap-types`). DESIGN, NOT a decision — deliverable is this
> note + the runnable witnesses in `Bang/Witness/ScopedCapWitness.lean`. No implementation this lane.
>
> **The motivating change since the last pass.** The archival `scoped-capabilities-for-vcapfree-drop.md`
> (#18, 2026-06-27) opened with *"there is NO v1 soundness hole"* — the escape was HasCTy-untypeable.
> **ADR-0063 refuted that.** The laundered-via-re-handle escape (`progComp`, `ReturnEscapeReach.lean`) is
> a **typeable, VcapFree, well-typed** program that reaches `.escapedCap`: B-occ guards the *direct*
> escape by LABEL, but a re-handle launders the label out of both the row and the answer type while the
> cap rides inside, dispatching by IDENTITY to the dead handler. So the door this note designs is no
> longer a hardening nicety on a closed hole — it is the **correctness-by-construction endpoint for a
> real, surface-reachable escape** (#134: `let leaked = state 0 in { get } in $leaked` typechecks and
> escapes). This note supersedes the #18 record's cost verdict with the post-ADR-0063 candidate space.

Every claim about bang's own code is cited `file:line` or to a build-checked witness and graded
shown / suggests / can't-verify. Web/paper citations are in §8; `refs.bib` already carries the four
capability-safety papers (`boruch-gruszecki-22-scoped-capabilities`, `brachthauser-oopsla20/22`,
`boruch-gruszecki-oopsla25-capless-reach-capabilities`, `tang-popl26-rows-capabilities-modal-effects`).

---

## 0 · The one-paragraph thesis

The escape has a single structural shape: **a capability RETURNED (as a captured thunk) out of the
handler that binds it, then forced after the handler pops** (`ScopedCapWitness.progEscape` → `.escapedCap`,
build-checked). Every capability use in the entire corpus (50 example programs, §3) does the *opposite*:
the cap is passed **down** (as an argument, or performed lexically inside the handle body) and **never**
returned/stored/thunked-out (`ScopedCapWitness.progDown` → `.done`, build-checked). That gap **is** the
"second-class capability" cut (Osvald/Rompf; Brachthäuser System C): caps may go down, never up. So the
cheapest static exclusion that makes the escape unrepresentable — **second-class capabilities** — costs
**zero legitimate corpus programs** (census: 0 rejections, §3), needs **no kernel change and no `∀`**
(it is a surface-checker rule, elaborate-to-mono, ADR-0103), and is a strict special case of the full
rank-2/`runST` region-typing endpoint the memory-management survey §4 already named. **Recommendation:
adopt second-class caps as the v1.5 door (a surface premise `¬ capOccurs ℓ A` on every handler), keep
full rank-2/CC<:□ region-capability types as the genuinely-post-v1 generalization** unlocked only when
first-class-cap *return* is a demanded feature (no corpus program demands it today).

---

## 1 · What the escape actually is — the shape all three candidates must exclude

`ScopedCapWitness.progEscape` (build-checked `.escapedCap`) is the ADR-0063 shape at the kernel level:

```
letC (handle (state 1) (ret (vthunk Mesc)))    -- the handler RETURNS a thunk...
     (force (vvar 0))                            -- ...forced AFTER the handler pops
  where Mesc performs on the outer cap (vvar 0)  -- the thunk closes over the bound cap
```

The cap escapes **upward** — out of the handler, inside the returned value. Contrast the corpus idiom
`ScopedCapWitness.progDown` (build-checked `.done`):

```
handle (state 1) (force (vthunk downBody))       -- the handler FORCES a thunk in place...
  where downBody performs on the bound cap        -- ...the cap is used DOWN, never returned
```

The discriminator, stated structurally and build-checked (`ScopedCapWitness.capOccurs`): **the answer
type `A` of a handler binding label `ℓ` must not carry `cap ℓ`** (directly, or under a thunk / sum /
product / μ). `capOccurs 1 (U _ (F 1 (cap 1))) = true` (escape flagged); `capOccurs 1 (F 1 unit)`-ish
`= false` (corpus clean); it reaches through a returned pair (`U _ (F 1 (int × cap 1))) = true` — the
System-Capless "reach capability" gap for generic containers) and is per-label (`cap 2` not flagged for
`ℓ=1`, matching dispatch-by-identity being per-handler-instance). **Shown** (all six `#guard`s in
`Bang/Witness/ScopedCapWitness.lean`, built green in the 828-job tree).

**Why keying on the CAP former, not the LABEL, is the whole point.** ADR-0063's escape *laundered the
label* out of the answer type via the inner re-handle — that is precisely why the label-keyed B-occ
(`¬ LabelOccurs ℓ A`, ADR-0057) passes. A scoped-cap discipline keys on the `cap` former, which survives
the laundering because the returned thunk's body still performs on the outer cap. `capOccurs` flags where
B-occ was blind. This is the memory-management survey §4.5 obligation ("re-index the escape guard by
identity/region, not strengthen a still-leaky label check") made concrete as a surface predicate.

---

## 2 · The candidate table

| | (a) rank-2 / `runST` scoped types | (b) **second-class capabilities** | (c) honest do-nothing (status quo) |
|---|---|---|---|
| **mechanism** | cap type carries a fresh **scope variable**; handle's result type must not mention it (avoidance) | cap is a **second-class value**: passable down (args), never returned/stored/thunked-out | C2 runtime stamp + `escapedCap` defined fail-loud (ADR-0063) |
| **prior art** | Launchbury–PeytonJones `runST`; CC<:□ avoidance (Prop 3.3); Tofte–Talpin regions | Osvald/Rompf second-class values; Brachthäuser Effekt/System C (`brachthauser-oopsla20/22`) | OCaml 5 `Effect.Unhandled`; Koka `final` |
| **where the check lives** | surface checker (kernel has **no ∀**, IR.lean:240) — a phantom scope on the cap type + answer-avoidance, elaborate-to-mono | surface checker — one premise `¬ capOccurs ℓ A` per handler; **no scope variable needed** | already shipped (C2 lane, `scratch/cap-gc/`) |
| **kernel change** | none (surface-only, ADR-0103 erased rung) | **none** (surface-only, same erased rung) | none |
| **excludes the #134 escape?** | yes (statically) | **yes (statically)** | no — detects at first run |
| **corpus rejections (§3)** | 0 | **0** | 0 (nothing rejected; nothing statically excluded either) |
| **also buys** | full region-escape prevention; effect polymorphism (with boxing); re-handleable stored caps | the escape exclusion, and **only** that — minimal | nothing static; keeps first-class-return *working* (into a fail-loud) |
| **forbids that a corpus program needs** | nothing today; forbids returning a cap even scoped-safely (needs boxing to recover) | **returning/storing a cap** — nothing in the corpus does this (§3) | n/a (forbids nothing) |
| **cost** | ≥ the whole inc-5 effort: subtyping (kernel dropped `Qle`), reference-dependent `VTy`, boxing | **~1 session, syntactic**: one `capOccurs` premise per handler-typing rule, threads like B-occ | 0 (done) |
| **proof burden** | logical relation OR the full CC<:□ syntactic metatheory (progress+preservation over capturing types) | **syntactic induction** (a `LabelOccurs`-shaped premise — see §5 on the LR question) | none new (ADR-0063 already gates it) |

The three are a **ladder, not rivals**: (c) is shipped and sound-dynamic; (b) is the cheapest *static*
exclusion and a strict special case of (a) (empty scope / no return); (a) is the general endpoint that
also solves region-escape (memory-management-survey §4, M7). Each higher rung is forward-compatible: (b)'s
`¬ capOccurs ℓ A` is exactly CC<:□'s answer-avoidance projected onto the cap former (the
`scoped-capabilities-for-vcapfree-drop.md` §"forward-compatible" observation, still true).

---

## 3 · The corpus census — the falsifier for over-restriction

**Bar: zero rejections of legitimate programs.** I read every cap-using program in `examples/` (50 dirs)
and classified how each uses its capability. Method: `grep -rl "with … as <cap>" examples/` +
`state`/`transaction` (implicit cap), then read each driver body.

**Finding: every corpus cap is used SECOND-CLASS (down), none returns/stores/thunks-out a cap.**

| program | cap idiom | down-only? | (b) rejects? |
|---|---|---|---|
| `state`, `stm`, `effect-op-arith` | `state`/`transaction` handler, `get`/`put` performed in the body | yes | no |
| `logger-silent`, `logger-counting` | `logger.log(_)` performed lexically in the handle body | yes | no |
| `handle-custom-{resume,nested,tracer,abort-coexist}` | cap performed in the handle body | yes | no |
| `echo-mock`, `hostio-echo`, `hostio-fs` | host-effect cap performed in the body | yes | no |
| `fail-parser-{default,strict}`, `json`, `parser-combinators`, `calc`, `tokenizer` | `Fail`/`Trace` cap **passed DOWN as a parameter** (`Cap Fail -> …`), performed in place | yes | no |
| `stage-swap` | cap passed **down through a thunk argument** `($body)(net)`, forced *inside* the handler | yes | no |
| `cap-param`, `cap-param2`, `rpn` (scratch-stranger4) | cap explicitly `: Cap Err` **parameter**, performed in the callee | yes | no |
| **`dst-rounds-const`, `dst-rounds-lcg`** | `sched.bit(s)` performed inside a `let rec go` **recursion DRIVEN INSIDE the handle body** | **yes** | **no** |
| **`sched-{roundrobin,seeded-lcg,swap-dfs}`** | `sched.next(round)` performed inside a `let rec drive` **recursion inside the handle body** | **yes** | **no** |

**The dst-rounds/sched driver was the lead's flagged falsifier** — "it captures a cap in a RECURSIVE
closure passed down." It survives (b): the `sched` cap is bound by the enclosing `handle … with Sched as
sched`, and the recursive driver (`go`/`drive`) is a `let rec` **inside that handle body**. The cap flows
**down** through the recursive calls and is performed lexically within the handler's dynamic extent; it is
**never returned** past the handle, never stored in a data structure that outlives the handler, never put
in a returned thunk. Second-class caps permit exactly "passed/captured downward into computations run
inside the scope" — which is what these drivers do. **Shown** (`examples/dst-rounds-lcg/main.bang`,
`examples/sched-swap-dfs/main.bang`: the `handle … with Sched as sched { … }` lexically encloses the
`let rec` and its `($go)`/`($drive)` calls; the answer of the handle is an `Int`, no cap).

**Census verdict: (b) second-class rejects 0 of 50 corpus programs.** (a) and (c) also reject 0 — but (c)
excludes nothing statically, and (a)'s extra power (returning a scoped-safe cap) is exercised by **0**
corpus programs, so it buys nothing measurable today. The bar is met by (b) at the least cost.

**The one thing (b) forbids that a *hypothetical* program might want:** returning a capability as a
first-class result (`let c = handle … in $(c.op(x))` — the `d3-return-cap.bang` shape). That is **already
refused by the checker today** (`not a value (wrap a computation in braces)`, TypeCheck.lean:1042 —
`scratch/cap-gc/surface-escape/REFUSED-attempts.md`), so second-class *formalizes an existing de-facto
restriction* rather than removing capability from any working program. The genuinely-lost capability is
returning a cap *inside a thunk* for use back under a re-handler — the exact escape shape — which is a
feature no one has asked for and which is unsafe without full rank-2 machinery anyway.

---

## 4 · Design space (a) worked precisely — where the scope variable lives

The lead's crux: bang's kernel has **no ∀** (`IR.lean:240`, `tvar` is a μ-recursion var, not a
∀-variable, ADR-0027). So a `runST`-style rank-2 scope variable cannot live in a kernel type. The
answer, consistent with elaborate-to-mono (ADR-0103, every erased rung): **the scope variable is
surface-only, a phantom the CHECKER threads and ERASES before the kernel.**

```
surface:   handle<s> (body : … Cap<s> Net …) with Net as net { … } : A     — s a fresh scope var
checker:   (1) mint fresh scope tag  s  at each `handle`
           (2) the bound cap gets type  Cap<s> Net  (s = this handle's identity, phantom)
           (3) SIDE CONDITION (avoidance):  s ∉ freeScopes(A)   — A is the handle's result type
           (4) ERASE s → the kernel sees the existing monomorphic  Cap Net  (no ∀ reaches the kernel)
elaborate: unchanged kernel `HasCTy`; the escape is rejected at (3), pre-elaboration
```

This is **CC<:□ avoidance (Prop 3.3) projected to a single scope tag per handle**, and it degenerates:
when the only thing (3) can reject is "a cap of *this* handle's scope appears in the answer," the scope
tag is redundant with the label + the cap former — you do not need a *fresh* `s`, you need "the answer
does not carry `cap ℓ` for the `ℓ` this handler binds." **That degeneration IS candidate (b)**: (b) is
(a) with the scope-variable collapsed to the label the handler already binds. (a) buys back the
generality (multiple live handlers of the same label distinguished by scope, returning scoped caps via
boxing) only when you need it — and the census says you do not, yet.

**So (a) and (b) are the same door at two settings.** (b) = "no fresh scope var, avoidance keyed on the
bound label's cap former"; (a) = "fresh scope var + boxing to tunnel." Ship (b); the (a) generalization
is a *widening* of the same avoidance premise, not a rewrite.

---

## 5 · The LR question — does the typed-LR blockage apply to this door?

The LWT/LWConfig trail (`lwt-config-eager-vs-lazy-cap-obligation`, ADR-0045 R1) established that the
**non-escape discipline is TYPE-DIRECTED**: distinguishing "escaping a vint" (the ledger, safe) from
"escaping a thunk-with-caps" (unsafe) needs the escaping value's TYPE, and the untyped `LWConfig` could
not be preservation-complete for the return-escape fragment "without TYPES" (option (D), build-confirmed
necessary). That blockage was on **PROVING preservation** — the operational `preservation_returnEscape`
obligation genuinely needs the typed LR re-index.

**Does it apply here? Split the two jobs cleanly:**

- **The CHECKER-level surface design (this door): NO, the LR blockage does not apply.** `¬ capOccurs ℓ A`
  is a static premise on a *type* (`A`, the handler's answer VTy) — it is exactly the type-directed check
  the LWT memory said was needed ("a type-premise on `ret`/`letC` constraining only `U φ C` values").
  Adding the premise makes `progEscape` **untypeable** (the answer `U _ (F 1 (cap 1))` carries `cap 1`;
  the premise fails). Untypeable programs never reach preservation — the escape is rejected at
  type-check, so the return-escape preservation obligation *that could not be proven* is **vacated, not
  discharged**. The witness `capOccurs` is that type-directed check, build-checked in §1.

- **PROVING the resulting `type_safety` closes (the metatheory): YES, that still rides the typed LR** —
  but as a *simpler* obligation. With `¬ capOccurs ℓ A` in force, `preservation` no longer needs the
  false `liveCapsResolveC_returnEscape` (ADR-0063) because the laundered-thunk case is untypeable. The LR
  re-index the LWT memory pointed to is still where the proof lands, but the premise makes the hard arm
  *unreachable* rather than needing a true-but-hard lemma. **Suggests** (the checker witness is
  build-sealed; the metatheory theorem is unbuilt): the door *removes* the LR blockage from the checker
  and *shrinks* it in the proof.

**Discipline note (invariant: proof rides the reference).** Landing (b) as a surface checker premise with
NO kernel/`HasCTy` change ships an *earlier fail* (compile-time rejection) with the *same* sound dynamic
semantics behind it (ADR-0063's `escapedCap` stays as the belt-and-braces runtime backstop for any path
the surface checker cannot see — e.g. a cap escaping via a construct the checker under-approximates).
That is the stratification move: the surface checker is the tested-superset guard; `escapedCap` is the
verified-core fail-loud. Ship (b) as the checker; **do not delete `escapedCap`** — it is the floor.

---

## 6 · Interaction with row-attenuation (pledge-as-a-type)

The OS-survey's headline cheap win is **row attenuation**, now shipped as
`pledge {E, …} in body` (ADR-0112 — assert an effect-row ceiling while retaining the body's actual
row). Scoped-cap types and row attenuation are
**orthogonal and complementary**, and the OS-survey already named the split (§4.2 "pledge and unveil are
two syscalls for a reason"):

```
row-attenuation  = pledge  : restricts WHICH effects a computation may perform  (the label/row axis)
handler policy   = runtime : restricts WHICH operation values are admitted       (the value axis)
scoped-cap types = the cap-lifetime discipline : restricts WHERE a cap may FLOW  (the identity axis)
```

Row-attenuation narrows the *static row* (whether the effect); scoped-cap types constrain *cap escape*
(where the handler instance flows). ADR-0113's host-allowlist consumer occupies the third axis:
ordinary handler configuration decides which request values are admitted. They touch different axes
of bang's core principle ("typing by label, dispatch by identity"): attenuation is a label/row
upper-bound; handler policy is a value predicate at dispatch; scoped-caps is an identity-flow bound.
Both are surface-checker, kernel-free, erased rungs. They ship independently: row attenuation has
landed first because the sandboxed-plugin consumer selected it; scoped caps remain the separate
identity-flow mechanism needed to close the #134 *soundness* story.

---

## 7 · Recommendation, cost, and the v1.5-vs-post-v1 call

**Recommend candidate (b), second-class capabilities, as a v1.5 surface-checker door**, with (a) as the
named post-v1 generalization and (c) retained as the runtime floor underneath both.

**The honest v1-vs-later call.** This is **NOT a v1 blocker.** ADR-0063 already ships a *sound, defined,
honest* v1 semantics: the escape is `escapedCap` (a defined fail-loud, OCaml-5-grade), `type_safety`
holds with its frozen text, and the guarantee is stated without a hollow premise. #134 proves the escape
is *surface-reachable*, which sharpens the motivation but does **not** open a v1 soundness hole — it
reaches a *defined* terminal, not genuine `.stuck`. So the timing is:

- **v1: ship (c) as-is** (done). The guarantee: "a well-typed ⊥ program never reaches genuine stuck — it
  returns, diverges, or hits a defined capability-escape fail-loud."
- **v1.5: land (b)** — the `¬ capOccurs ℓ A` handler premise, ~1 session, surface-only, moving the escape
  from *first-run fail-loud* to *compile-time rejection*. This is the correctness-by-construction upgrade:
  the escape becomes **unrepresentable** rather than **detected**. Cost is one premise threaded through
  the handler-typing rules (the shape B-occ already established), plus a differential probe. The census
  guarantees zero legitimate-program regressions.
- **post-v1: (a)** only when returning first-class caps (scoped-safe) becomes a demanded feature — at
  which point build it AS region typing (memory-management-survey M7: one construct, both problems). No
  corpus program demands it; do not pay for it speculatively (invariant #7).

**What buying (b) actually gets, priced against (c):** compile-time vs first-run detection. (c) fails the
`state 0 in {get} in $leaked` program on its first execution with `escapedCap`; (b) fails it at
`bang check`. For an agent-first language (the ergonomics lens), compile-time is materially better — the
error is at the authoring boundary, before any run, with the misused cap named. That is the entire value
(b) adds over (c), and it is worth ~1 session because it is the highest-leverage correctness-by-construction
upgrade available on the cap axis at surface-checker cost.

---

## 8 · Rejected alternatives

- **Full rank-2 / CC<:□ region-capability types NOW (candidate (a) at v1.5).** REJECTED on cost and
  demand: it needs subtyping (the kernel dropped `Qle`), reference-dependent `VTy`, and boxing — ≥ the
  whole inc-5 effort — to buy a generality (returning scoped-safe caps, same-label multi-handler scope
  distinction) that **0** corpus programs exercise. It is the right *post-v1* endpoint (build it as region
  typing), not the right v1.5 spend. §4 shows (b) is its degenerate case, so nothing is lost by deferring.

- **Prove "the cap does not escape" (strengthen B-occ / NonEscape to a proof-invariant).** REJECTED,
  build-impossible (ADR-0063 §Alternatives, restated): the sealed witness `progComp` proves the cap
  **does** escape operationally, so any invariant claiming it cannot is false. The bad program must become
  *untypeable* (candidate (b)/(a)) or *defined-behavior* (candidate (c)) — never "proven-not-to-escape."

- **Delete `escapedCap` once (b) lands.** REJECTED: `escapedCap` is the verified-core runtime floor; the
  surface checker is a tested-superset guard that may under-approximate (a future construct could route a
  cap past the checker's view). Keep both — the stratification seam (§5). Removing the floor would trade a
  belt-and-braces fail-loud for a checker's completeness claim we have not proven.

- **Do nothing beyond (c) forever.** REJECTED as the *endpoint* (accepted as the *v1 floor*): (c) is a
  per-run fail-loud, not static soundness (memory-management-survey §4.4). #134 shows the escape is
  surface-reachable on legal-looking programs; leaving it first-run-only forever forgoes the
  correctness-by-construction upgrade that costs only ~1 session and rejects zero real programs. The honest
  call is "(c) for v1, (b) for v1.5" — not "(c) forever."

---

## 9 · Slice map (for whoever lands (b))

```
S0  witnesses (DONE, this lane) — Bang/Witness/ScopedCapWitness.lean:
      progEscape → .escapedCap · progDown → .done · capOccurs separates them (6 #guards green).
      These are the permanent regression oracles: any (b) impl must keep progEscape UNTYPEABLE
      and progDown TYPEABLE, and capOccurs must stay the discriminator.
S1  surface premise — add `¬ capOccurs ℓ A` to the handler-typing rule(s) in TypeCheck.lean
      (the surface `handle`/`state`/`custom` elaboration), keyed on the bound label's cap former.
      Threads like B-occ (ADR-0057). NO kernel/HasCTy change. Reuse the capOccurs shape from S0.
S2  differential probe (BoccSpike pattern) — build-confirm: (a) progEscape (the #134 shape) now
      REJECTED at `bang check`; (b) all 50 corpus programs still check (the census, mechanized);
      (c) progDown + dst-rounds/sched still check. This is the over-restriction falsifier as a test.
S3  metatheory (typed-LR, hand to proof-engineer) — with the premise in force, re-prove `type_safety`:
      the laundered-thunk preservation arm is now UNREACHABLE (untypeable), vacating the false
      liveCapsResolveC_returnEscape rather than needing a true-but-hard replacement. Rides the ADR-0045
      typed-LR re-index but as a SHRUNK obligation (§5).
S4  ADR — record (b) as the v1.5 cap-escape door: rationale, the census (0 rejections), the rejected
      (a)-now/(c)-forever alternatives, and the forward-compat to (a)=region-typing (M7). Reopens/closes
      the #134 + #50 structural item at the v1.5 tier. Supersedes scoped-capabilities-for-vcapfree-drop.md.
```

Build-confirm S2 before any S4 ratification (the census must be *mechanized*, not eyeballed — the
`capOccurs` witness is the seed but the corpus-wide check is the ratifying artifact).

---

## S1-REFUTED · The `capOccurs`-on-answer-TYPE mechanism does not close the escape

> Finding (2026-07-12, `feat-second-class-caps` lane, task #168). S1 as specified above was
> IMPLEMENTED verbatim (`capOccursIV`/`capOccursIC`, the frontend mirror of `ScopedCapWitness`'s
> own predicate, wired as `¬ capOccurs ℓ B` into `synthSC`'s `.withCapS`/`.handleCustomS` arms) and
> then REFUTED against its own motivating witness before landing. This section records the
> refutation, the root cause of the S0 seal's blind spot, and the syntactic candidate the next
> design pass should formalize — WITH its own falsifier pre-named, so the mistake this section
> documents is not repeated a second time.

**The refutation, mechanized.** `bang check` on all three named refusal witnesses
(`scratch/cap-gc/surface-escape/{b3,c1,d2-sched-capture}.bang` — the `state`, custom-`Log`, and
`Sched` shapes) still returns `ok` with the `¬ capOccurs ℓ B` premise wired into BOTH handler-
typing arms. Debug-traced the actual synthesized answer type at each site: every one carries an
EMPTY row and NO `.cap` former anywhere in its structure (`F(omega, U(φ=[], F(omega, int)))` for
the `c1.bang` custom-effect shape, traced live). The premise never fires because there is nothing
in the TYPE for it to find.

**Root cause, hand-traced through the kernel's own typing judgment** (`Bang/Core/Typing.lean`'s
`HasVTy`/`HasCTy`, NOT run through a prover — a manual derivation, cited by rule name and line):
the ADR-0063 laundering shape's returned thunk (`Val.vthunk Mesc` in `ScopedCapWitness.progEscape`)
captures the outer capability as a FREE DE BRUIJN VARIABLE inside its own computation BODY
(`Comp.perform (Val.vvar 1) "get" …`) — never as a value the THUNK'S OWN TYPE mentions. Per
`HasVTy.vthunk` (`Typing.lean:122`: `HasCTy γ Γ M φ B → HasVTy γ Γ (Val.vthunk M) (VTy.U φ B)`),
the thunk's type is `VTy.U φ B` where `φ`/`B` come from `M`'s (`Mesc`'s) OWN typing — and `Mesc`
RE-HANDLES `state 1` internally, so its OWN `handleState` typing arm's B-occ premise
(`Typing.lean:281`, `¬ LabelOccurs ℓ A`) ALREADY discharges label 1 from `Mesc`'s own answer type
before ANY outer `capOccurs` check ever runs. The label is gone from the row, and the cap was
never a value in the type to begin with — `capOccurs` inspects a type that has genuinely nothing
to find, for the EXACT SAME structural reason bare B-occ was insufficient in the first place (the
whole premise of this design note's own §1 thesis, ironically now shown to defeat its OWN proposed
successor by the identical mechanism). **A capability escape is a FREE-VARIABLE-CAPTURE fact, not
a type-SHAPE fact** — `Thunk T`'s own type says nothing about what `T`'s computation closes over,
by CBPV's own design (the same reason a closure's captured-environment types are erased from an
ordinary function type in any CBPV-based system).

**The S0 seal gap, named precisely** (the probe-methodology lesson worth banking verbatim): **A
PREDICATE SEALED IN ISOLATION IS NOT A SEALED DESIGN — the witness must connect through the real
judgment.** `Bang/Witness/ScopedCapWitness.lean`'s six `#guard`s (§1/§9 S0, marked "DONE") test
`capOccurs`/`cCapOccurs` against HAND-CONSTRUCTED `VTy`/`CTy` VALUES (`capOccurs 1 (VTy.U ⊥ (CTy.F
1 (VTy.cap 1))) = true`, line 125) — illustrative of the PREDICATE's own mechanics, but the file
contains ZERO references to `HasCTy`/`HasVTy` anywhere (grep-confirmed) — `progEscape`'s type is
NEVER actually derived through the kernel's own typing judgment and checked against `capOccurs`.
The `#guard`s prove the predicate CAN flag a cap-former-carrying type; they do not prove
`progEscape`'s type IS one. That gap is exactly what this refutation closes: `progEscape`'s real
derived type (hand-traced above) has no cap former to flag. Any future predicate-based door needs
its OWN witness to be a genuine `HasCTy progEscape e C → capOccurs-or-equivalent-on-C = true`
DERIVATION, not a standalone assertion about a hand-picked `C`.

**The syntactic candidate for the next design pass** (sketch, not built): check the raw `Surf`
tree, not the elaborated TYPE. Does the handler's `body` contain a free reference to the bound cap
name (`name`/`h`) INSIDE a `.thunk` node that ends up in the HANDLE'S OWN answer/return position —
i.e. reachable as the final tail-position value of `body` itself (through `let`-chains, `if`/
`match` arm results, the same positions `checkSC`'s own tail-position arms already enumerate) —
rather than forced lexically within `body`? `surfUsesVar` (`TypeCheck.lean:5687`) already exists
as the free-variable-reference primitive this would need; the harder, NOT-yet-formalized part is
"ends up in answer position OF THE HANDLE" precisely.

**The pre-named falsifier for that candidate** (so the next pass is born already knowing its own
census wall, not discovering it late): the Sched library demo's `Step`-coroutine pattern
(`data Step = Done(Int) | More(Unit -> Step)`, `docs/notes/sched-library-demo.md`) constructs and
RETURNS thunks (`More`'s payload) that carry references to the driving `sched` capability — and
that return is LEGAL, down-flow use (the returned `Step` value is consumed and its `More` thunk
FORCED again entirely WITHIN the SAME `handle … with Sched as sched { … }` block's dynamic extent
— the coroutine never outlives its own handler). A naive "any thunk closing over the cap name that
appears anywhere in a return-reachable position" check would REJECT this legal program, because
the thunk genuinely IS returned as a value inside the handle body — the rejection needs to be
scoped to "escapes the HANDLE's OWN dynamic extent," not "appears in ANY return position of ANY
sub-expression," which the Sched pattern's own internal recursion structurally satisfies (the
returned `More`-thunk is always re-consumed before the outer `handle` itself returns). Formalizing
"answer position OF THE HANDLE, not of an inner function/recursion step" — almost certainly
requiring the discipline to track WHERE (relative to the handle's own extent) a thunk gets forced,
not merely WHETHER it is syntactically returned somewhere — is the precision the next design pass
must nail down before any implementation, on pain of repeating this exact refutation's own lesson
a second time. **Any redesign must clear the 0/50 census INCLUDING this shape** — the census in §3
already lists `sched-{roundrobin,seeded-lcg,swap-dfs}`/`dst-rounds-{const,lcg}` as corpus programs
that must stay accepted; this section makes explicit WHY a naive syntactic tightening would
regress them, which §3's own text names but does not formalize as a falsifier for a NEW mechanism.

**What this means for #168.** The operator's RATIFICATION of the second-class-capability
DISCIPLINE itself stands — the direction is still right, the census (§3) is still the correct
bar, and the runtime C2 stamp (`escapedCap`, ADR-0063) keeps the language sound in the meantime.
Only the ENFORCEMENT MECHANISM (the specific `¬ capOccurs ℓ A` check this section refutes) goes
back for a fresh design pass. `capOccursIV`/`capOccursIC` and their (currently inert) call sites
in `TypeCheck.lean` are landed as `WIP-INFRA` — reusable plumbing (the mirror of `ScopedCapWitness`'s
own predicate, useful if a future mechanism still wants a type-shape sub-check as ONE clause of a
combined test) — not as a working enforcement, and every comment at those sites says so explicitly.

---

## 10 · References

- **Osvald, Essertel, Wu, Alayón, Rompf**, "Gentrification Gone too Far? Affordable 2nd-Class Values for
  Fun and (Co-)Effect", OOPSLA 2016 (`osvald-oopsla16-second-class-values`, added to `refs.bib` this
  lane) — the second-class-values discipline (candidate (b)'s origin): pass down, never return up, via a
  lightweight scope-nesting check (no rank-2 machinery).
- **Brachthäuser, Schuster, Ostermann**, "Effects as Capabilities", OOPSLA 2020
  (`brachthauser-oopsla20-effects-as-capabilities`) — second-class caps for effect HANDLERS (Effekt); the
  handler-native form of (b). Caps cannot be returned/stored ⇒ cannot outlive their handler.
- **Brachthäuser, Schuster, Lee, Boruch-Gruszecki**, "Effects, Capabilities, and Boxes", OOPSLA 2022
  (`brachthauser-oopsla22-effects-capabilities-boxes`) — System C: second-class + `box` (capture set) to
  lift the restriction; the (b)→(a) bridge. A returned/thunk-captured cap is provably un-usable past its
  handler.
- **Boruch-Gruszecki, Brachthäuser, Lee, Lhoták, Odersky**, "Scoped Capabilities for Polymorphic Effects",
  arXiv 2022 (`boruch-gruszecki-22-scoped-capabilities`) — CC<:□, avoidance (Prop 3.3 = candidate (a)'s
  scope-freshness), `cv`-monotonicity = ADR-0060 liveness. The rank-2 endpoint.
- **Xu, Boruch-Gruszecki, Odersky**, "System Capless" (reach capabilities), OOPSLA 2025
  (`boruch-gruszecki-oopsla25-capless-reach-capabilities`) — caps in generic containers (the returned-pair
  reach case `capOccurs` handles in §1). The current Scala capture-checking line.
- **Launchbury & Peyton Jones**, "Lazy Functional State Threads", PLDI 1994 (`launchbury-pldi94-runst`) —
  the `runST` rank-2 region-escape trick candidate (a) instantiates.
- **Tang & Lindley**, "Rows and Capabilities as Modal Effects", POPL 2026
  (`tang-popl26-rows-capabilities-modal-effects`) — unifies row-based (attenuation, §6) and
  capability-based (this note) effect disciplines; the framework making "typing by label, dispatch by
  identity" coherent.

**Repo cross-refs:** ADR-0063 (the escapedCap reclassification + post-v1 scoped-caps mention) ·
ADR-0057 (B-occ, the label-keyed guard (b) generalizes) · ADR-0103 (elaborate-to-mono, the erased-rung
pattern (a)/(b) follow) · ADR-0045 R1 (the typed-LR the §5 metatheory rides) ·
`docs/notes/memory-management-survey.md` §4 (cap-escape ≈ region-escape; M7 = build (a) AS region typing) ·
`docs/notes/os-inspiration-survey.md` §4 (row-attenuation = pledge; §6 orthogonality) ·
`docs/notes/scoped-capabilities-for-vcapfree-drop.md` (archival #18 record — SUPERSEDED here by the
post-ADR-0063 reframe) · `scratch/cap-gc/surface-escape/` (#134 witnesses: b3/c1/d2 reachable, d1/d3
refused) · `Bang/Witness/ScopedCapWitness.lean` (this note's runnable seals).

**refs.bib addition** (the one paper not yet keyed — Osvald/Rompf second-class values):
```
@inproceedings{osvald-oopsla16-second-class-values,
  keywords = {topic:capability-safety role:frontier},
  author  = {Osvald, Leo and Essertel, Gr\'egory and Wu, Xilun and Gonz\'alez Al\'ayon, Lilliam and Rompf, Tiark},
  title   = {Gentrification Gone too Far? Affordable 2nd-Class Values for Fun and (Co-)Effect},
  booktitle = {Proceedings of the ACM on Programming Languages (OOPSLA)},
  year    = 2016,
  doi     = {10.1145/2983990.2984009},
  note    = {The SECOND-CLASS-values discipline: a value can be passed DOWN (arguments) but never
             returned/stored/escaped upward, enforced by a lightweight scope-nesting check (no rank-2
             machinery). The origin of bang's scoped-cap candidate (b) — caps as second-class values
             makes the ADR-0063 laundered-thunk escape UNTYPEABLE at zero corpus cost (the whole corpus
             uses caps down-only; see docs/notes/scoped-cap-types-design.md census). Effect-handler
             realization is brachthauser-oopsla20-effects-as-capabilities (Effekt).},
}
```
