<!-- note-status: active -->
# Handler surface + the module≟trait≟effect unification — empirical design inputs (Q38 / Stage-7)

> Research lane (rq38), 2026-07-09. Docs-only; no production code. Empirical inputs for TWO coupled
> upcoming forks: **(a)** Stage-7's `handle … with { … }` surface syntax (ADR-0085 D4), and **(b)** the
> **Q38 stress-test** — is module ≟ trait ≟ effect ≟ capability ONE interface+implementation construct
> dialed by resumption grade, or separate constructs? The operator's directive on (b) is
> **stress-test, don't decide**; this doc is the evidence table for that test, not a verdict.
> Companion to [[Q38]] (the axes table + grade-as-dial insight), [[Q27]] (the three-channel grade
> proposal), ADR-0085/ADR-0092 (the landed reality that CONSTRAINS what the surface can promise).

## TL;DR (the three sharpest findings)

1. **Steal Flix's surface.** `eff Name { def op(args): Ret }` + `run { … } with handler Name { def op(args, resume) = … }`
   is a near-exact match for ADR-0085 D4's sketch, and its **method-impl clause shape (`def op(…, resume) = …`)
   is the ONE that degrades most gracefully to bang's v1 ret-shape constraint AND grows best toward D5**:
   `resume` is an ordinary bound name, so v1 hardcodes "tail-call `resume` at the end" while the syntax is
   already ready for the day `resume` becomes first-class (multi-shot). Koka's `fun`/`ctl` split is the
   thing to steal *for Q27* (grade-at-the-clause); Flix is the thing to steal *for the clause body shape*.

2. **The unification is real but the interface≠implementation split is where every attempt paid.** TWO
   shipped languages unified across the boundary bang is asking about — **1ML** (modules≡functions≡functors,
   one construct) and **Frank** (functions≡handlers, one "operator"). Both UNIFIED THE INTERFACE cleanly.
   1ML's cost was **inference: unification forced impredicative System-F, whose inference is undecidable, so
   quantifier intro/elim must be programmer-annotated.** That is *the same wall* ADR-0092 D3 already hit from
   the effect side (the answer-GRADE wall → v1 ret-shape-only clauses). Convergent evidence: **the interface
   unifies for free; the implementation (continuation access / grade / inference) is the load-bearing seam.**

3. **The grade-as-dial thesis has shipped prior art AND a soundness proof.** Koka SHIPS resumption-grade-at-
   the-clause (`fun`=tail/one-shot, `ctl`=general, `final ctl`=abort) and compiles the cheap path off it —
   that IS the operator's 0/1/ω channel, per-operation, declared at the effect decl. Tang et al's *Soundly
   Handling Linearity* (already in refs.bib) is the PROOF that tracking resumption-multiplicity in types is
   sound — and its **ML-variant (Qeffpop) infers control-flow linearity with zero annotations**, which is
   the escape hatch from 1ML's annotation cost. The operator's "resumption grade = QTT grade of the `k`
   binder" (Q27 input) is exactly what Tang formalizes as control-flow linearity. **The thesis is not a
   fantasy — it is shipped (Koka) and proven-sound (Tang).**

---

## 1. The handler-surface census

What each language's `handle`/`with` actually looks like, how clauses read, how the continuation appears, and
how handler STATE (parameterized handlers) is expressed. Sources per row in the Sources list.

```
lang       handle-syntax                         clause shape          continuation           handler state
─────────────────────────────────────────────────────────────────────────────────────────────────────────────
Koka       handle(action){ <op-clauses> }        match-arm per op      IMPLICIT (fun) or       via `var`
           or `with` sugar                       (fun/ctl/final ctl)   named `resume` (ctl)    (local mutable
                                                                        — grade AT the clause    in handler scope)
Effekt     try { … } with Cap { def op(x)=… }    method-impl (def)     `resume(v)` keyword,    2nd-class caps;
                                                  named capability      2nd-class (can't escape) state via passing
Unison     handle e with handlerFn               `cases`: match the    explicit `k`, applied   thread state as a
                                                  Request ADT           by recursive handler-   handler-fn PARAM
                                                  ({State.get -> k})    fn call (multi-shot)    (recursion arg)
OCaml 5    match e with | effect Op k -> …        exception-style       explicit `k`,           no built-in; encode
           (effc record in Effect.Deep)          match-arm             `continue k v` /         in the match / refs
                                                                        `discontinue`; ONE-SHOT
Eff        with h handle e                        match-arm, ops `#Op`  explicit `k`, `k! v`    parameterized
                                                                        (multi-shot)            handlers (Pretnar)
Frank      NO handle keyword — an "operator"      operator = pattern    IMPLICIT (direct-style  none needed (an
           IS a function that pattern-matches     match incl. command   call applies k);        operator threading
           commands: `f <p> = …`                  patterns AND values   MULTIhandler over args   a value is a fn)
Flix       run { … } with handler E { def op     method-impl (def),     named `resume`,          (not first-class;
           (args, resume) = … }                   resume is a PARAM      `resume(v)`; Void ops   encode via closure)
                                                                        = non-resumable/abort
bang v1    handle e   /   state e0 in e   /       (kernel: built-in     one-shot tail-resume    state = carried Val
(reality)  atomically e; ADR-0085 D4 sketch:      triple; custom =      IMPLICIT in v1 (D2);    param (D2); D5 param-
           handle e with Net { read(x)=>… }       a clause MAP)         `resume` reserved       UPDATE deferred
```

**Two clause-shape families:**
- **match-arm** (Koka, Unison, OCaml, Eff): the handler is a *pattern match* over operations/requests; reads
  like exception handling generalized. Natural when handlers are values you match against.
- **method-impl** (Effekt, Flix): the handler is a *record of `def op(…) = …`*; reads like an interface
  implementation — **literally the same shape as a trait `impl`.** This is the shape that makes Q38's
  "handler = trait-impl" visible *in the syntax*, not just in the semantics.

**Continuation-appearance ladder** (this is the axis that determines the compile, per Q27):
```
  IMPLICIT tail (Koka fun, Frank, bang v1)   → no k in source; compiles to a stack frame (cheap)
  named resume, one-shot (Effekt, Flix)      → resume(v) once; one-shot machine, no copy
  named k, one-shot enforced (OCaml 5)       → continue k v; runtime error on 2nd use
  named k/resume, MULTI-shot (Unison, Eff,   → k is first-class, copyable; heap resumable closure
    Koka ctl)                                   (expensive — the Q22 cap-rep fork bang deferred)
```

**Degradation-to-v1 verdict (research Q1's core ask).** bang v1 clauses are **ret-shape, one-shot tail-
resumptive** (ADR-0092 D3: the answer-grade wall forces `ret w` bodies). The syntax that degrades to this
*most gracefully* while growing best toward D5 is **the method-impl family with a named `resume` (Flix /
Effekt)**, because:
- `resume` as an ordinary bound name means v1 = "the clause must tail-call `resume` (implicitly, or the
  elaborator inserts it)"; the *surface doesn't change* when D5 makes `resume` first-class/multi-shot —
  only the typing rule loosens. Koka's `fun`/`ctl` split is the same idea one level up (the grade is on the
  *operation kind*, not just implicit).
- The method-impl shape **is** the trait-impl shape (`def op(args) = body`), so it directly serves Q38's
  unification: a `handle e with Net { def read(x) = … }` and an `impl Show for Foo { def show(x) = … }` are
  the SAME surface form dialed by binding-time — which is exactly the stress-test's hypothesis made visual.

Koka's `fun`/`ctl`/`final ctl` is the single most valuable thing to *additionally* steal, but for Q27 (the
grade channel), not for the base clause shape — see §4.

---

## 2. The unification question, empirically

Did any shipped language unify effects with typeclasses/traits/modules into ONE construct? **Yes — two did,
across the two halves of Q38's boundary — and the failure modes are the evidence the stress-test needs.**

```
attempt          what it unified                  UNIFIED cleanly?   what it COST / what broke        lesson for bang
──────────────────────────────────────────────────────────────────────────────────────────────────────────────────────
1ML              modules ≡ functions ≡ functors   YES at interface   inference: forced impredicative  unifying the INTERFACE is
(Rossberg '15)   ≡ type constructors (one          (structures =      System-F ⟹ UNDECIDABLE inference free; the cost lands on
                 first-class construct)            records = tuples)  ⟹ quantifier intro/elim must be   INFERENCE. Exactly ADR-0092
                                                                      programmer-ANNOTATED, never       D3's answer-grade wall,
                                                                      inferred. DM-inference "not       seen from the module side.
                                                                      complete."
Frank            functions ≡ handlers (the         YES — no `handle`  gave up: a separate handler       the effect-side unification
(Lindley '17)    "operator"; a fn is an operator   keyword at all;    construct. KEPT: implicit-only    WORKS if you accept implicit
                 handling no commands)             multihandlers      continuation (direct-style tail-  tail-resume as the default.
                                                   over many args     apply). Multi-shot needs care.    bang v1 = a Frank operator.
Effekt           effects ≡ capabilities ≡          YES — effects      gave up: FIRST-CLASS functions.   the unification is bought by
(Brachthäuser)   type-class dictionaries (all      compile to cap/    caps are 2nd-CLASS (can't be      the 2nd-class restriction —
                 capability-passing)               dictionary passing returned/stored) ⟹ can't outlive  bang's cap-escape arc
                                                                      handler. Escape = a type error.   (ADR-0063) is the same trade.
Scala 3          typeclasses ≡ givens; Caprese     PARTIAL — givens   capture-checking (caprese) is     the DUAL of bang's rows:
givens+Caprese   adds capabilities/capture-        are the typeclass  still experimental; scaling to    Scala tracks caps in the
                 checking on top                   mechanism, caps a  the collections library was the   VALUE's type (capture set),
                                                   separate track     named blocker. NOT one construct.  bang tracks them in the ROW.
Koka             row-effects unify exceptions,     effects unify (one within effects only — does NOT     effects-as-one-construct is
(Leijen)         state, iterators, async as ONE    row mechanism)     unify with typeclasses/modules.   settled prior art; the
                 effect mechanism                                     Overloading is a SEPARATE feature. cross-boundary unify is not.
Unison           deliberately did NOT unify —      N/A (chose         no typeclasses AT ALL (abilities   a data point AGAINST forced
abilities        abilities kept separate; no       separation)        only). The "keep separate" arm    unification: a shipped lang
                 typeclasses in the language                          of the stress-test.               chose the split on purpose.
```

**The verdict-shape the evidence points to (for the stress-test, NOT a decision):**

> **Unify the INTERFACE; keep the IMPLEMENTATION seam explicit and grade-dialed.** Every attempt that
> unified the *signature+interface* layer succeeded (1ML, Frank, Effekt, bang's own glossary already says
> "a handler is a value implementing an effect's operations; a trait impl is a value implementing a trait's
> operations" — the same sentence). Every attempt PAID at the *implementation* layer, and paid in one of
> three currencies:
> - **inference** (1ML: undecidable ⟹ annotate),
> - **first-class-ness** (Effekt: caps 2nd-class ⟹ can't escape),
> - **a residual separate mechanism** (Scala: caprese ≠ givens; Koka: overloading ≠ effects).
>
> This maps DIRECTLY onto bang's landed reality: ADR-0085/0092 already unified the *performer* interface
> (`EffSig` types any op at any label — "EffSig already IS the user-effect interface") and already PAID at
> the implementation layer in currency #1 (the answer-grade wall ⟹ v1 ret-shape clauses) and currency #2
> (the cap-escape arc, ADR-0063, is Effekt's 2nd-class trade). **bang is not choosing whether to pay — it
> is already paying the exact prices the literature predicts.** The stress-test's real question is narrower
> than "one construct or four": it is **"does the binding-time axis (static trait-resolution vs dynamic
> handler-install) fit as a KNOB on the shared interface, or does it force a second resolution story?"** —
> and on THAT, the evidence is: Effekt/Frank say it fits (capability-passing subsumes both); 1ML says the
> price is inference; nobody has unified it WITH the row/label discipline bang commits to except the very
> recent **Tang & Lindley "Rows and Capabilities as Modal Effects"** (POPL'26, already in refs.bib), which
> shows rows (Koka, ≈ bang's typing-by-label) and capabilities (Effekt, ≈ bang's dispatch-by-identity) are
> **two modalities of ONE calculus.** That paper is the closest thing to a proof that bang's own
> "typing-by-label / dispatch-by-identity" split is the coherent unification, not an ad-hoc pairing.

---

## 3. Parameterized handlers (feeds ADR-0092 D5 — the param-update protocol)

The pair-return protocol vs first-class handler state — what the literature says each costs.

```
option                        mechanism                              cost / when it's needed
────────────────────────────────────────────────────────────────────────────────────────────────
Plotkin–Pretnar               deep handler + a state value THREADED  the classic; tail-resumptive by
parameterized handlers        through the fold over the computation  construction. This IS bang's v1
                              tree (the handler carries a param)      state/txn mechanism (ADR-0025).
                                                                      NO first-class k needed.
Koka `var` (local state)      mutable local in the handler scope;    cheap; but it's IMPERATIVE state,
                              primitive state, tail-resumptive        not the functional param-thread.
                              (Xie–Leijen)                            Sound because tail-resumptive.
Frank adjustments             the ambient ability set is ADJUSTED    subsumes state as an ability the
                              per-operator; state = a threaded arg    operator threads; no separate
                                                                      "handler state" concept.
pair-return protocol          the clause returns (result, newParam); explicit; the ADR-0087 §Open-Qs
(bang D5 candidate)           the machine threads newParam to the     candidate for `put`-like ops.
                              next resume                             READ-only param (v1) needs none
                                                                      of this — Net/read is the case.
```

**Input for ADR-0092 D5.** bang v1 already IS a Plotkin–Pretnar parameterized handler (the carried `Val`
param, ADR-0025). The literature's clear message: **read-only param (v1) is the free case** (every language
does it tail-resumptively with no first-class continuation); **param-UPDATE (`put`-like) is where you choose**
between (a) the pair-return protocol (explicit, bang's named D5 candidate) and (b) Koka-style primitive
mutable `var` (cheaper, imperative, still sound BECAUSE tail-resumptive). The cost is NOT continuation
machinery — both stay one-shot tail-resumptive; the cost is only the threading protocol. **Recommendation
for the D5 ADR: the pair-return protocol keeps the functional/calculated-machine story clean (a pure
`param → (result, param)` step derives a machine arm the Bahr–Hutton way); Koka's `var` would import
imperative state the kernel doesn't have.** Defer either until a `put`-like effect actually needs it (Net/
read doesn't — ADR-0092 D5 already scopes this out correctly).

---

## 4. The grade-as-dial thesis — prior art for tracking resumption multiplicity in types

Does any system track resumption multiplicity (0/1/ω) in types? **Yes, and it's both shipped and proven.**

```
system                        tracks resumption grade?          how close to operator's 0/1/ω channel?
────────────────────────────────────────────────────────────────────────────────────────────────────────
Koka fun/ctl/final ctl        YES — per-OPERATION shape,         VERY close. `fun`=1 (tail), `ctl`=ω
(SHIPPED)                     declared at the effect decl;       (general k), `final ctl`=0 (abort). It's
                              licenses the cheap compile         per-op not per-channel, but same content:
                              (fun ops = no continuation copy)    the grade is DECLARED, and it drives the
                                                                  compile. This is the operator's thesis,
                                                                  SHIPPED. Steal this for Q27.
OCaml 5 one-shot conts        PARTIAL — enforces grade ≤ 1 at    the "1" channel, dynamically enforced.
(SHIPPED)                     RUNTIME (2nd resume = exn), not     No 0/ω distinction in types. A weaker
                              in types                            (runtime) version of the dial.
Tang et al, "Soundly          YES — PROVEN sound. Control-flow   CLOSEST to the operator's Q27 input.
Handling Linearity"           linearity tracks how many times    "control-flow-linear context = entered
(POPL'24, IN refs.bib)        control ENTERS a context (exactly  exactly once" = grade-1; "unlimited" = ω.
                              once vs unlimited); continuations   Two variants: F-style (annotated) and
                              used per the linearity of captured  ML-style Qeffpop (ZERO annotations,
                              resources. Fixed a real Links bug.  inferred). The inference escape hatch.
Frank adjustments             NO explicit multiplicity — but     the implicit-tail default is grade-1 by
                              the direct-style default IS grade-1 construction; multi-shot is the deviation.
Granule / QTT (IN refs.bib)   YES for VALUES (0/1/ω use-count),  the SAME rig the operator proposes reusing
                              not for resumption per se           for the k-binder. "resumption grade = QTT
                                                                  grade of the k binder" = literally this.
```

**The operator's thesis, checked against the literature (Q27 input, 2026-07-09):**

> *"Resumption grade = the QTT grade of the continuation binder."* — This is **exactly** what Tang et al
> formalize as **control-flow linearity**, and it is SOUND (they proved it, fixing a Links bug). The operator's
> "same rig grades every other binding — no third mechanism" is precisely Tang's move (linearity and effects
> both via qualified types) and Granule's rig reused for the k-binder. **The thesis is not speculative — it is
> the POPL'24 result.** Two concrete gifts for bang:
> 1. **The ML-variant (Qeffpop) infers control-flow linearity with ZERO annotations.** This is the escape from
>    1ML's annotation cost (§2): bang need NOT make users write grades if it adopts the qualified-types
>    inference. (Caveat bang must weigh: inference-of-grade is HARD — design-space-map already flags this, and
>    ADR-0066's ω-default is the pragmatic floor. Qeffpop shows it's POSSIBLE, not that it's cheap.)
> 2. **Koka SHIPS the declaration form** (`fun`/`ctl`/`final ctl`). If bang surfaces the grade per-operation at
>    the `effect` decl (Q27's operator input #2: "grade is intrinsically per-handler ⟹ declare it"), it matches
>    a shipped design, and the empty-ω-channel statically licenses the cheap labelling cap-rep + one-shot
>    machine (the Q22 fork bang deferred) — the exact compiler seam Q27 already names.

**On the THREE-channel display (Q27 operator input #2).** `A ! { aborts: throws | uses: state,Net | forks: amb }`
partitions the row by the handled effect's declared grade. No shipped language displays the row this way
(Koka annotates per-operation, not per-channel), but it is a *display* projection of Koka's per-op grades —
sound as sugar, and (as Q27 notes) the ω-channel is empty by construction until multi-shot lands, so it can
ship as declaration/display sugar before it constrains anything. **This is a bang original with a shipped
substrate (Koka's per-op grades) underneath it.**

---

## 5. Reserved-names check (research Q5)

How do other languages handle user ops shadowing builtin op names? **Namespacing is universal; bang v1's
reserve-the-builtin-names is a deliberate temporary restriction with a known correct fix.**

```
language     mechanism for op-name collision
──────────────────────────────────────────────────────────────────────────────────────
Koka         qualified names per module/effect: `file/read` vs `list/map`; type-directed
             overload resolution picks the unambiguous one automatically. NO reservation —
             every op is namespaced by its effect/module.
Flix/Effekt  ops are members of a named effect/capability (`E.op`); the effect name IS the
             namespace. Collision impossible by construction.
Unison       abilities namespace their constructors (`State.get`, `State.put`).
OCaml/Eff    effects are constructors in scope; ordinary ML shadowing/module-qualification.
bang v1      RESERVES builtin op names (get/put/raise/new/read/write) — a user `effect` may
             NOT declare an op with a builtin name (LOUD error; ADR-0092 D1 landed finding
             (ii)). capOpSig is the single source of truth.
```

**Verdict:** bang v1's reservation is the ODD ONE OUT — every other language NAMESPACES ops by their
effect/label (`Effect.op` / `label/op`) rather than reserving a flat global set. ADR-0092 already names the
correct fix ("namespacing ops by label end-to-end") and correctly DEFERS it to the Q34/Q38 module-interface
work. **This is a direct Q38/Q34 input: the module-interface construct should give every effect/trait/module
its own op namespace (the `Effect.op` form), which dissolves the reservation entirely.** The reservation is a
scaffolding restriction, not a design position — the census confirms per-label namespacing is the universal,
correct end-state.

---

## ADR-INPUTS

### For the Stage-7 handler-surface syntax ADR (builds on ADR-0085 D4)

1. **Adopt the Flix/Effekt method-impl clause shape** `handle e with Name { def op(args, resume) = body }`
   (or the `=>` arrow bang already uses in D4's sketch). Rationale: (a) it degrades to v1's ret-shape/one-
   shot constraint by treating `resume` as an implicitly-tail-called bound name; (b) it grows to D5/multi-
   shot by loosening the typing rule, NOT changing the surface; (c) it is *syntactically identical* to a
   trait `impl` (`def op(args) = body`), which serves the Q38 unification for free. Avoid OCaml's exception-
   style `effect Op k ->` (reads as exception-handling, obscures the interface-impl framing).
2. **Steal Koka's `fun`/`ctl`/`final ctl` grade markers for the Q27 channel** — put the resumption grade on
   the operation declaration in the `effect` decl (per-op), not on the handler clause. v1 = all `fun`
   (tail/one-shot); `final ctl` (abort) is already expressible (bang's `throws` = zero-shot); `ctl` (multi-
   shot) stays a parse-but-reject-in-typechecker placeholder until Q22/Q27 land (the empty-ω-channel).
3. **`resume` is a reserved binder in clause bodies** (like Flix/Effekt), NOT a general keyword; v1 inserts
   the tail-call implicitly (matching the built-ins' identity return-clauses) OR requires an explicit
   `resume(w)` that must be in tail position. Either is consistent with the D3 ret-shape ruling.
4. **Give every effect its own op namespace** (`Net.read`, not a global `read`) so ADR-0092's builtin-name
   reservation dissolves — the census shows this is universal. Ties Q34 (module system) directly.

### For the Q38 verdict (the stress-test — evidence, not a decision)

1. **The interface unifies for free; run the stress-test at the IMPLEMENTATION layer.** bang's own glossary
   already unifies the interface ("a value implementing an effect's/trait's operations"). The empirical
   evidence (§2) is unanimous that the *signature* layer unifies; the load-bearing question is whether the
   binding-time knob (static trait-resolution vs dynamic handler-install) fits on ONE resolution story.
2. **The price is already predicted and already being paid.** 1ML → inference (bang paid it: the answer-grade
   wall, ADR-0092 D3, v1 ret-shape). Effekt → 2nd-class caps (bang paid it: cap-escape arc, ADR-0063).
   The stress-test should CHECK bang against these two prices, not re-discover them.
3. **Tang & Lindley "Rows and Capabilities as Modal Effects" (POPL'26, refs.bib) is the theoretical spine**
   for the unification bang actually wants: rows (typing-by-label) and capabilities (dispatch-by-identity) as
   two modalities of one calculus. If the Q38 stress-test wants a *proof* the split is coherent, that paper
   is it. The verdict-SHAPE the evidence points to: **one interface construct, two modalities (static/label
   vs dynamic/capability) dialed by binding-time + grade — NOT one flat construct, and NOT four separate
   ones.** A "graded modal" unification, matching bang's already-committed typing-by-label/dispatch-by-
   identity architecture.
4. **The grade-as-dial is the strongest arm of the unification** and it is shipped (Koka) + proven (Tang).
   Q27's three-channel display is a bang original with a real substrate. This is the part of Q38 LEAST at
   risk — build it.

## Sources

Local refs.bib (verified on-disk): `tang-popl24-soundly-handling-linearity`, `tang-popl26-rows-capabilities-modal-effects`,
`brachthauser-oopsla20-effects-as-capabilities`, `brachthauser-oopsla22-effects-capabilities-boxes`,
`orchard-icfp19-granule`, `xie-icfp21-generalized-evidence-passing`, and the three registered this lane:
`lindley-icfp17-do-be-do-be-do` (Frank), `rossberg-icfp15-1ml` (1ML), `leijen-esop14-koka-row-effects` (Koka).

Web (2026-07-09):
- [Algebraic Handler Lookup in Koka, Eff, OCaml, and Unison](https://interjectedfuture.com/algebraic-handler-lookup-in-koka-eff-ocaml-and-unison/) — the four-language handle-syntax comparison
- [Koka book](https://koka-lang.github.io/koka/doc/book.html) + [Koka docs](https://koka-community.github.io/koka-docs/koka-docs.kk.html) — `fun`/`ctl`/`final ctl`
- [Effekt: Effect Handlers](https://effekt-lang.org/docs/concepts/effect-handlers) — try/with, `resume`, second-class caps
- [Unison: Abilities and ability handlers](https://www.unison-lang.org/docs/language-reference/abilities-and-ability-handlers/) — `handle … with`, `cases`, Request ADT
- [OCaml 5 Effect handlers manual](https://ocaml.org/manual/5.5/effects.html) — `match … with effect`, `continue`/`discontinue`, one-shot
- [Flix: Effects and Handlers](https://doc.flix.dev/effects-and-handlers.html) — `eff`, `run { } with handler`, `def op(args, resume)`
- [Do Be Do Be Do (Frank)](https://arxiv.org/abs/1611.09259) — operators unify functions + handlers
- [1ML — Core and Modules United](https://people.mpi-sws.org/~rossberg/1ml/) — modules ≡ functions, undecidable-inference cost
- [Soundly Handling Linearity](https://arxiv.org/abs/2307.09383) — control-flow linearity, Qeffpop zero-annotation inference
