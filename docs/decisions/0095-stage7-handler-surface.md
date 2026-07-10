# ADR-0095 · #44 Stage 7: the handler surface — `handle … with` syntax, the Q38 posture, and the clause calling convention

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: Stages 1–6 landed the kernel arc for user-defined effects (`Handler.custom` rep, one-shot dispatch, the typed custom-handle rule, and the trusted-three census clean through soundness — ADR-0085/0092, ADR-0085 §Stage-6 STATUS `MET`). What remains is Stage 7: the **surface** a user writes and the **end-to-end `bang eval`** that lowers it. The `effect Name { op : A -> B }` half of the declaration surface already landed at Stage 3 (ADR-0092 §Status D1/D2 EXECUTED `844931f`+`88e0f55`); this ADR decides the `handle … with` half. It is also the stress-test the operator deferred Q38 TO (ADR-0093 §Q38-posture: "module-as-file deliberately left no construct to collide with it … run the stress-test THEN") and the decision issue #78 was parked TO (the trait-ops calling-convention fork). **Five decisions, each operator-ruled: (D1) the concrete `handle e with Name { op(arg) => body }` syntax — the Flix/Effekt method-impl clause shape (`def op(args, resume) = body`), recommended over the Koka match-arm and OCaml exception-style forms because it (a) is syntactically identical to a trait `impl` (serving Q38 for free), (b) degrades to v1's ret-shape/one-shot constraint by treating `resume` as an implicitly-tail-called bound name, and (c) grows to multi-shot by loosening the TYPING rule, not changing the surface (rq38 §1 degradation verdict) — **amended D1a (2026-07-10)**: the handled body names the capability via a REQUIRED explicit `as h` binder, `handle e with Name as h { … }`, scoping over the body (the ADR-0070 `state … as name` precedent; implicit-lowercase rejected — silently-shadowing nested same-effect handlers — and the optional-default sugar deferred as purely additive), with the decl-order-dependent label resolved at elaboration into a slot on the Surf constructor so lowering stays `ElabEnv`-free; (D2) the Q38 posture — a SEPARATE `handle` construct now, NOT syntactic convergence with `trait`/`impl`, per the taxonomy's "unify the MACHINERY, keep the surfaces separate until this stress-test rules" (laws-taxonomy §5 caveat) and the census finding that every unification pays at the implementation layer, not the interface (rq38 §2); the interface ALREADY unifies in bang's glossary, so convergence buys nothing and costs the binding-time knob; (D3) the clause calling convention — effects are CURRIED (`op(x) => body` is sugar for a curried clause, `op` performed as `$cap.op arg` curried), decided ONCE with #78's tuple-vs-curried finding in view; the existing trait ops (tuple-style `fn eq(a,b)`, stranger-test-2 §S3 papercut) DIVERGE-documented in v1 and are flagged for convergence to curried in a follow-up (#78 option B), NOT retrofitted here; (D4) the ret-shape restriction (ADR-0092 §D3-as-landed: v1 clause bodies are `ret w`) surfaces as a SPECIFIC diagnostic ("clause body must be a `ret`-shape value in v1; compute-then-return needs binop typing (ADR-0065) + grade surfacing (Q27)") naming the exact entry gate, NOT a bare type error; (D5) resume's surface spelling — IMPLICIT tail-resume in v1 (a clause body that is `ret w` resumes with `w`; no `resume` binder needed), with `resume` RESERVED as a binder name so the explicit `resume(w)` form and the eventual multi-shot first-class `k` (Q22/Q27) slot in without a surface break.** **What Stage 7 does NOT do (explicitly scoped out): the IO prong is ADR-0084's own unit (unblocked BY this stage, not part of it); multi-shot / first-class `k` stays Q22/Q27 (v1 one-shot pin, ADR-0085 D2); param-UPDATE (`put`-like clauses) stays ADR-0092 D5 / ADR-0087 §Open-questions; op-name namespacing end-to-end (`Net.read` dissolving the builtin-name reservation) is named by ADR-0092 §Status as Q34/Q38 module-interface work and rides the module system, not the handler surface.** **Rejected**: the Koka match-arm form (`handle(e){ op(x) -> body }` — reads as exception-handling, obscures the interface-impl framing that serves Q38); the OCaml `effect Op k ->` form (exposes `k` as a first-class binder v1 cannot honor one-shot, and reads as exception matching); syntactic convergence of `handle` with `trait impl` in v1 (the taxonomy's implementation-layer-pays finding says the interface unification is free and the surface convergence is the untested claim — this ADR keeps them separate to KEEP the stress-test honest, not to foreclose it); tuple-style effect clauses matching today's trait ops (would double down on the #78/stranger-test-2 §S3 inconsistency the language should shed, not entrench); an explicit-`k` binder in v1 (ADR-0085 D2 one-shot pin means a visible `k` would over-promise a control the kernel cannot deliver).
- **Depends-on**: 0085 (the coexist custom-handler arc + one-shot v1 pin), 0092 (the typed custom-handle rule + the ret-shape D3 wall + the `effect`-decl surface already landed), 0093 (module-as-file, the Q38-testable-later posture this now runs), 0070 (named-cap surface: `as h` binder + `$h.op` perform — the lowering target already exists)
- **Relates-to**: #44 (Stage 7 of the arc — the surface + e2e eval), #78 (the trait-ops calling-convention fork parked TO this decision — D3 rules it), Q38 (the module≟trait≟effect stress-test — D2 takes the position), Q22/Q27 (multi-shot + resumption grades — D5 leaves the door open, does not enter), Q34 (op-namespacing — the reservation-dissolving fix rides the module interface, out of scope here), ADR-0084 (IO/Net — the first real consumer, unblocked BY this stage), ADR-0065 (binop typing — half the D4 entry gate), `docs/notes/q38-handler-surface-survey.md` (the census + degradation verdict this ADR steals from), `docs/notes/laws-taxonomy.md` §3/§5 (one-theory-three-coats + the machinery-not-surface caveat), `docs/notes/stranger-test-2.md` §S3 (the trait tuple/curried inconsistency real users hit)

## Status

Accepted (2026-07-10, operator ruling: "Adr 95 Approved" — all five decisions as recommended:
D1 Flix/Effekt-shaped `handle e with Name { op(x) => body }` · D2 separate `handle` construct,
machinery-unified surfaces-separate (the Q38 stress-test's answer) · D3 effects CURRIED, trait
ops diverge-documented (#78 half-ruled) · D4 the teaching diagnostic for ret-shape · D5 implicit
tail-resume with `resume` reserved). Implementation = the Stage-7 lane, founded on this ADR +
the s7probe mechanics findings. Originally Proposed same day.

**Amended 2026-07-10 (D1a, operator-ruled):** the s7probe lane surfaced a genuine gap in D1's
own tracer example — the handled body performs via `$net.read`, but nothing bound `net`. Ruled:
a **REQUIRED explicit `as h` capability binder** — `handle e with Name as h { clauses }` — with
`h` scoping over the handled body `e`. See §D1a below for the rationale and rejected
alternatives; the examples in D1 are corrected accordingly. This is exactly the §Revisit-if
channel firing as designed.

- **Layer:** F (frontend — parser + elaborator + error messages) + product docs. Kernel
  untouched by construction (invariant #5): the surface LOWERS to the already-landed
  `Handler.custom` + typed custom-handle rule (ADR-0085 D1, ADR-0092 D3); the five primitives
  never learn the surface exists (the ADR-0075/0088/0091/0093 elaborate-away move, applied
  again). The stratification principle's language leaf — the surface is the tested-not-verified
  edge, checked differentially against the kernel oracle.

## Context

The moat — "a language whose paradigm and runtime are VALUES" (`CLAUDE.md`) — becomes visible
to a user only when they can write their own `effect` and `handle` it end-to-end. The kernel
arc for that is DONE (ADR-0085 §Stage-6 STATUS `MET`; the custom handler dispatches, types, and
rides `preservation`/`progress`/`type_safety` census-clean). The `effect Name { op : A -> B }`
declaration surface ALSO landed (ADR-0092 §Status: D1/D2 EXECUTED on main — decls parse, labels
allocate `ℓ := 4 + declIndex`, the program-derived `EffSig` types performs at user labels,
user labels render in rows). What is left is the OTHER half of ADR-0085 D4's sketch: the
`handle e with Name { … }` surface, and the `bang eval` that lowers a user program to a running
kernel term.

This stage is uniquely load-bearing for TWO parked decisions:

- **Q38** (module ≟ trait ≟ effect — one construct or several?). ADR-0093 §Revisit-if:
  "Stage 7 lands the `effect` declaration surface → run the Q38 stress-test THEN (module-as-file
  deliberately left no construct to collide with it)." The module system was built to leave the
  ground clear for exactly this test. This ADR runs it.
- **#78** (are trait ops callable by name, and by what calling convention?). Issue #78's own
  recommendation: "(C) — park until Stage 7, where the `effect` op surface forces the same
  convention questions; decide both at once." The effect clause surface forces the
  tuple-vs-curried question; D3 decides it for effects and states what happens to trait ops.

The banked design inputs (`docs/notes/q38-handler-surface-survey.md`, the rq38 census;
`docs/notes/laws-taxonomy.md` §3/§5, the one-theory-three-coats framing;
`docs/notes/stranger-test-2.md` §S3, the real-user friction) are the evidence each decision
below cites. The census's own bottom line — **"steal Flix's surface"** and **"unify the
machinery, keep the surfaces separate"** — is the spine of D1 and D2.

## The starting point (what the surface must lower to, already landed)

```
kernel term            Handler.custom : Label → Val → List (OpId × Comp)     (ADR-0085 D1, ADR-0087 rep)
typed rule             handle-custom: clauses typed pointwise, body : opRes ! φ',   (ADR-0092 D3)
                       v1 ret-shape (body = ret w), B-occ anti-escape carried
perform surface        $cap.op arg   (named-cap: as h binder + h.op, identity dispatch)   (ADR-0070)
effect decl surface    effect Net { read : Int -> Int }  →  program-derived EffSig   (ADR-0092 D1/D2, LANDED)
```

The surface this ADR designs is the `handle e with Name { … }` form that BUILDS the
`Handler.custom` value and installs it — nothing more. Everything below it is proven.

## Decision detail

### D1 — the concrete `handle … with` syntax: the Flix/Effekt method-impl clause shape

**Recommendation.** Adopt the method-impl clause shape, `def`-less to match bang's existing
`=>`-arrow clauses:

```
handle e with Net as net {         -- `as net` binds the capability in e (D1a)
  read(x)  => ret (x + 100)        -- one-shot tail-resume: the ret value resumes the continuation
  write(s) => ret unit             -- likewise
}
```

and, for a handler carrying a parameter (the ADR-0025 state mechanism, read-only in v1):

```
handle e with (Counter init 0) as ctr {
  tick(u) => ret (param + 1)       -- `param` names the carried Val; v1 is read-only (ADR-0092 D5 defers update)
}
```

A complete v1 bang program using it (the tracer-bullet the implementation lane targets;
call syntax per D1b — bare `h.op(args)`, NOT `$`-forced):

```
effect Net { read : Int -> Int }         -- the decl surface, already landed (ADR-0092)

let main =
  handle
    (net.read(1)) + (net.read(2))        -- performs through the D1a-bound `net` (D1b call form)
  with Net as net {
    read(n) => ret (n * 10)              -- one-shot, ret-shape (D4/D5)
  }
-- evaluates to (1*10) + (2*10) = 30    -- VERIFIED e2e: examples/handle-custom-tracer
```

**Why this shape** (rq38 §1 "Degradation-to-v1 verdict", the census's sharpest finding):

1. **It is syntactically identical to a trait `impl`.** `handle e with Net { read(x) => body }`
   and `impl Show for Foo { show(x) => body }` are the SAME clause form dialed by binding time —
   which makes Q38's "handler = trait-impl" unification VISIBLE in the syntax, for free
   (rq38 §1, the method-impl family; laws-taxonomy §3, "one mathematical object, three coats").
   This is the payoff D2 then declines to spend prematurely — the shapes rhyme without merging.
2. **It degrades to v1's constraint most gracefully.** `resume` is an ordinary bound name, not a
   keyword, so v1 = "the clause tail-resumes with its `ret` value" (D5) and the SURFACE does not
   change when D5's typing rule later makes `resume` first-class/multi-shot — only the typing
   rule loosens (rq38 §1; ADR-0085 D2's "loosen the typing rule, not the surface").
3. **It matches ADR-0085 D4's own sketch** (`handle e with Net { read(x)=>…, write(x)=>resume(…) }`)
   and Stage-3's landed `effect` decl — the two halves compose into one coherent surface.

**Rejected alternatives** (rq38 §1 census rows + the pattern-match rationale):

- **(A) the Koka match-arm form** — `handle(e){ read(x) -> body }` (or `with` sugar). Reads as
  *exception handling generalized* (the handler is a pattern-match over operations), which
  obscures the interface-impl framing D1 wants and D2 needs visible. Koka's real gift is the
  `fun`/`ctl`/`final ctl` grade markers (rq38 §4) — those are worth stealing FOR Q27, on the
  `effect` decl, but not the base clause shape. Rejected for the base form; noted for the grade
  channel.
- **(B) the OCaml 5 exception-style form** — `match e with | effect Op k -> …`. Exposes `k` as a
  first-class binder, which v1 (one-shot, ADR-0085 D2) cannot honor without over-promising a
  control the kernel does not deliver; and it reads as exception matching, the same framing cost
  as (A). Rejected.

The census verdict is unambiguous (rq38 TL;DR #1): the method-impl family with a named `resume`
is "the ONE that degrades most gracefully to bang's v1 ret-shape constraint AND grows best
toward D5." D1 adopts it.

### D1a — the capability binder: REQUIRED explicit `as h` (post-approval addendum, operator-ruled 2026-07-10)

**The gap** (found by the s7probe lane, the §Revisit-if channel firing as designed): D1's
original tracer example had the handled body perform via `$net.read` with `net` bound nowhere.
This is not optional plumbing — the kernel's core principle is **typing by label, dispatch by
identity** (glossary; ADR-0052 rejected dynamic nearest-label dispatch): the body performs
through a named capability *value*, and nameable caps are what make nested same-effect handlers
expressible at all. Flix needs no cap because it dispatches dynamically by effect name; bang
deliberately does not.

**Ruling.** The grammar is `handle e with Name as h { clauses }` — the `as h` binder is
**mandatory** in v1, and `h` binds in the handled body `e`. Elaboration order: resolve the
effect name and clause-map, install the binder, then elaborate `e` under the extended context
(the binder is textually after `e` but scopes over it — same move as a `where` clause).
This is the ADR-0070 precedent applied unchanged: the built-ins already write
`state init as name in body`; the user surface inherits the same explicit-binder discipline.

**Rejected alternatives:**

- **Implicit lowercase only** (`Net` implicitly binds `net`, matching the original erroneous
  example). Rejected: nested same-effect handlers become inexpressible — the inner handle
  silently shadows the outer, so the surface could not express a program the identity-dispatch
  kernel handles fine. It is also implicit binding, against the explicit-context discipline
  (invariant #6's spirit; the agent-first lens).
- **Optional `as` with a lowercase default.** Rejected for v1: the default is the footgun above
  in disguise, and the sugar is purely ADDITIVE — it can be layered later without breaking any
  explicit-form program, so v1 buys nothing by shipping it now. Not foreclosed.
- **Binder-first restructure** (`handle h : Name { clauses } in e`). Rejected: reverses the
  just-ruled D1 Flix shape for a scoping-presentation benefit the elaboration order already
  delivers.

**Implementation note (ruled with D1a, on s7probe's probe facts):** a user effect's label is
decl-order-dependent and known only post-elaboration, but `lowerC` is a pure structural pass
with no `ElabEnv` (true even on the typed `checkAndLower` path). The ruled mechanism is a
**resolved-label slot on the `handleCustomS` Surf constructor**: elaboration resolves the label
and rewrites it into the tree; lowering stays a pure function of the tree. Pre-elaboration the
slot holds a placeholder; lowering an unresolved slot is a defined loud error. Rejected: threading
`ElabEnv` through every `lowerC` call site (pollutes a structural pass with elaboration state;
the untyped `elaborateToComp` path has no full `ElabEnv` to thread). Probe evidence:
`docs/notes/stage7-elab-probe.md`.

### D1b — corrections from the implementation (2026-07-10, e2e-verified)

Three findings from the implementation lane, recorded at landing (the examples above are
already corrected):

1. **The call syntax in this ADR's original examples was WRONG.** They wrote `$net.read 1`;
   that form does not parse or type — the D1a-bound cap is already a *value*, so `$` would
   force-then-perform on a non-thunk. The correct perform is the **bare parenthesized call**
   `net.read(1)`, exactly ADR-0070's landed `h.op(args)` convention. D3's "curried" describes
   the op's SIGNATURE and its desugaring (`write(k, v)` ⇒ curried), NOT a `$f x`-style
   call-site spelling. Independently confirmed by the first consumer's design lane (ndet, G5).
2. **`with` is now a RESERVED word.** Without reserving it, `pApp`'s application-fold silently
   swallowed `with Name { … }` as an ordinary application chain — no error, wrong tree. The
   reservation is the fix; a program using `with` as an identifier now fails loudly at parse.
3. **The carried param has NO surface-writable binder yet.** D1's `(Counter init 0)` form
   parses and the param is threaded internally (bound under a sentinel), but no clause can
   NAME it from source — the `param` identifier in D1's Counter example is design intent, not
   landed surface. This is the named NEXT SLICE of the handler surface. Priority note from the
   first consumer (ndet/DST, `docs/notes/ndet-dst-design.md` §7): its stateless-seed design
   RETIRED its need for the param binder — the consumer's actual critical-path ask is
   **compute-then-return clause bodies (D4's exit gate: ADR-0065 binop typing + Q27)**, which
   therefore outranks the param-binder slice in the queue.

### D2 — the Q38 posture: a SEPARATE `handle` construct now; unify machinery, not surface

**Recommendation.** Keep `handle`/`effect` as their own surface constructs, distinct from
`trait`/`impl`, in v1. Do NOT converge the syntaxes even though D1 makes them rhyme. This is
the taxonomy's standing verdict made concrete (laws-taxonomy §5 caveat, verbatim):

> "the rq38 census shows surface unifications pay at the implementation layer — so unify the
> MACHINERY (one propagation engine + one law gate), keep `trait`/`effect`/`axis` as separate
> surface declarations until the Stage-7 stress test rules."

**This ADR IS that stress test, and the position it takes is: the machinery is already unified;
the surfaces should stay separate.** Two grounds, both from the banked census:

1. **The interface unifies for free; every attempt PAID at the implementation layer** (rq38 §2,
   the unification table). 1ML unified modules≡functions and paid in *inference* (undecidable →
   annotate). Effekt unified effects≡capabilities and paid in *first-class-ness* (caps 2nd-class).
   bang has ALREADY unified the interface — its own glossary says "a handler is a value
   implementing an effect's operations; a trait impl is a value implementing a trait's operations"
   (the same sentence) — and has ALREADY paid the predicted prices: the answer-grade wall
   (ADR-0092 D3, currency #1) and the cap-escape arc (ADR-0063, currency #2). So **surface
   convergence buys nothing bang doesn't already have, and the one thing it would have to prove —
   that the binding-time knob (static trait-resolution vs dynamic handler-install) fits on ONE
   resolution story — is the exact claim NO shipped language has demonstrated together with the
   row/label discipline bang commits to** (rq38 §2 verdict-shape).

2. **The semantic unification is already fixed; the surface split loses nothing** (laws-taxonomy
   §3). Plotkin–Power: effects ARE algebraic theories, handlers ARE their algebras; a trait is
   the same theory with a data carrier, a module the same signature with no laws. "Whatever
   surface Stage 7 picks, the SEMANTIC unification is already fixed." Keeping the surfaces
   separate does not re-fork the semantics — it keeps the binding-time knob (the load-bearing
   difference) EXPLICIT rather than hidden behind a merged syntax that would have to disambiguate
   it anyway.

The verdict-shape the evidence points to (rq38 §2, and Tang & Lindley POPL'26 "Rows and
Capabilities as Modal Effects", refs.bib) is **"one interface construct, two modalities
(static/label vs dynamic/capability) dialed by binding-time + grade — NOT one flat construct,
and NOT four separate ones."** bang's already-committed typing-by-label / dispatch-by-identity
architecture IS that graded-modal split. D2's position — separate surfaces over unified
machinery — is the faithful surface for that architecture: the modalities are visibly different
constructs BECAUSE they are different modalities, not despite it.

**Rejected alternatives:**

- **Syntactic convergence of `handle` with `trait impl` in v1** (one construct, dialed by a
  keyword). Rejected: it spends the interface-unification payoff on an UNTESTED claim (that the
  binding-time knob fits one resolution story) precisely when the census says that claim is the
  load-bearing risk. It would ALSO force the op-namespacing (Q34) and grade-channel (Q27) work
  to land together with the surface, coupling three deferred questions into one. Keeping the
  surfaces separate keeps them independently schedulable. NOT foreclosed — if a future stress
  test shows the knob fits cleanly, convergence becomes a surface refactor over the same
  machinery (the same "later refactor once the risk is proven" shape as ADR-0085 D5).
- **Four fully-separate constructs with no shared machinery** (the Unison "keep separate on
  purpose" arm, rq38 §2). Rejected the other direction: bang has ALREADY unified the machinery
  (the graded-row engine, the law gate, `EffSig` as the shared interface) and would throw that
  away. The position is unify-machinery / separate-surface, not separate-everything.

### D3 — the clause calling convention: effects are CURRIED; trait ops diverge-documented

**Recommendation.** Effect operations are **curried**, matching the rest of the language. A
clause `read(n) => body` is surface sugar for a single-parameter curried clause; a two-argument
op `write(k, v)` desugars to a curried `write(k) => fun v => …` at the elaborator, and the
perform site is curried too (`$net.write key val`, not `$net.write (key, val)`). This decides
#78's fork (2) — "the calling-convention inconsistency" — ONCE, for effects.

**What happens to trait ops** (#78's explicit ask — "decide ONCE for effects, traits follow or
diverge-documented"): trait ops today are TUPLE-style (`fn eq(a, b)`, applied `eq(3, 4)` as one
pair — ADR-0068, confirmed by stranger-test-2 §S3 as a real papercut: "the rest of the language
is curried … but a trait op is declared `fn eq(a, b)`"). In v1, effects are curried and trait
ops STAY tuple-style — a **documented divergence**, flagged loudly in the reference and NOT
silently inconsistent. The convergence (making trait ops curried too, #78 option B's
`.app`-shaped resolution path) is a SEPARATE follow-up, because it is kernel-adjacent (an
elaboration rule mirroring the `.binopS` arm, ADR-0068) and entangled with #78's fork (1) —
trait ops callable by name at all — which is its own decision. Coupling the trait-op refactor
into this surface ADR would drag a kernel-adjacent change into a frontend-leaf unit.

**Why curried for effects** (and why not follow the trait precedent):

- The perform surface is ALREADY curried — `$cap.op arg` (ADR-0070 named-cap: `as h` binder +
  `$h.op` perform). Making the clause tuple-style would mean the DECLARATION and USE sites of the
  same op disagree on shape — the exact inconsistency stranger-test-2 §S3 flagged for traits, now
  avoided for effects by construction.
- Curried is the language's ground convention (`fun x => …`, `$f x`, effect op typed
  `Int -> Int`). Effects are new surface; they should be BORN consistent, not inherit the trait
  ops' historical tuple shape. The agent-first lens (ride conventions unless semantics is novel —
  memory `agent-first-ergonomics-lens`) says a new construct matches the dominant pattern.

**Rejected alternatives:**

- **Tuple-style effect clauses** (`read(n)` as one pair-arg, matching today's trait ops).
  Rejected: entrenches the #78/stranger-test-2 §S3 inconsistency the language should shed. The
  clause `read(n)` LOOKS like a paren-call but is really a curried single binder; the paren is
  grouping/readability sugar, not a tuple — the elaborator treats `op(a, b) =>` as curried
  `op a b =>`.
- **Deciding trait ops in this ADR** (retrofit them to curried here). Rejected: #78 fork (1)
  (name-callability) and fork (2) (convention) are entangled and kernel-adjacent; this is a
  frontend-leaf surface ADR. D3 rules the convention for the NEW construct (effects) and names
  the trait convergence as a separate, sequenced follow-up — the honest scope boundary.

### D4 — how the ret-shape restriction surfaces: a specific diagnostic, not a bare type error

**The constraint** (ADR-0092 §D3-as-landed): v1 custom clause bodies must be the RETURN shape
`ret w` (a `HasVTy` premise). This is forced by the answer-GRADE wall — the perform's returner
grade is free, a general body's grade is structure-pinned, and no re-grading lemma exists
(ADR-0092 D3, evidenced by three committed probes). A clause like `read(n) => ($net.read (n+1))`
(compute-then-return, effectful body) does NOT type in v1.

**Recommendation.** When a clause body is not `ret`-shaped, emit a SPECIFIC diagnostic that
names the constraint AND the documented path to the general form, not a bare "type mismatch":

```
error: handler clause body must be a `ret`-shape value in v1
   in `read(n) => <body>`
   v1 clause bodies return a value directly (`ret w`); a compute-then-return body
   is not yet typeable. This needs binop typing (ADR-0065) + resumption-grade
   surfacing (Q27) — tracked as the general-body entry gate. See the handler
   reference § "v1 clause restriction".
```

This rides the project's fail-loud invariant and the stranger-test finding that **"parser error
messages double as a teaching tool"** (stranger-test-2 §Strengths — a user with zero docs
reconstructed the trait grammar from the error messages). The diagnostic teaches the fix and
names the exact ADRs (0065 + Q27) that constitute the entry gate, so a user (or agent) hitting
the wall knows precisely what has to land for the general form — it is a *scoped restriction with
a named exit*, not a mysterious rejection.

**The documented path to the general form** (ADR-0092 D3, verbatim): the compound entry gate is
**binop typing (ADR-0065) + grade surfacing (Q27)**. Until both land, the flagship
compute-then-return clause stays untyped-fragment-only. The diagnostic points there.

**Rejected alternatives:**

- **A bare type-mismatch error** (the elaborator's generic "expected `ret A`, got …"). Rejected:
  it does not name the v1 restriction as a restriction, so a user reads it as "my program is
  wrong" rather than "this form is deferred" — the difference between a papercut and a teaching
  moment (stranger-test-2 §S3 is exactly the papercut version for traits). Fail-loud means loud
  AND specific.
- **Silently accepting the clause and failing later** (at the machine, or with a stuck term).
  Rejected outright by invariant #1 (proof rides the reference) and the fail-loud principle — a
  clause the type system cannot honor must be rejected at check time, at the clause, with the
  reason.

### D5 — resume's surface spelling: implicit tail-resume in v1, `resume` reserved for the future

**Recommendation.** In v1, resumption is IMPLICIT: a clause whose body is `ret w` (D4) resumes
the captured continuation with `w`. There is NO `resume` binder in v1 clause bodies — the
`ret`-shape body IS the resume value (mirroring the built-ins' identity return-clauses, ADR-0092
D3). BUT `resume` is a RESERVED binder name (a user effect may not declare an op named `resume`,
nor bind it), so the explicit form slots in without a surface break:

```
v1 (implicit):     read(n) => ret (n * 10)              -- ret value = the resume value
future (explicit): read(n) => resume (n * 10)           -- `resume` first-class; tail position in one-shot,
                                                          -- multi-shot when Q22/Q27 land
```

**Why implicit-with-reserved-name** (rq38 §1 continuation-appearance ladder + ADR-0085 D2):

- v1 is one-shot tail-resumptive (ADR-0085 D2, the load-bearing scope pin). The implicit form is
  the honest surface for that: there is nothing to name because the continuation is invoked
  exactly once, at the tail, with the `ret` value. Frank and Koka's `fun` clauses do exactly this
  — "no `k` in source; compiles to a stack frame" (rq38 §1 ladder, IMPLICIT tail row).
- Reserving `resume` means the spelling does NOT foreclose the hybrid future (rq38 TL;DR #1:
  "`resume` is an ordinary bound name, so v1 hardcodes tail-call `resume` at the end while the
  syntax is already ready for the day `resume` becomes first-class"). When Q22 (closure cap-rep)
  + Q27 (resumption grades) land, `resume(w)` becomes a bound name the clause may invoke — one-
  shot in tail position first, then multi-shot when the grade admits it (the rq22 ω-channel
  future, Q27's `fun`/`ctl` distinction). The surface grows by ADDING the explicit form, never by
  breaking the implicit one.
- This matches the grade channel D1's rejected-Koka-note reserves: Koka's `fun` (implicit tail) /
  `ctl` (named `resume`, general) split (rq38 §4) is exactly the v1-implicit → future-explicit
  ladder, dialed by the operation's declared grade at the `effect` decl. v1 = all `fun`; the
  `resume` reservation is what lets `ctl` land later without a surface break.

**Rejected alternatives:**

- **An explicit `k` binder in v1** (`read(n, k) => k (n*10)`, OCaml-style). Rejected: v1 is
  one-shot (ADR-0085 D2); a first-class `k` the user can name promises a control (store it,
  invoke it twice) the kernel cannot deliver until Q22. Surfacing `k` would over-promise — the
  same over-promise D1 rejected the OCaml form for. Implicit tail is the surface that matches the
  actual one-shot semantics.
- **No reserved name at all** (let users name an op or binder `resume`). Rejected: it would force
  a breaking surface change when the explicit form lands (a program using `resume` as an op name
  would collide). Reserving it now (elaboration-only, zero runtime cost — the same move ADR-0092
  §Status made for builtin op names) keeps the future free.

## What Stage 7 does NOT do (explicit scope boundary)

```
concern                      status                        owner / gate
──────────────────────────────────────────────────────────────────────────────────────
IO / Net effect              UNBLOCKED BY, not part of     ADR-0084's own unit (its {Net} handler
                             this stage                    is the first real consumer of D1's surface)
multi-shot / first-class k   DEFERRED                      Q22 (closure cap-rep) + Q27 (grades);
                                                           D5 reserves `resume` so it lands cleanly
param-UPDATE (put-like)      DEFERRED                      ADR-0092 D5 / ADR-0087 §Open-questions;
                                                           v1 clauses are read-only param (D1 `param`)
op-namespacing (Net.read)    DEFERRED                      Q34/Q38 module interface (ADR-0092 §Status);
                             — dissolves the ADR-0092       rides the module system, NOT this surface
                             builtin-name reservation
trait-op convention          DIVERGE-documented in v1      #78 fork (1)+(2) — a separate follow-up
convergence                                                (kernel-adjacent, D3 names it)
```

The Net effect (ADR-0084) is the sharpest confirmation this ADR's surface is right-sized: ADR-0084
gated its genuine `{Net}` effect on #44 (ADR-0085 §Context), and D1's `handle e with Net { read(x)
=> … }` is EXACTLY the surface an ADR-0084 IO handler installs. Stage 7 opens the door; ADR-0084
walks through it — as its own unit.

## Invariant compliance

- **#5 (five primitives):** the surface LOWERS to the already-landed `Handler.custom` (a fourth
  constructor of the existing handler primitive, ADR-0085 D1) via the elaborate-away move — no
  kernel change, no sixth primitive. The parser/elaborator own the `handle … with` form; the
  kernel never learns it exists (ADR-0093 §Layer, fourth application of ADR-0075/0088/0091).
- **#1 (proof rides the reference):** the e2e `bang eval` of a user program is diff-tested against
  `Source.eval` (the kernel oracle) — the same differential-#guard discipline ADR-0093's v1 oracle
  uses (`elaborate(surface) ≡ the hand-built kernel term`). No execution path ships without the
  oracle behind it. The tracer-bullet program (`main = handle … with Net { read(n) => ret (n*10) }`
  → 30) is the first such #guard.
- **#6 (no implicit capture; reactivity is the operator):** the `handle … with` form installs a
  handler explicitly at the use site — the "runtime is a handler installed at the use site" thesis
  made surface-visible (ADR-0093 D5's manifest framing). Nothing captures implicitly.

## Revisit if

- The implementation lane (s7probe) finds the `handle … with` elaboration needs a surface shape
  D1 did not anticipate (e.g. multi-op clause-map parsing collides with block syntax) → surface
  the obligation; D1's method-impl shape is the design intent it refines FROM (the same
  "sketch-stands-as-intent" clause ADR-0092 D3 used).
- Q22 (closure cap-rep) + Q27 (resumption grades) resolve → D5's `resume` reservation activates:
  add the explicit `resume(w)` form and the `fun`/`ctl` grade markers on the `effect` decl (the
  Koka split, rq38 §4), one-shot-tail first then multi-shot. Surface grows additively.
- ADR-0084 lands IO → the first real `handle e with Net { … }` consumer exercises D1 end-to-end;
  the capability-manifest checking (main's row ⊇ what the runtime provides, ADR-0093 D5) lands
  with it.
- A future stress test shows the binding-time knob fits ONE resolution story cleanly → D2's
  separate-surface position becomes a candidate convergence refactor over the same machinery
  (the ADR-0085 D5 "collapse once the risk is proven" shape). NOT foreclosed by v1.
- #78 fork (1) (trait ops callable by name) gets ruled → D3's trait-op convergence-to-curried
  lands with it (the follow-up D3 named).

## Evidence

`docs/notes/q38-handler-surface-survey.md` (rq38: §1 the handler-surface census + degradation
verdict — "steal Flix's surface, method-impl clause shape degrades most gracefully"; §2 the
unification table — "interface unifies for free, every attempt pays at the implementation layer";
§4 the grade-as-dial thesis — Koka `fun`/`ctl`, Tang POPL'24, the future D5 grows into);
`docs/notes/laws-taxonomy.md` §3 (one-theory-three-coats — Plotkin–Power, "semantic unification
already fixed, whatever surface Stage 7 picks") + §5 (the machinery-not-surface caveat, verbatim —
"unify the MACHINERY, keep the surfaces separate until this stress test rules");
`docs/notes/stranger-test-2.md` §S3 (the trait tuple/curried inconsistency real users hit) +
§Strengths (error-messages-as-teaching-tool, the D4 rationale); ADR-0085 (the coexist arc +
one-shot D2 pin + §Stage-6 STATUS `MET`); ADR-0092 (the typed custom-handle rule + the ret-shape
D3 wall + the `effect`-decl surface LANDED); ADR-0093 (module-as-file, the Q38-testable-later
posture this runs); ADR-0070 (the named-cap perform surface D1 lowers onto); issue #78 (the
trait-ops calling-convention fork D3 rules); ADR-0084 (the IO consumer unblocked BY this stage).
