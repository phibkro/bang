<!-- note-status: active -->
# The algebra of effects and the effect-side lambda cube — design survey (R-series companion to R6)

> The operator's questions (2026-07-11): *can handlers depend on / return / resume effects (recursive
> handlers, state-effect-as-handler-memory)? · does stack allocation even need to be an effect if only
> escaping memory needs tracking? · what is the algebra of effects and handlers? · does the term→type→kind
> lambda cube apply to the algebra of **computations** (possible comps) instead of **values** (possible
> vals)?* This is the **computation-side twin** of R6 (`lambda-cube-ascent-survey.md`, the value side): R6
> asked how far the SURFACE climbs the value cube while the kernel stays ∀-free; this note asks the same of
> the EFFECT axis, and grounds every question on the repo's actual walls (the D4 ret-shape gate, D5
> param-update, the escapedCap/region seam). **ADR-input note, not an ADR.** Theoretical frame:
> `effects-vs-cic.md` (CBPV as the synthesis), `laws-taxonomy.md` (effects = algebraic theories),
> `kernel-substrate-survey.md` §2a (the grade family). Every bang claim is `file:line` or ADR; web in §Refs.

## 0 · The four verdicts, one line each

```
Q1/Q3  handlers-perform-effects       the higher-order-effects LADDER exists (forwarding < parameterised <
       (recursive/HO effects)         bidirectional < scoped/hefty); bang sits at rung 1 (forwarding, SHIPPED)
                                       with rung 2 (param) named as D5; the D4 wall IS "handler clause bodies
                                       cannot perform" — Q1 is that wall, not a new discovery. State-as-handler-
                                       memory = the SAME mechanism as D5 param-update, not a different one.
Q2     stack-alloc-as-effect          the operator's "only escapers need tracking, at return/resumption" is
                                       TRUE and literature-held (2nd-class values, Koka st<h>); an allocation
                                       EFFECT does NOT earn its place — CBPV already makes it structural.
Q4     the effect cube                 "λ-cube over computations" is an ANALOGY transported along U⊣F, not
                                       Barendregt's theorem; the three effect axes are real (∀ρ rows · effect
                                       operators · value-indexed effects) and bang occupies the bottom corner
                                       (row-poly, SHIPPED) — the same erased-ceiling/typed-floor shape as R6.
Verdict CTR needs rung 1 only          nothing here re-sequences D4/D5; the higher-order ladder is the map that
                                       PLACES them (D4 = clause-body-effects = rung-2-entry; D5 = param = the
                                       handler-memory face of the same rung). One roadmap consequence (§Verdict).
```

---

## 1 · §The algebra — theories, models, homomorphisms mapped onto bang's kernel

The settled account (Plotkin–Power; Plotkin–Pretnar): **an effect is an algebraic theory** (operations +
equations); **a handler is a model** (an algebra) of that theory; **handling is the unique homomorphism**
from the free model (the computation tree) to the handler's carrier. `laws-taxonomy.md` §3 already pins this
for bang ("effects ARE algebraic theories, handlers ARE their algebras — not analogy, Plotkin–Power"). The
one-table map onto the frozen kernel objects (`IR.lean:113/139`):

```
 algebra concept              bang kernel object                              cite
 ──────────────────────────   ─────────────────────────────────────────────  ───────────────────────
 signature (operations)       EffSig.opArg/opRes (per-label op types)         ADR-0092 D2; parametric
 a theory (ops + equations)   a Label + its ops; equations = the effect's     laws-taxonomy §3; state's
   "the effect"                 laws (state: get-get/get-put/put-get/put-put)   4 eqns are the theory
 the free model (comp tree)   Comp (the description; "programs are             IR.lean:113; ADR-0007
   "syntax before semantics"    descriptions until forced", ADR-0007)
 a model / algebra            a Handler value (state/throws/transaction/       IR.lean:139-168
   (carrier + op interps)       custom ℓ p clauses)
 the handling homomorphism    Source.eval's handle/dispatch fold              Dispatch.lean:130-183
 equations HOLD in a model    a handler law-checked vs its theory (bang test) laws-taxonomy §3 (post-S7)
```

The load-bearing subtlety bang already lives (glossary): **typing is by LABEL, dispatch is by IDENTITY.** In
algebra terms, the *label* is the theory (which signature/equations), the *identity* `n` is *which model
instance* — many models of one theory coexist on the stack, and `splitAtId` (`Dispatch.lean:78`) selects the
instance by identity. This is exactly the **tunneling / lexically-scoped-handler** semantics (Zhang–Myers
POPL'19; Zhang–Salvaneschi–Myers OOPSLA'20 §4.2): a handler handles only effects it is "locally aware" of;
others *tunnel through*. bang's identity-keyed `splitAtId` walking *past* non-matching frames **is** tunneling
— forwarding-through-a-frame already exists in the kernel (the abort-coexist example: a `raise` forwards
THROUGH a custom frame because the custom frame's identity ≠ the throws cap's identity).

## 2 · §Q1+Q3 — the higher-order-effects ladder, and where bang is on it

"Can handlers depend on / return / resume effects?" is the **higher-order effects** question, and the field
has a precise four-rung ladder. Each rung is "how much may a handler CLAUSE BODY do beyond return a value":

```
 rung  name                     what the CLAUSE BODY may do                 prior art                bang status
 ────  ──────────────────────   ─────────────────────────────────────────  ──────────────────────   ─────────────────
 0     pure return              return a value; resume tail-position         all systems               SHIPPED (D2/D3)
 1     FORWARDING               perform effects that TUNNEL to OUTER          Koka row-poly forward;    SHIPPED — splitAtId
       (handler is effect-        handlers (not its own resumption)            Zhang–Myers tunneling     tunnels; abort-
        polymorphic)                                                           [zhang-popl19]            coexist example
 2     PARAMETERISED            carry + UPDATE a state param across            Plotkin–Pretnar param.    NAMED = D5 (param-
       (handler memory)          resumes (get/put-as-handler-memory)          handlers [plotkin-esop09] update; deferred)
 3     BIDIRECTIONAL            RAISE a further effect BACK to the perform    Zhang–Salvaneschi–Myers   NOT in v1 (post-v1;
       (handler raises)          site; a handler may handle its OWN effects   [zhang-oopsla20]          the D4 wall's far side)
 4     SCOPED / HEFTY           operations that DELIMIT a sub-computation     Wu–Schrijvers–Hinze       NOT in v1 (research;
       (higher-order ops)        (once/catch/local) — ops take COMPS as args  [wu-haskell14]; hefty     needs a kernel HO-op
                                                                              [poulsen-popl23]          former — an ADR)
```

**The sharpest finding: Q1 is the D4 ret-shape wall, not a new question.** The operator's "can handlers
perform effects" is *exactly* the gate `ctr-design.md` already pins: v1 `HasClauses` requires a clause body
`= Comp.ret w` (`Typing.lean:346`), so a clause body that *performs* is untypeable in the kernel. That is the
boundary between **rung 1 (forwarding, which bang HAS — the perform tunnels to an outer handler, no kernel
typing of the clause body needed because the outer handler owns it)** and **rung 2+ (the clause body itself
is an effectful computation the KERNEL must type)**. So:

- **Forwarding (rung 1) is SHIPPED and needs no lift.** A user handler whose clause `perform`s an effect it
  does not itself handle already works: `splitAtId` tunnels the inner perform past this frame to the enclosing
  handler (`Dispatch.lean:78-84`; the abort-coexist example is the built-in witness). This is Koka's
  "polymorphic handler forwards unknown ops" ([leijen-koka]) realized by identity-dispatch.
- **Rung 2 (parameterised = handler memory) is D5, and state-effect-as-handler-memory is the SAME
  mechanism.** The operator's idea — "the state effect could be used for handler memory" — is precisely
  Plotkin–Pretnar **parameterised handlers**: a handler threads a carried value, `get`/`put` read/replace it.
  bang's built-in `state`/`transaction` arms ALREADY do this (`Dispatch.lean:133-164`: `put` reinstalls the
  frame carrying the new value); the `custom` arm reinstalls the param **unchanged** (`Dispatch.lean:177-181`,
  "v1 is a READ-ONLY param"). **`memory-management-survey.md` §1.2 already reached this verdict**: mutable
  user-handler = the D5 param-update slice = the `state`-arm's `s ↦ v` swap generalized to `custom`. So
  state-effect-as-handler-memory is **not a different mechanism — it is D5**, and it is a *typing* cost (the
  answer-grade wall, `ctr-design.md` §2.3), not a semantic one (the reinstall already exists). **Recursive
  effects** (an effect whose op signatures mention the effect itself) are a red herring at rung 2: handler
  memory does not need the effect to be recursive — it needs the param to be *updatable*, which is D5.
- **Rung 3 (bidirectional = handlers RAISE effects to the perform site) is the operator's "can handlers
  return or resume effects" in its strong form, and it is genuinely post-v1.** Zhang–Salvaneschi–Myers
  ([zhang-oopsla20]) generalize an effect operation to declare a **`raises` clause** — "further effects its
  handling code may raise" — so the *perform site* must handle the reverse effects, and a **`self` handler**
  lets a handler "ask that its own effects be handled by itself" (a fixpoint). This is the precise formal
  content of "handlers return/resume effects." It rides the SAME tunneling/lexical-scope semantics bang
  already uses (their §4.2 = bang's dispatch-by-identity), so bang is *architecturally compatible* — but it
  needs (a) effectful clause bodies (past the D4 wall) AND (b) op signatures that carry a reverse-effect row.
  Correctly deferred.
- **Rung 4 (scoped/hefty) is a kernel-former question.** Scoped operations (`once`, `catch`, `local`) take a
  *computation* as an argument and delimit it (Wu–Schrijvers–Hinze [wu-haskell14]); hefty algebras
  ([poulsen-popl23]) give the modular **elaboration** of higher-order ops into first-order algebraic ops +
  handlers. The 2024 reconstruction (Matache–Lindley–Moss–Staton–Wu–Yang, [matache-oopsla24]) shows scoped
  effects = **parameterized algebraic theories where scopes are RESOURCES with open/close operations** — the
  same shape as file handles or regions (§Q2's connection). bang's kernel has no higher-order-op former
  (`perform : Val → OpId → Val → Comp`, `IR.lean:123` — the op arg is a *value*, not a computation). Adding
  one is a spec change (invariant #5) — an ADR, not a v1 concern. The hefty result matters as the *escape
  hatch*: HO-ops **elaborate away** into first-order ops (the elaborate-to-mono move, R6's spine), so bang
  could host scoped ops at the SURFACE via elaboration without a kernel former — the same trick R6 uses for
  the value cube. **This is the one genuinely new roadmap input** (§Verdict).

**Handler-memory verdict:** state-effect-as-handler-memory and D5 param-update are the **same mechanism** (a
parameterised handler threading an updated carried value) — one thing from two sides, not a unification
opportunity (`memory-management-survey.md` M1 files it); a typing wall (answer-grade), not a semantic one.

## 3 · §Q2 — does stack allocation need to be an effect?

The operator's claim, made precise: *"only memory that outlives its scope needs tracking, and if that is
exclusively allowed at return or resumption then it becomes the continuation's responsibility."* **This is
TRUE, it is literature-held, and it means an allocation EFFECT does NOT earn its place — CBPV already makes
the property structural.**

The evidence, three converging sources:

```
 source                          the position (= the operator's claim)                          cite
 ─────────────────────────────   ────────────────────────────────────────────────────────────  ─────────────────
 2nd-class values                a value stays STACK-allocated for its whole lifetime UNLESS it   [osvald-oopsla16],
   (Osvald; Xhebraj–Rompf)         ESCAPES (returned / stored / captured); escape is exactly       [xhebraj-ecoop22]
                                    "outlives its syntactic scope" → only then heap. Tracking =
                                    a scope/privilege level, a TYPE qualifier, not an effect.
 Koka st<h> heap effect          the st<h> effect is AUTOMATICALLY DISCHARGED (removed from the    [leijen-koka]
                                    row) "whenever it can prove no mutable reference escapes" —
                                    escape-analysis erases the effect at the seam.
 CBPV stack discipline            "a value is, a computation does"; values are stack-passed; the   `effects-vs-cic.md`;
   (Levy; the env machine)         ONLY value that outlives its frame is a thunk/closure            EnvMachine.lean:81
                                    (`mvclos M ρ`). Everything else is LIFO, dies at frame pop.
```

`memory-management-survey.md` §2.1 already draws this line in bang's own code: **the sole heap escaper is the
closure** (`EnvMachine.lean:81-82`, "the ONLY constructor that captures the env is `vthunk M ↦ mvclos M ρ`");
values, let-results, handler frames, and effect stores are all stack-disciplined (`:160-168`). So the
operator's "escape only at return/resumption" is the CBPV structure itself: a value escapes a frame **iff** it
is returned into an outer continuation (or captured in a thunk that is). The continuation *is* where escape
happens — the operator's "continuation's responsibility" is exact.

**Verdict: an allocation effect is NOT earned.** The information it would carry ("does this escape") is
**already structural in CBPV** (thunk = escaper, everything else = stack), so a row label on allocation would
be discharged at every non-escaping frame pop (Koka's `st<h>` auto-discharge) — empty exactly where the value
doesn't escape, i.e. almost everywhere. Where a finer dial is wanted it belongs on the **R (region) grade
axis** (`kernel-substrate-survey.md` §2a; `memory-management-survey.md` M6: regions = handler scopes) — a
*coeffect* the type system folds, NOT a sixth primitive and NOT a row label. This *confirms*
`memory-management-survey.md`'s "no memory subsystem — CBPV IS one" thesis; the operator's phrasing is its
CBPV justification. **The one residue:** a *capability* captured in a thunk that outlives its handler is the
escape the structure does NOT catch by construction (escapedCap, ADR-0063) — a *region-typing* job
(`memory-management-survey.md` §4), not an allocation-effect one.

## 4 · §Q4 — THE CUBE over computations

The operator: *"does the term→type→kind lambda cube apply to the algebra of effects instead of types — the
lambda cube applied to computations instead of values, possible comps instead of possible vals?"* **Honest
answer: it is an ANALOGY transported along the U⊣F adjunction, not literally Barendregt's cube — but the
analogy is precise and productive, and it names three real effect axes.** Take the phrasing seriously and it
resolves cleanly; assert it as a theorem and it breaks.

**Not literally the λ-cube.** Barendregt's cube classifies *type* formers over a *value* calculus by three
*dependency* axes (∀/System-F, type-operators/Fω, Π/dependent). The effect side has no "kind" former in that
sense — it has a family of *grades* (`laws-taxonomy.md` §5) indexing computations. There is no functor from
Barendregt's cube to an "effect cube"; the correspondence is an **analogy**, and calling it a theorem is the
exact over-claim R6 warns against. **But it is precise:** in CBPV types classify VALUES and rows/grades
classify COMPUTATIONS, joined by `U`/`F` (`effects-vs-cic.md`), and the three "effect-cube" axes are the three
ways a computation type is *abstracted* — each with a settled name:

```
 λ-cube axis (VALUES)         effect-cube axis (COMPUTATIONS)          the mechanism           bang status
 ──────────────────────────   ─────────────────────────────────────   ─────────────────────   ─────────────────────
 λ2  ∀ over types (System F)  ∀ over EFFECT ROWS (row polymorphism)    a grade/row VARIABLE     SHIPPED — EffRow.tail
                                "comp polymorphic in its effects"        (Katsumata graded       (Option RVar) +
                                                                         monad [katsumata14])     unify + MGU
                                                                                                  (EffectRow.lean:51,155)
 λω  type operators (Fω)      EFFECT OPERATORS / effect constructors   a grade indexed by a     ERASED — no kernel
                                (an effect parameterized by an effect     TYPE/effect; category-  effect-operator former;
                                 or type: Koka effect<a>)                 graded monad             surface elaborates
                                                                          [orchard-graded-param]   (R6's kinds-as-arity)
 λP  Π: types over terms      effects indexed by VALUES (parameterised  Atkey parameterised /    ERASED / research —
     (dependent)                monads: pre/post state, session/         indexed monad            no value-indexed row;
                                 protocol conformance)                    [atkey-param-monad]      the P grade axis
```

The unification (Orchard–Wadler–Eades, [orchard-graded-param]): **graded monads** (indexed by a *monoid* —
effect quantity, bang's row) and **parameterised monads** (indexed by *pre/post values* — Atkey, session
types) are BOTH special cases of **category-graded monads** (indexed by *morphisms of a category*). So the
"effect cube" is really: *how is the computation-classifier indexed?* — by a monoid element (grade/row), by a
value (parameterised), or by a morphism (the unification). That is the honest content of "possible comps
instead of possible vals": the value cube abstracts *type* formers; the effect cube abstracts *how
computations are graded* — the same three abstraction moves (variable, operator, value-index), one adjunction
apart.

**Which corner bang occupies.** Bang sits at the **λ2-analog (row-polymorphism, SHIPPED)** — `EffRow` carries
a polymorphic tail variable with unification + principality (`EffectRow.lean:51,155`) — with the λω/λP-analogs
(effect-operators, value-indexed protocol effects) as *surface-erased* grade axes (`kernel-substrate-survey.md`
§2a). The effect cube's verdict mirrors R6's **verbatim: the surface climbs, the kernel stays grade-mono, and
the "typed" guarantee is a floor (the row), not a full-cube surface.** The diagram:

```
        effect-cube CORNER            bang          transported-R6 reading
        ──────────────────────        ──────        ─────────────────────────────────────
        (row-mono, ⊥)                 KERNEL         the λ→-floor of the effect axis (grade-mono)
        + ∀ρ (row-poly)               SHIPPED        λ2-analog — the ONE typed climb (EffRow.tail)
        + effect-operators            ERASED         λω-analog — elaborate-to-mono (grade family)
        + value-indexed (protocol)    RESEARCH       λP-analog — the P grade axis, post-v1, erased
        + bidirectional/scoped ops    RESEARCH       the HO-op formers (§Q1 rungs 3-4) — kernel ADR
```

## 5 · §Verdict — load-bearing for the ROADMAP

**Which rung of the higher-order ladder does the CTR gate actually need?** Rung 2's *typing*, and only that.
`ctr-design.md` already pins G1 (the ndet DST consumer) as a **⊥-row, `binop`-only** clause body — a *pure*
compute-then-return, which is rung-1-to-rung-2 *at the kernel-typing layer only* (the body computes but
performs nothing). So the CTR exit gate needs the D4 kernel-typing carve-out (ADR-0065 ④ + a ⊥-row
`HasClauses` arm), **NOT** rungs 3-4 (bidirectional/scoped) and **NOT** even rung 2's *semantics* (param
update = D5, orthogonal to G1). This survey **confirms `ctr-design.md`'s sequencing and adds the map that
places it**: D4 (effectful clause bodies) = the rung-1→rung-2 boundary; D5 (param update) = the handler-memory
face of rung 2; both are strictly below rung 3 (bidirectional), which is where "handlers return/resume
effects" in the strong sense lives. **Nothing here re-sequences D4/D5.**

**The one genuinely new roadmap input:** the **hefty-algebras elaboration result** ([poulsen-popl23]) — that
higher-order/scoped ops **elaborate away** into first-order algebraic ops + handlers — means bang's
elaborate-to-mono thesis (R6's spine) extends to the EFFECT axis: **scoped operations (`once`/`catch`/`local`)
could be a SURFACE feature via elaboration, with NO kernel higher-order-op former** (invariant #5 intact),
exactly as R6's value cube climbs by elaboration. This is an ADR-input worth filing when scoped ops are
demanded (they are not on the current roadmap; the ndet DST story needs only ⊥-row bodies).

**ADR-inputs (present, don't decide):**

```
 # ADR-input                                                              rung / when            rides
 ── ─────────────────────────────────────────────────────────────────    ──────────────────     ──────────────────────
 EA1 Forwarding is rung 1 and SHIPPED — a user handler whose clause       v1 LANDED              splitAtId tunneling
     performs a tunneling (outer-handled) effect already works.                                   (Dispatch.lean:78)
 EA2 State-effect-as-handler-memory ≡ D5 param-update (ONE mechanism,     v1.x (gated on the     memory-survey M1;
     not two) — a typing cost, not a semantic one.                        answer-grade wall)      Dispatch.lean:137/181
 EA3 Stack-alloc is NOT an effect — CBPV makes escape structural;         v1 (structural) /       memory-survey M6;
     the finer dial is the R region grade, post-v1.                       post-v1 (R grade)       EnvMachine.lean:81
 EA4 The effect cube is a transported analogy (U⊣F), not a theorem;       framing (adopt) /       EffectRow.lean:51;
     bang occupies row-poly (λ2-analog, SHIPPED); effect-operators +      P axis post-v1          kernel-substrate §2a
     value-indexing elaborate/erase (λω/λP-analogs) — R6's shape.
 EA5 Scoped/HO ops (rung 4) can be a SURFACE feature via hefty-style      research (when          R6 elaborate-to-mono;
     elaboration — no kernel HO-op former needed (invariant #5).          scoped ops demanded)    poulsen-popl23
 EA6 Bidirectional effects (rung 3, "handlers raise effects") ride        post-v1 (past D4 +      zhang-oopsla20;
     bang's tunneling/dispatch-by-identity — architecturally compatible,   a reverse-effect row)   ctr-design D4 wall
     needs effectful clause bodies + reverse-effect op signatures.
```

**Proposed OPEN_QUESTIONS entries (not filed):** (a) "Should scoped/higher-order operations be a surface
elaboration (hefty) rather than a kernel former?" — the EA5 fork. (b) "Do value-indexed (protocol/session)
effects earn the P grade axis, or elaborate to sums like R6's finite-index dependency?" — the λP-analog fork,
paralleling R6 probe 3. Neither is on the critical path; both are the effect-side twins of R6's deferred
value-cube questions.

**Do NOT pre-empt Q38.** This note maps the *algebra* (theory/model/homomorphism) and the *cube*; it does not
rule on whether trait/effect/module unify into one surface construct — that is Q38's stress-test
(`q38-handler-surface-survey.md`), and its verdict-shape ("unify the interface, keep the implementation seam
grade-dialed") is untouched here.

---

## References

External — `[NEW]` = add to `refs.bib`; others already present (verified on-disk):

- Plotkin & Pretnar, "Handlers of Algebraic Effects", ESOP 2009 — handler = model of a theory (§1).
  `plotkin-esop09` (via ADR-0025). · Plotkin & Power, "Algebraic Operations and Generic Effects", ACS 2003
  — effects = algebraic theories (§1). `plotkin-power`.
- Zhang & Myers, "Abstraction-Safe Effect Handlers via Tunneling", POPL 2019
  (<https://doi.org/10.1145/3290318>) — tunneling = lexically-scoped handlers = bang's dispatch-by-identity
  (§1). `[NEW] zhang-popl19-tunneling`.
- Zhang, Salvaneschi & Myers, "Handling Bidirectional Control Flow", OOPSLA 2020
  (<https://doi.org/10.1145/3428207>) — rung 3: an op's `raises` clause + `self` handler = handlers raise
  effects to the perform site (§2). `[NEW] zhang-oopsla20-bidirectional`.
- Wu, Schrijvers & Hinze, "Effect Handlers in Scope", Haskell 2014
  (<https://www.cs.ox.ac.uk/people/nicolas.wu/papers/Scope.pdf>) — scoped/HO operations (rung 4).
  `[NEW] wu-haskell14-scope`. · Poulsen & van der Rest, "Hefty Algebras", POPL 2023
  (<https://doi.org/10.1145/3571255>) — HO effects ELABORATE to first-order ops + handlers (§2, EA5).
  `[NEW] poulsen-popl23-hefty`. · Matache, Lindley, Moss, Staton, Wu & Yang, "Scoped Effects as
  Parameterized Algebraic Theories", 2024 (<https://arxiv.org/abs/2402.03103>) — scopes = resources
  (open/close), ties rung 4 to §Q2. `[NEW] matache-oopsla24-scoped-param`.
- Orchard, Wadler & Eades, "Unifying Graded and Parameterised Monads", MSFP 2020
  (<https://arxiv.org/abs/2001.10274>) — graded (monoid=row) vs parameterised (Atkey, value-indexed),
  unified as category-graded (§Q4). `[NEW] orchard-msfp20-graded-param`. · Atkey, "Parameterised Notions
  of Computation", JFP 2009 — value-indexed monad = the λP-analog (§Q4). `[NEW] atkey-jfp09-param-monad`. ·
  Katsumata, "Parametric Effect Monads", POPL 2014 — graded monad = row/∀ρ axis + FREE fundamental-lemma
  soundness (§Q4). `[NEW] katsumata-popl14-graded`.
- Leijen, "Koka: Row-Polymorphic Effect Types" (<https://arxiv.org/abs/1406.2061>) — row-poly forwarding
  (rung 1) + `st<h>` heap effect auto-discharged on non-escape (§Q2). `leijen-esop14-koka-row-effects`.
- Osvald et al., "Affordable 2nd-Class Values", OOPSLA 2016 (<https://doi.org/10.1145/2983990.2984009>);
  Xhebraj, Bračevac & Rompf, "What If We Don't Pop the Stack?", ECOOP 2022
  (<https://bracevac.org/assets/pdf/ecoop22.pdf>) — only ESCAPING values need heap; escape at
  return/continuation (§Q2). `[NEW] osvald-oopsla16-secondclass`, `xhebraj-ecoop22-nopop`. · Tofte &
  Talpin, "Region-Based Memory Management", I&C 1997 — the R grade axis (§Q2, EA3). `tofte-ic97-region-memory`.

Internal: `ctr-design.md` (D4 wall = rung-1→2 boundary; G1 ⊥-row carve-out) · `memory-management-survey.md`
(§1.2 D5 = handler memory = rung 2; §2.1 closures = only escapers = Q2; §4 escapedCap/region residue; M1/M6)
· `lambda-cube-ascent-survey.md` (R6, the value-side twin) · `effects-vs-cic.md` (CBPV/U⊣F, §Q4) ·
`kernel-substrate-survey.md` §2a (grade family = the λω/λP-analog axes; R/P/S) · `laws-taxonomy.md` §3/§5
(effects = theories; FREE-vs-PRICED = §Q4's Katsumata shape) · `q38-handler-surface-survey.md` (unification —
NOT pre-empted) · `multishot-survey.md` (Q22/Q27 = the K axis, orthogonal to rungs). Code: `IR.lean:113/123/
139-168` (perform op-arg is a VALUE, no HO-op former) · `EffectRow.lean:51,155` (polymorphic row tail + MGU =
λ2-analog, SHIPPED) · `Dispatch.lean:78-84` (splitAtId = tunneling) `:133-181` (state `put` swap vs custom
read-only param = D5) · `EnvMachine.lean:81-82` (closures = only escapers). Invariants: #2, #5, #8.
