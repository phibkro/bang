<!-- note-status: active -->
# Refinement types vs grades — design survey (R5, ROADMAP §Pre-v1 research ladder)

> The R5 question (survey-tier ONLY pre-v1): *"grades vs refinements — bang's n-axis grade
> family may subsume the cheap cases; refinements-as-an-axis is the question, not a
> commitment."* This note surveys the refinement-type systems (Liquid Haskell, F*, Idris 2,
> Flux, Granule), answers the three bang-specific questions — (a) what the grade family
> already subsumes, (b) whether "refinements as another grade axis" is coherent under the
> laws-taxonomy criterion, (c) where the SMT decidability/TCB boundary lands against the
> stratification principle — and ends with the falsifiable probe questions + a verdict.
> It is an **ADR-input note, not an ADR**. Companions: `kernel-substrate-survey.md` (the
> grade family §2a), `laws-taxonomy.md` (the gradeable criterion), Q31 (the operator's
> refinement-surface/quotient-kernel architecture — this survey slots INTO it, it does not
> reopen it), `lambda-cube-ascent-survey.md` (R6 — refinements are the cheap face of its
> dependency question).

## 0 · The one-paragraph verdict

**Refinements are NOT another grade axis, and that is the survey's central finding, not a
disappointment.** A grade classifies a *morphism* by an element of a fixed lattice folded
along composition ("performs at most φ", "uses its argument ≤ q times"); a refinement
classifies a *value* by a predicate that mentions the value (`{n : Int // n ≥ 0}`). Forcing
refinements into the grade machinery destroys the property that makes grades cheap — a
grade lattice's order is decidable by construction, while a predicate lattice's order IS
logical entailment, i.e. the SMT query (§3). The two systems are the two *complementary*
halves every mature design in the literature ships: **graded/effect-indexed COMPUTATION
types × refined VALUE types**, composed at exactly the point bang's CBPV kernel already
has (`F q A` — grade on the computation, refinement inside the `A`). F* is the existence
proof of the composed design; Granule is the existence proof that grades and
solver-discharged refinements coexist as *separate* mechanisms in one language. The
recommendation: **defer implementation (post-v1, as ROADMAP already says), adopt the
framing now** — refinements enter through Q31's surface-refinement/quotient-kernel path as
a *tested-stratum checker* (the laws pattern), never as a grade axis, with a three-rung
discharge ladder whose top rung (lean-smt-style proof reconstruction) keeps the solver out
of the TCB entirely.

## 1 · The census — five systems, one axis of trust

```
 system          refinement power         discharge            solver in TCB?      effects story
 ─────────       ──────────────────────   ──────────────────   ─────────────────   ─────────────────────
 Liquid types    QF predicates over a     SMT (predicate       YES (solver +       none (pure ML subset)
 [rondon-pldi08] fixed qualifier set;     abstraction infers    VC generator
                 DECIDABLE by fragment-   the refinements)      trusted)
                 restriction
 Liquid Haskell  as above + reflection    SMT (Z3)             YES                 divergence BREAKS it:
 [vazou-icfp14]                                                                    lazy binders unsound →
                                                                                    stratify by TERMINATION
 F*              full dependent types +   SMT (Z3) + manual    YES (Z3 + the       THE effect ladder: Tot
 [swamy-popl16]  refinements at every     proofs               WP calculus)        base, effects layered
                 effect (WP transformers)                                           above; refinements ride
                                                                                    each rung's WP
 Idris 2         NO refinements — full    type CHECKING        NO (kernel checks   QTT grades (0/1/ω)
 [brady-ecoop21] inductive families +     (conversion), no      everything)        beside dependency;
                 explicit proof terms     solver                                    effects as libraries
 Flux            liquid types bolted ON   SMT (Z3)             YES — but the       ownership/borrowing
 [flux-pldi23]   an existing language     via rustc plugin     checker is a        (Rust) does the
                 (Rust), core untouched                        LAYER, not core     heavy lifting first
 Granule         indexed types + graded   SMT (Z3) for the     YES for the         graded modal rows;
 [orchard-       modal types SIDE BY      index constraints    constraints         grades and indexed
  icfp19]        SIDE                                                              types are SEPARATE
```

Three census facts do the work downstream:

1. **The decidability of liquid types is bought by fragment restriction** — refinements are
   drawn from quantifier-free logics with decidable SMT theories (linear arithmetic +
   uninterpreted functions), and inference is predicate abstraction over a finite qualifier
   vocabulary ([rondon-pldi08]). Decidable, but *decidable-via-an-oracle*: the check is one
   entailment query per subtyping edge, answered by a solver.
2. **Refinement soundness has a totality dependency.** Liquid Haskell's headline finding
   ([vazou-icfp14]): refinement typing is **unsound under lazy evaluation** because a binder
   may be bound to a diverging term, so `{x : Int // false}`-style vacuous refinements become
   inhabited; soundness is recovered only by **stratifying binders by termination** and
   verifying the stratification (LH proves ~96% of the recursive functions in its 10k-line
   benchmark corpus terminating to get its refinements back). The general lesson: *a
   refinement on `x` is only meaningful where `x` is a value.*
3. **Idris 2 is the solver-free pole.** Full dependency, zero SMT: obligations are discharged
   by conversion checking + explicit proofs. The cost is ergonomics (manual proof terms where
   LH writes nothing); the payoff is a TCB that is just the kernel. Every design in the table
   is a point on this one trust-vs-ergonomics axis.

## 2 · Question (a) — what the grade family already subsumes

Take the refinement use-case census (what people actually verify with LH/F*/Flux) against
the kernel-substrate grade family (`kernel-substrate-survey.md` §2a):

```
 refinement use-case                  grade-subsumed?   which axis / why not
 ──────────────────────────────      ──────────────    ─────────────────────────────────────────
 termination measures                 ◑ COARSE rung     T axis: the Div/⊥-row seam IS the coarse
   (LH's decreasing metrics)                            case; LH-fine measures = refinement-side
 resource / usage counts              ✅                U axis (0/1/ω; zero_usage_erasable)
 taint · security levels              ✅                I axis (DCC-shaped info-flow grade)
 units of measure                     ✅                a user-defined axis (laws-taxonomy §5;
                                                        F# units precedent — no solver needed)
 determinacy / confluence             ✅                N axis (calm-as-grade)
 protocol / typestate                 ◑                 P axis (session-shaped) covers the
   (files must be open, sockets                         COMPOSITION-CLOSED part; per-value state
    connected, …)                                       predicates stay refinement-side
 ──────────────────────────────      ──────────────    ─────────────────────────────────────────
 array bounds  {0 ≤ i < len}          ✗                 the predicate MENTIONS the value
 non-null / non-empty                 ✗                 same
 div-by-zero  {d : Int // d ≠ 0}      ✗                 same
 ordering invariants (sorted list)    ✗                 same (data-structure shape)
 arithmetic pre/postconditions        ✗                 same
```

**The dividing line is sharp and principled:** a use-case is grade-subsumed exactly when the
property is a fact about the *arrow* (how the computation behaves — over-approximable by a
lattice element that joins along composition) and refinement-shaped exactly when it is a fact
about the *point* (which values may sit at this position). The grade family already eats the
whole top half of what refinement papers advertise — which matters economically
(`kernel-substrate-survey.md` §1d: each grade turns a global analysis into a compositional
type, solver-free). What remains genuinely refinement-shaped is the value-predicate residue:
bounds, null-ness, shape invariants, arithmetic side conditions. That residue is real (it is
most of the dogfood JSON parser's manual checks) and no grade axis will ever absorb it.

## 3 · Question (b) — is "refinements as another grade axis" coherent? NO, structurally

The laws-taxonomy criterion (`laws-taxonomy.md` §1/§5): a property is gradeable iff it is
**morphism-shaped and composition-closed**, in which case the grade lattice + join-on-
composition + one fundamental lemma give soundness. Test refinements against it honestly —
the superficial fit is tempting, and the note must kill it precisely:

- **The tempting reading.** Predicates over a carrier form a complete lattice (meet = ∧,
  order = implication); refinement predicates compose by conjunction. So declare "the
  predicate lattice" as an axis and ride `GradeVec` (`IR.lean:334`)? 
- **Failure 1 — the order is not decidable by construction.** Every grade axis shipped or
  scoped (E/U/T/N/I/…) has a *small fixed* lattice whose `⊑` is a table lookup. The predicate
  lattice's `⊑` is **logical entailment** — deciding it IS the SMT query. The axis would
  smuggle the solver into the grade machinery's inner loop, destroying the property the
  laws-taxonomy admissibility gate checks (the axis algebra's own laws must be
  checkable/decidable — model-shaped leaf laws). Grades are cheap *because* their lattices
  are dumb; refinements are expressive *because* their lattice is the whole logic. One
  mechanism cannot be both.
- **Failure 2 — grades cannot mention the value.** A grade element is drawn from a lattice
  fixed before the program exists; `{n : Int // n ≥ 0}` mentions `n`. The row machinery has
  no binder: `F q A` carries a multiplicity `q` and an answer type `A`, and nothing in
  `EffRow`/`GradeVec` scopes over the returned value. Adding that binder is not "another
  axis" — it is **dependency**, the R6 question (`lambda-cube-ascent-survey.md`). Refinements
  smuggled in as grades would be dependent types wearing a lattice costume.
- **Failure 3 — sequencing is not join.** Grades compose by join/fold: `φ₁ ⊔ φ₂`,
  `q₁ + q₂`. Refinements compose *relationally*: `{P} f {Q}` then `{Q} g {R}` — the
  intermediate predicate is consumed, not joined. The structure that captures this is the
  predicate-transformer / Dijkstra-monad composition (F*'s WP calculus, [swamy-popl16]) —
  a graded monad only in the degenerate sense that the "grade monoid" has become as large as
  the assertion logic. **Graded Hoare Logic** ([gaboardi-esop21]) is the literature's exact
  pronouncement on this point: it combines a grade (preordered monoid, folded along
  composition) *and* Hoare assertions (pre/post predicates) as **two separate parameters of
  one framework** — precisely because they are different shapes. The closest prior art to
  "refinements as a grade" deliberately does not merge them.

**The coherent compose-point instead** (and it is already bang's shape): grades stay on the
computation side, refinements go *inside the value type* — `F q {x : A // P x}` — the
Granule/F* factoring. CBPV even hands bang a structural bonus the lazy-Haskell world had to
buy back with a termination analysis (§1 fact 2): **in CBPV, binders bind VALUES** — `letC`
forces the computation before the continuation runs, and thunks are values whose refinement
speaks about the thunk, not its result. The Vazou lazy-binder unsoundness is
unrepresentable by construction in a CBPV kernel. (The totality dependency survives in one
place only: *proving* things about refinements — the Q43 rung — stays total-fragment-only,
which is the standing Q43 ruling anyway.)

## 4 · Question (c) — the decidability/TCB boundary, mapped onto the stratification

Grades are decidable by construction (§3); SMT-backed refinements import a solver. Where
does the solver land against the verified-core/tested-superset seam? The census gives the
ladder, and it is the laws ladder (`laws-taxonomy.md` §1: fuzz → prove) wearing refinement
clothes:

```
 rung   discharge mechanism                     trust story                        stratum
 ─────  ─────────────────────────────────────   ────────────────────────────────   ──────────────
 0      runtime check, fail-loud                 dynamic; the ADR-0063 shape        runtime
        (elaborator inserts the guard)           (escapedCap precedent)
 1      Decidable instances / decision           NO new trust: checking = running   TESTED stratum,
        procedure in the checker                 a total decision procedure; Q31's   solver-free
        (Nat, bounds over known lens,            quotient-prop kernel path rides
         finite-domain predicates)               Quot.sound — ALREADY trusted-3
 2      SMT (Z3/cvc5) discharges VCs             solver + VC-gen enter the TESTED    TESTED stratum
        (the LH/F*/Flux workhorse)               stratum's trust base — like the
                                                 differential-tested surface, NOT
                                                 the kernel's
 3      SMT + proof reconstruction               solver emits a proof OBJECT;        VERIFIED-
        (lean-smt: cvc5's proof replayed         Lean's kernel replays it — the      compatible
         through Lean's kernel                   solver becomes an untrusted         (nothing enters
         [leansmt-cav25]; SMTCoq the             PROOF FINDER, zero TCB growth;      the TCB)
         Coq ancestor)                           the Q43 proof-export shape
```

Three consequences worth pinning:

1. **The refinement CHECKER lives in the tested stratum, like laws** — exactly the brief's
   hypothesis, confirmed by Flux as the census precedent: a liquid-types layer over an
   untouched core language, trusted like a linter, not like the kernel. Bang's version is
   stronger: rung 1 is *solver-free* (Q31's decidable-props path — propositional truncation
   via quotient collapses proof-relevance, so checking a refinement = deciding `P`, and
   `Quot.sound` is already in the trusted-3 axiom budget), and rung 3 exists because the
   host IS a proof assistant — lean-smt-style reconstruction makes even the SMT rung
   TCB-neutral, which none of LH/F*/Flux can say (they trust Z3 forever).
2. **F*'s known pain is the cautionary tale for rung 2**: solver-discharged obligations are
   brittle (proof instability under solver upgrades, opaque failures). The stratification
   answer: rung-2 red is a *tested-stratum* red (like a failing law fuzz), never a
   kernel-soundness event.
3. **The seam marking stays explicit**: a rung-0 runtime guard is a *descent* (ADR-0026
   shape) and must be marked, exactly like `Div`. An unproven refinement silently checked at
   runtime would violate the fail-loud invariant.

## 5 · The falsifiable probes an R5 probe-increment would run

1. **The residue-coverage probe (is rung 1 worth anything?).** Implement `Nat` +
   array-bounds as Q31 rung-1 refinements (Decidable instances, no solver) in the
   checker; falsifier: they discharge < a useful fraction (say < half) of the dogfood JSON
   parser's manual guards (`dogfood-json-findings.md` names them). If the solver-free rung
   covers most real guards, rung 2 (SMT) can be deferred indefinitely; if not, the SMT rung
   is on the critical path and its TCB story (rung 3) must be designed sooner.
2. **The erase-to-base probe (does the kernel stay untouched?).** Elaborate
   `{x : A // P x}` to kernel `A` + an obligation (discharged rung-1/2, or a rung-0 guard) —
   the type-level analog of elaborate-to-mono ("elaborate-to-base"). Falsifier: some
   refinement flows through a `mu`/`sum` position where erasure loses the invariant needed
   to re-check downstream (the same shape as the ADR-0075 hole-id wall) — that would force
   refinements into kernel `VTy`, i.e. a spine ADR, and the cost estimate changes class.
3. **The grade-axis refutation probe (close the (b) question by machine, not prose).**
   Attempt to register `(Prop over Int, ∧, ⊨)` as a user grade axis through the
   laws-taxonomy admissibility gate. Expected: fails the gate (the axis's own lattice laws
   are not decidably checkable). A machine refutation here turns §3 from argument into
   witness — the house refute-first move.

## 6 · Verdict — recommend / defer, with cost

**DEFER implementation (post-v1, as ROADMAP R5 already scopes); ADOPT the framing now; the
survey is the deliverable and it is banked here.** Concretely:

- **Refinements-as-a-grade-axis: REJECTED** on three structural grounds (§3); Graded Hoare
  Logic is the literature's corroboration that grades and assertions are two parameters,
  not one. Nobody should re-litigate this without new structure; probe 3 can make the
  rejection machine-checked for ~an afternoon of work.
- **The adopted shape**: grades × refined value types, composed at `F q A`; checker in the
  tested stratum; discharge ladder rung 0→3 (§4) with Q31's solver-free rung 1 first and
  lean-smt reconstruction as the eventual TCB-clean top. This slots into Q31 unchanged —
  the survey *confirms* the operator's quotient-props architecture and adds the census +
  the ladder around it.
- **Cost when taken up** (post-v1, post-#47): rung 0–1 is elaborator/checker work only —
  kernel untouched, census stable (the ADR-0075 pattern; days-to-weeks). Rung 2 adds a
  solver integration (tested-stratum, engineering-sized). Rung 3 rides Q43's machinery when
  that lands. The only path that touches the spine is probe 2's falsifier firing —
  kernel-visible refinements — which is precisely what the probe exists to detect early.
- **Trigger to take it up** (unchanged from Q31): array/index safety, positivity, or
  div-by-zero pressure in dogfooding — i.e. probe 1's residue becoming a felt cost.

## References

- **Liquid types**: Rondon, Kawaguchi, Jhala, PLDI 2008, DOI
  [10.1145/1375581.1375602](https://dl.acm.org/doi/10.1145/1375581.1375602). [rondon-pldi08]
- **Refinement types for Haskell** (the lazy-binder unsoundness + termination
  stratification): Vazou, Seidel, Jhala, Vytiniotis, Peyton Jones, ICFP 2014, DOI
  [10.1145/2628136.2628161](https://dl.acm.org/doi/10.1145/2628136.2628161); tool/experience:
  "LiquidHaskell", Haskell 2014, DOI 10.1145/2633357.2633366. [vazou-icfp14]
- **F*** (refinements + the Tot-base effect ladder, WP transformers, Z3): Swamy et al.,
  "Dependent Types and Multi-Monadic Effects in F*", POPL 2016, DOI
  [10.1145/2837614.2837655](https://fstar-lang.org/papers/mumon/). [swamy-popl16]
- **Idris 2** (the solver-free dependent+QTT middle): Brady, ECOOP 2021, DOI
  [10.4230/LIPIcs.ECOOP.2021.9](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ECOOP.2021.9).
  [brady-ecoop21]
- **Flux** (liquid types layered over Rust — the tested-stratum-checker precedent):
  Lehmann, Geller, Vazou, Jhala, PLDI 2023, arXiv
  [2207.04034](https://arxiv.org/abs/2207.04034). [flux-pldi23]
- **Granule** (grades + indexed types side by side, Z3-discharged): Orchard, Liepelt,
  Eades, ICFP 2019 — in-repo `orchard-icfp19-granule`.
- **Graded Hoare Logic** (grades and assertions as two separate parameters — the §3
  corroboration): Gaboardi, Katsumata, Orchard, Sato, ESOP 2021, arXiv
  [2007.11235](https://arxiv.org/abs/2007.11235), DOI 10.1007/978-3-030-72019-3_9.
  [gaboardi-esop21]
- **lean-smt** (cvc5 proof reconstruction through Lean's kernel — the rung-3 TCB story):
  Mohamed et al., CAV 2025, arXiv [2505.15796](https://arxiv.org/abs/2505.15796);
  SMTCoq the Coq ancestor. [leansmt-cav25]
- **In-repo anchors**: Q31 (`docs/notes/questions/Q31-refinement-types-quotient-props.md` —
  the operator architecture this slots into) · `laws-taxonomy.md` §1/§5 (the gradeable
  criterion + the axis admissibility gate) · `kernel-substrate-survey.md` §2a/§1d (the grade
  family + the economic axis) · `Bang/Core/IR.lean:334` (`GradeVec`) · ADR-0063 (fail-loud
  runtime rung) · ADR-0026 (descent must be marked) · `docs/notes/verification-ladder.md`
  (fuzz→prove; refinement/contract types "post-v1, design-first" — this is that design
  survey) · `dogfood-json-findings.md` (the manual-guard residue probe 1 measures).
