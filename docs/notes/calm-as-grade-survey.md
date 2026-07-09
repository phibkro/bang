<!-- note-status: active -->
# CALM as a grade — can monotonicity be a coeffect in bang's row system?

> Research lane rcalm (2026-07-09). Answers `distributed-story.md` §2 rung 3: can CALM's
> *"consistency ⟺ logical monotonicity"* be carried as a GRADE/coeffect in bang's effect-row
> system, so **monotone** operations type coordination-FREE and **non-monotone** ones
> (compare-and-swap, aggregation-with-retraction) visibly demand coordination in the type?
> DOCS-ONLY survey. Verdict + ADR-INPUTS at the bottom; nothing here is scoped v1 work —
> this is a POST-V1 research map. The local anchor already exists: `Bang/Distribution.lean`
> states `rowmonotone_coordination_free` as a marked, off-spine **conjecture** (a `sorry`),
> and this note is the design study behind that marker.

---

## 0 · TL;DR (the verdict, up front)

```
recommended arm  : (iii) LATTICE-TYPED DATA (LVars-style monotone store) as the KERNEL primitive,
                   + (i) a `coord` EFFECT that non-monotone ops must carry as the SURFACE display.
                   The grade-on-the-arrow (ii) is the WRONG shape (grades the row → forbidden multiset).
smallest pub unit: "a monotone `lat`-typed fragment + a coordination-free replication handler with
                   a PROVED convergence law for CRDT merges (Bang.Distribution's conjecture, discharged
                   for the fragment)" — NOT full CALM. The honest wall is that CALM is proved for
                   DATALOG, and the functional-language transfer is exactly the research contribution.
kernel cost      : arm (i) needs NO new primitive (a `coord` label is an ordinary effect — invariant #5
                   intact). arm (iii)'s monotone-store IS a state handler with a lattice-join `put` — a
                   library, NOT a sixth primitive, IF the join is a user value (the CRDT `merge`). So
                   NEITHER recommended arm is an ADR-level spec change to the five primitives. The
                   arm to REJECT (ii, grading the row) IS foreclosed by invariant #2 (ADR-0001/0018).
```

The move that makes this cheap for bang and expensive for everyone else: **bang is already graded
CBPV with rows that ARE join-semilattices** (invariant #2, `[Lattice Eff] [OrderBot Eff]`, ADR-0018).
CALM's precondition — a bounded join-semilattice — is bang's *native row algebra*. Nobody else gets
the lattice for free; bang pays for it once (it already did) and reuses it on the distribution axis.
That is the `Bang/Distribution.lean` thesis (`semilattice → coordination-free`) made into a language
feature instead of a comment.

---

## 1 · CALM primary sources — what EXACTLY was proved, and for WHICH model

### 1.1 The theorem (Hellerstein & Alvaro, CACM 2020)

**CALM = Consistency As Logical Monotonicity.** The headline (CACM'20, [HA20]):

> *"The programs that have consistent, coordination-free distributed implementations are exactly the
> programs that can be expressed in monotonic logic."*

The two load-bearing definitions, verbatim-precise from the paper:

```
monotonic program   P is monotonic iff for input sets S ⊆ T,  P(S) ⊆ P(T).
                    (output only GROWS with input; no earlier conclusion is ever retracted.)
coordination-free   a distributed implementation where every machine can proceed autonomously,
                    WITHOUT waiting on synchronisation messages required in ALL possible
                    data-partitionings. Coordination-free ⇒ AVAILABLE under partition.
```

The equivalence is an **iff**: monotone ⟺ coordination-free-implementable. The non-monotone side is
the interesting one — an operation whose output can SHRINK when more input arrives (set-difference,
`∀`, negated `∃`, aggregation-with-retraction, compare-and-swap) *cannot* be made coordination-free,
because a machine that answered early might have to retract. That retraction is the coordination.

**The CACM paper's own caveat about real languages** (this is the wall, stated by the authors):

> *"Assignment is a nonmonotonic programming construct: outputs based on a prefix of assignments may
> have to be retracted when new assignments come in."*

So **imperative mutable assignment is inherently non-monotone**, which makes CALM analysis of an
imperative language "extremely hard." The paper explicitly notes that **functional / immutable
programming gives a simple monotone pattern**: `undefined → final value, never back`. This is the
single most important sentence in the survey for bang: *a pure functional core is already on the
monotone side of the line by construction; the non-monotone operations are the ones that mutate or
retract.* bang's kernel (thunks, force, no implicit mutation — mutation is a handler) sits on the
good side of this by design.

### 1.2 The proof and its model (Ameloot, Neven, Van den Bussche, PODS'11 → JACM/TODS)

The conjecture (Hellerstein 2010) was **proved** by Ameloot et al. [ANV13] in the framework of
**relational transducer networks**:

```
model             a network of nodes, each an event-driven server with a RELATIONAL backing store,
                  programmed with QUERIES (relational algebra / Datalog). A node: (1) ingests
                  unordered batches of tuple insertions, (2) recomputes its queries, (3) sends
                  results to peers. All state is relations; all computation is queries.
what was proved   Thm (Ameloot): a query is computable by a COORDINATION-FREE transducer network
                  IFF it is MONOTONE. "Coordination-free" is formalised as: the output does not
                  depend on knowledge of the full set of network nodes — a node cannot need to hear
                  from EVERYONE before answering. Later work (Ameloot/Ketsman, TODS'15, "Weaker forms
                  of monotonicity") refines this into a LADDER: successively weaker monotonicity ⟺
                  successively more coordination, each captured by an explicit Datalog variant.
```

**The gap that IS the research risk (and the honest wall):** the theorem is proved for a
**first-order / Datalog relational query model** — a computation model where "program" = a set of
monotone-or-not deductive rules over relations. It is **NOT** proved for a λ-calculus, an
effect-and-handler calculus, or a graded CBPV kernel. The transfer from "monotone Datalog query" to
"monotone bang computation with an effect row" is the unproven step. §5 states this precisely and
names the smallest thing bang can actually prove.

### 1.3 Blazes / Bloom — the language embodiment

Bloom (and its coordination-analysis companion **Blazes**) is the data-centric distributed language
where CALM lives: state and events are named data, computation is queries over that data, and the
compiler's monotonicity analysis flags exactly where coordination is required. Blazes does the
*coordination-placement* — given a dataflow with some non-monotone nodes, it inserts the minimum
coordination (ordering/sealing) needed. **This is the pattern bang would replicate at the type level:
the row tells you WHERE the non-monotone ops are; a handler supplies the coordination there and only
there.** Blazes is the existence proof that "analyse monotonicity → place coordination minimally" is a
real, implemented pipeline — not just a theorem.

---

## 2 · Lattice-language prior art — the functional-language transfer attempts

This is the crucial section: **who has moved CALM off Datalog and toward a typed/functional setting,
and how far did they get.** Ranked by proximity to what bang wants.

### 2.1 BloomL (Conway et al., SoCC'12) — the closest "monotonicity-as-classification" prior art

BloomL extends Bloom with **bounded join-semilattices as first-class types**, and — critically —
**classifies every method into three grades**:

```
method class     meaning                                       coordination consequence
─────────────────────────────────────────────────────────────────────────────────────────
non-monotonic    output may shrink as lattice input rises      REQUIRES coordination
monotone         order-preserving (x ≤ y ⇒ f x ≤ f y)          coordination-FREE
morphism         homomorphism: f(a ⊔ b) = f(a) ⊔ f(b)          coordination-free AND
  (homomorphic)    (implies monotone)                            incrementally / efficiently computable
```

**This is a per-operation grade, and it is the direct ancestor of the arm this survey recommends.**
The certification rule is exactly CALM: *so long as a program's dataflow avoids non-monotone methods,
it needs no coordination.* BloomL lets users define their own semilattices (supply the `⊔`/merge) and
composes small analysable lattices into large programs — the "safe composition of small lattices" that
maps directly onto bang's compositional row union. BloomL shipped a Dynamo-style KV store this way.

The one gap: BloomL's classification is a **whole-program dataflow analysis over a Datalog-ish
substrate**, not a type/effect discipline in a higher-order functional language. It marks methods by
*fiat/annotation* and checks composition; it does not have bang's arrow types or effect rows to hang
the grade on. bang's contribution would be to make BloomL's three-way method classification a
**property of the type** (a row membership or a data-type grade), inferred/checked rather than declared
per-method — and to have it compose through higher-order functions, which BloomL cannot express.

### 2.2 LVars / LVish (Kuper & Newton, ICFP'13; Kuper/Turon/Krishnaswami/Newton, POPL'14) — the CLOSEST functional-calculus transfer

**This is the one prior art in a real typed λ-calculus with a determinism PROOF.** LVars are shared
memory cells whose contents live in a user-specified lattice:

```
write  putLV     takes the least-upper-bound (⊔) of old and new content — writes are MONOTONE by
                 construction; the store only ever climbs the lattice.
read   getLV     a THRESHOLD read — blocks until the cell has crossed a specified lower bound, then
                 returns that fixed threshold value. Threshold reads are the trick that makes
                 concurrent monotone writes OBSERVABLE deterministically.
freeze freezeLV  seal a cell (enables a negative/exact read); post-freeze writes error. This is the
                 escape hatch to non-monotone observation, and it is exactly where determinism weakens.
```

Formal results (the part bang should steal):
- **λLVar** (put + threshold-get) is **deterministic** — proved.
- **λLVish** (adds freeze, handlers, arbitrary updates) is **quasi-deterministic** — proved: *every
  run that produces a value produces the SAME value, or raises an error.* `freezeLV` is statically
  typed `QuasiDet`; `putLV`/`getLV` are polymorphic in the determinism level.

**The transfer to bang:** LVars ARE "lattice-typed DATA" (encoding-fork arm iii). A monotone store is
a state handler whose `put` is a lattice-join instead of an overwrite; a threshold read is the safe
observation. The determinism-level in the LVar type (`Det` vs `QuasiDet`) is **precisely a grade**:
freeze flips you from the coordination-free (`Det`) fragment to the may-need-coordination (`QuasiDet`)
fragment. bang's graded CBPV can carry that determinism grade on the type where LVish carried it as a
type-index. **LVish is the proof that "monotone-write lattice store + a grade for the freeze escape"
is sound in a functional calculus.** It is the single strongest evidence that rung 3 is achievable —
it did the hard part (a determinism proof for a lattice-store λ-calculus) already; the CALM framing
(coordination-free ⟺ monotone) is the distributed reading of the same theorem.

### 2.3 Flix (Madsen/Lhoták, PLDI'16, OOPSLA'25) — monotonicity tracked WITH TYPES

Flix is the prior art for **"monotonicity is a property the type system checks"** — but for a
different purpose (fixpoint existence, not coordination):

```
Flix mechanism                                  what it buys
────────────────────────────────────────────────────────────────────────────────────────
lattice semantics on Datalog (`lat` not just    generalises Datalog from relations to lattices
  relations); lattices are type classes         (the BloomL move, but in a typed FP host)
the `fix` operator over a monotone function      the TYPE SYSTEM proves a function is monotone ⇒
                                                 guarantees the least-fixpoint EXISTS and terminates
first-class Datalog constraints as VALUES        Datalog programs are values: passed, composed,
                                                 returned. A Datalog sub-language embedded in an FP host.
stratified negation, checked at compile time     non-monotone (negation) is confined to strata;
                                                 the compiler ENFORCES the stratification
```

Flix's contribution bang can lift: **a function typed monotone is a machine-checkable property**, and
monotonicity licenses a semantic guarantee (for Flix: fixpoint existence; for bang: coordination-
freedom). Flix also demonstrates the **arm (iv)** route — a Datalog-ish sub-language embedded as
first-class values in a functional host. See q38-handler-surface-survey.md for the prior Flix findings
(method-impl clause shape, grade-as-dial); the distribution axis reuses the *same* Flix, different
feature (its lattice/Datalog core rather than its handler surface).

### 2.4 Consistency-type systems (RedBlue, Quelea, MixT, Gallifrey, LoRe) — the "annotate consistency" family

A parallel tradition annotates *consistency levels* rather than *monotonicity*:

```
system        mechanism                                       relation to CALM-as-grade
──────────────────────────────────────────────────────────────────────────────────────────────
RedBlue       ops labelled blue (eventually-consistent,       MANUAL labelling — the programmer
(Li, OSDI'12) local) vs red (strongly-consistent, coordinated) declares coordination need, not derived
              red ops serialised, blue ops replicated lazily   from monotonicity. bang wants the label
                                                               DERIVED (monotone ⇒ blue) not asserted.
Quelea        contract language over an eventually-consistent  contracts ≈ LAWS; the system SYNTHESISES
(Sivaramak.,  store; classifies ops by the strongest contract   coordination when an invariant could be
PLDI'15)      they need; auto-generates coordination            violated. Closest to "law-shaped check".
MixT          information-flow TYPE SYSTEM for mixed-consistency the type-system machinery (IFC) is the
(Milano '18)  transactions; consistency is a type label that    right shape; the label is consistency,
              can't be violated by construction                 not monotonicity — a sibling axis.
Gallifrey     restrictions + "consistency as a contract";       per-object consistency; shares objects
(Milano)      per-task consistency choices                      without losing safety
LoRe          reactive dataflow + static verification (Viper);  MOST RECENT (ECOOP'23) functional-
(Mogk '23)    developer writes safety INVARIANTS, compiler       flavoured attempt: proves invariants,
              inserts strong consistency (coordination) only     inserts coordination minimally. The
              where a concurrent interaction could violate them  Blazes idea with a modern verifier.
```

**The distinction that matters for bang:** these systems make consistency a *declared* label
(RedBlue's red/blue, MixT's IFC labels). CALM-as-grade is stronger and more elegant — the label is
**derived from monotonicity**, which is a structural property, not a programmer assertion. bang's bet
is the CALM bet: don't make the user say "this needs coordination," make the *type* say it because the
operation is non-monotone. LoRe is the closest recent evidence that the derived approach is
tractable (it derives coordination placement from invariant analysis) — but LoRe uses an external SMT
verifier (Viper), not a grade in the type system. **No shipped system carries monotonicity as a
graded effect/coeffect in a higher-order type system. That empty cell is the bang contribution.**

---

## 3 · The encoding fork — four arms, priced against bang's actual machinery

The question: *where does the monotonicity grade live?* Four candidate encodings, each priced against
(a) what licenses the coordination-free compilation, (b) what the CHECK is, (c) the kernel cost
(invariant #5: five primitives; a sixth is an ADR-level spec change).

### Arm (i) — monotonicity as an effect-row MEMBER (a `coord` effect)

```
shape       non-monotone ops carry a `coord` label in their row; monotone ops don't.
            a computation's type `A ! {coord, …}` VISIBLY demands coordination; `A ! {}` (coord-free
            fragment) is coordination-free by the row being coord-clean.
licenses    a coord-clean row ⇒ install the coordination-free replication handler (no consensus).
            a row containing `coord` ⇒ the type-checker requires a coordinating handler at the use site.
check       SYNTACTIC on the row: `coord ∈ row?` — reuses the EXACT `no_accidental_handling` /
            row-membership machinery the kernel already runs. This is the cheapest possible check.
kernel cost NONE beyond a new LABEL. `coord` is an ordinary effect; adding a label is NOT adding a
            primitive (invariant #5 counts the five primitives, not the label alphabet). NO ADR-level
            spec change to the kernel. ✓
weakness    a label is a BINARY flag (coord / not), not the structural REASON. It says "this op is
            non-monotone" but doesn't ENFORCE monotonicity of the ops that lack the label — a monotone
            op could forget to be monotone and the row wouldn't catch it. The label is a
            CONSEQUENCE of monotonicity, asserted, not a PROOF of it. Pairs best with arm (iii),
            which supplies the proof.
```

### Arm (ii) — a GRADE on the arrow (grade the row per-label) — **REJECTED**

```
shape       give the row a per-label MULTIPLICITY / monotonicity weight (`state ↦ monotone`,
            `agg ↦ non-monotone`) — a graded monad on the effect row.
licenses    (would) let the grade drive the compile.
check       structural on the graded row.
kernel cost FORECLOSED. This is THE TRAP named in Q27 and invariant #2 / ADR-0001: rows are SETS
            (idempotent, union = join, never a multiset). A per-label-WEIGHTED row IS the forbidden
            multiset; it breaks the join-semilattice structure that `no_accidental_handling` and the
            Yoshioka ICFP'24 effect-safety proof depend on. Grading the ROW is exactly what Q27 says
            NOT to do. ✗ REJECTED on invariant #2.
note        the grade must live BESIDE the row (on data or on a handler property), never INSIDE it.
            This is the same ruling Q27 reached for the resumption grade — orthogonal axes,
            `Finset Label × (grade elsewhere)`, never a fused graded row.
```

### Arm (iii) — lattice-typed DATA (LVars-style monotone store) — **RECOMMENDED CORE**

```
shape       a `lat T`-typed store cell (T a bounded join-semilattice); the ONLY write is a
            lattice-join `put x = cell := cell ⊔ x` (monotone by construction); reads are threshold
            reads (LVar-style) or full reads at a sealed point. The CRDT `merge` IS the `⊔`.
licenses    monotone-by-construction writes ⇒ replicas converge regardless of message order/dup/delay
            (the state-based-CRDT convergence theorem). Coordination-free BECAUSE the store can only
            climb its lattice — the CALM monotone side, ENFORCED not asserted.
check       LAW-SHAPED, and this is the killer: the coordination-freedom rides on `merge` being a
            join-semilattice (comm · assoc · idem). That is EXACTLY what `lawInstancesOf` + `bang test`
            (#60, LANDED) already discovers and shrinks, and what Q43 proof-export lifts to a Lean goal.
            So the check is: the user's `merge` PASSES its semilattice laws (rung 1 machinery, already
            built) ⇒ the `lat`-store is monotone ⇒ coordination-free. The determinism proof is LVish's
            (quasi-determinism for λLVish) — bang inherits the shape.
kernel cost  a monotone store is a STATE HANDLER whose `put` composes with the user's `merge` value —
            it is LIBRARY code over the existing state effect + handler, NOT a sixth primitive, PROVIDED
            the `⊔` is a user value (the CRDT merge) rather than a kernel operation. So: NO ADR-level
            spec change to the five primitives. ✓ (The state effect + handlers are primitives #3/#4;
            `lat` is a discipline on top, exactly as STM-as-handler is per ADR-0030.)
strength    this is the arm that makes monotonicity STRUCTURAL (correctness-by-construction, SOUL.md):
            the store CAN'T be written non-monotonically, so the "monotone" claim is a type property,
            not a hope. It's LVish's proven design + bang's already-built law machinery + bang's native
            join-semilattice rows. Three assets converge here.
```

### Arm (iv) — a Datalog-ish sub-language (the Flix route)

```
shape       embed a first-class monotone-Datalog fragment as VALUES (Flix's first-class constraints);
            monotone fixpoints compile coordination-free; stratified negation is the coordination seam.
licenses    the monotone-Datalog fixpoint IS the CALM-proved fragment — this is the ONE arm where the
            Ameloot theorem applies DIRECTLY (it's the same model), so the coordination-free compile is
            LITERALLY the proved result, no transfer risk.
check       stratification + monotonicity of rules, compiler-checked (Flix does this).
kernel cost  HIGH as a language feature: a Datalog sub-language is a large surface addition (parser,
            solver, stratification checker). NOT a kernel primitive, but a big frontend/stdlib build.
            Better as a LIBRARY / EDSL over the monotone fragment than a kernel change.
strength/wall the theoretically SAFEST (no transfer risk — it's the proved model) but the LEAST
            bang-native (it's a separate paradigm bolted on, not "paradigm = row"). Reserve as the
            escape hatch / comparison point, not the primary bet. It also under-uses bang's thesis:
            the whole point is that bang's OWN rows are the semilattice, so you shouldn't need a
            separate Datalog engine to get CALM.
```

### The fork, one table

```
arm   where the grade lives     check              kernel cost        verdict
──────────────────────────────────────────────────────────────────────────────────────────────
(i)   effect-row member `coord` syntactic row-mem   +1 LABEL (no ADR)  ADOPT as the SURFACE/display
(ii)  graded row (per-label)    structural          FORECLOSED inv#2    REJECT (the Q27 trap)
(iii) lattice-typed DATA (LVar) LAW-shaped (#60!)   handler+lib (no ADR) ADOPT as the CORE mechanism
(iv)  Datalog sub-language      stratification      big frontend        DEFER (safe but non-native)
```

**Recommended composite: (iii) as the enforcing core + (i) as the surface display.** The `lat`-store
makes monotonicity structural and the check LAW-shaped (riding #60, the machinery bang already ships);
the `coord` row-label makes the *consequence* visible in the type at the use site (the row tells you
which ops need consensus — the exact phrasing of rung 3). (ii) is the trap; (iv) is the safe-but-
foreign fallback and the direct-theorem comparison point.

---

## 4 · What bang already has (the assets this reuses)

```
asset                              where                          what it buys the CALM arm
──────────────────────────────────────────────────────────────────────────────────────────────────
rows ARE join-semilattices         invariant #2, ADR-0001/0018,   CALM's precondition (bounded
  ([Lattice Eff][OrderBot Eff])    Bang/Core/EffectRow.lean       join-semilattice) is NATIVE. Free.
graded CBPV (row ⟂ grade axes)     HasCTy: Finset Label ×         a place to put a monotonicity/determinism
                                   GradeVec Mult                  grade BESIDE the row (arm iii's det-grade)
lawInstancesOf + bang test (#60)   Bang/Witness/LawTest.lean,     the CHECK for arm (iii): user `merge`
  — LANDED                         TypeCheck.lawInstancesOf       passes semilattice laws ⇒ monotone store
Q43 proof-export (NEAR)            rq43 lane                      lifts the surviving merge-laws to a Lean
                                                                  goal ⇒ CERTIFIED CRDT (rung 1 → proof)
Bang/Distribution.lean             the marked conjecture          rowmonotone_coordination_free is ALREADY
                                   `rowmonotone_coordination_free`  the theorem to discharge for the fragment;
                                   (sorry, off-spine)             the algebra→mechanism spectrum is stated
STM-as-handler precedent           ADR-0030                       proves "a privileged-looking thing (STM,
                                                                  or a monotone store) ships as a HANDLER,
                                                                  not a primitive" — arm (iii)'s cost model
the total/Div seam (stratification) CLAUDE.md                     the SAME shape: a monotone (coord-free)
                                                                  fragment + a non-monotone superset,
                                                                  separated by an explicit type-visible seam
                                                                  (here the `coord` row-label = the seam)
```

The stratification principle applies cleanly: **monotone/coord-free fragment = the verified core;
non-monotone/coordinated = the tested superset; the `coord` effect-row label = the explicit seam.**
This is the project's one shape (CLAUDE.md) applied to the distribution axis — which is why it's a
natural fit rather than a bolt-on.

---

## 5 · The honest wall + the smallest publishable unit

### 5.1 The wall, stated precisely

```
CALM is PROVED for:      monotone first-order / Datalog queries over relations, in the relational-
                         transducer-network model (Ameloot et al.). "Program" = deductive rules.
bang wants it for:       monotone COMPUTATIONS in a higher-order, effectful, graded-CBPV calculus.
                         "Program" = thunks + effects + handlers.
the gap (= the risk       there is NO published CALM theorem for a λ-calculus or an effect-handler
AND the contribution):    calculus. The transfer requires either (a) restricting bang programs to a
                         fragment where "monotone bang computation" has a clean order-theoretic meaning
                         (the `lat`-store fragment, arm iii — where LVish already proved determinism),
                         or (b) a NEW theorem relating monotone-row bang computations to coordination-
                         freedom. (a) is achievable now; (b) is a genuine research paper.
```

Two things make the wall lower for bang than for a random FP language:
1. **The pure functional core is already monotone** (CACM's own observation: immutable = `undefined →
   value, never back`). bang's kernel has no implicit mutation — mutation is a handler. So the
   non-monotone operations are exactly the ones that install a mutating/retracting handler, which the
   ROW already tracks. bang doesn't have to *find* the non-monotone ops; the row already names them.
2. **LVish already proved the hard theorem** (quasi-determinism for a lattice-store λ-calculus). Arm
   (iii) inherits that proof shape rather than inventing it. The CALM reading (coordination-free ⟺
   monotone) is the distributed interpretation of LVish's determinism result.

### 5.2 The smallest publishable unit (SPU)

**NOT** "full CALM for bang" (a graded-effect CALM theorem — the ambitious version, arm-(i)+(iii)
general case, genuinely novel and paper-worthy but high-risk).

**The SPU is:**

> *A monotone `lat`-typed fragment of bang (LVar-style stores whose `merge` is a user-supplied
> join-semilattice), + a coordination-free replication handler, + a PROVED convergence law: for any
> `merge` that passes its semilattice laws (checked by `lawInstancesOf`/`bang test`, lifted to Lean by
> Q43), replicas driven under the coordination-free handler converge regardless of message order,
> duplication, or delay.*

This is publishable because it is the **first** integration of (a) CRDT-merge-law discovery/shrinking
(#60), (b) machine-checked law certification (Q43), and (c) a coordination-free handler, into ONE
pipeline in a graded-effect language — and it discharges the `Bang.Distribution` conjecture *for the
fragment*, turning the marked `sorry` into a theorem with a named scope. It rides the KV-store hello-
world (`distributed-story.md` §4): per-key `lat` registers with proved merges (SPU) → the CAS key is
the non-monotone op the `coord` row-label flags (arm i) → the story's rung-3 punchline lands with a
proof behind exactly one clause of it.

The full-CALM theorem (a general "monotone-row ⇒ coordination-free" result for bang) is the STRETCH
paper. Name it, don't promise it — it's the arm-(i) general case and it needs theorem (b) above.

---

## ADR-INPUTS

> For a future post-v1 ADR on the distribution axis / CALM-as-grade. This lane produces INPUTS
> (evidence + recommended shape + rejected alternatives), not the decision — the manager/operator
> decides. STOP-and-SHOW forks are marked ★.

### Recommended shape

1. **Adopt arm (iii) — lattice-typed data (LVar-style monotone store) — as the ENFORCING CORE.** A
   `lat T` store whose only write is a lattice-join with a user-supplied `merge`; monotone by
   construction. It ships as a STATE HANDLER + library (ADR-0030 precedent: privileged-looking =
   handler, not primitive), so it is **NOT** a sixth kernel primitive — invariant #5 intact, no
   spec-level kernel change. The determinism guarantee is LVish's (quasi-determinism, POPL'14),
   inherited not invented.

2. **Adopt arm (i) — a `coord` effect-row label — as the SURFACE DISPLAY.** Non-monotone ops (CAS,
   agg-with-retraction, the `freeze`/exact-read escape) carry `coord` in their row; a coord-clean row
   is the coordination-free fragment. The check is syntactic row-membership — reuses
   `no_accidental_handling`. This is the "the row tells you which ops need consensus" phrasing of
   distributed-story.md rung 3, made literal. Costs +1 label, no ADR-level kernel change.

3. **The CHECK is LAW-SHAPED and already built.** Coordination-freedom of a `lat` store rides on its
   `merge` being a join-semilattice — discovered and shrunk by `lawInstancesOf` + `bang test` (#60,
   LANDED), certified to Lean by Q43 proof-export (rq43 lane). Connect CALM-as-grade directly to the
   law machinery: **monotonicity is checked as a LAW, not asserted as an annotation.** This is the arm
   that makes the SOUL.md "correctness by construction" move — the store *can't* be non-monotone.

4. **REJECT arm (ii) — grading the row per-label.** Foreclosed by invariant #2 / ADR-0001: rows are
   SETS; a per-label-weighted row is the forbidden multiset and breaks the join-semilattice structure
   `no_accidental_handling` + Yoshioka ICFP'24 depend on. This is the Q27 trap ("do NOT grade the
   row") applied to the monotonicity grade. The grade lives on DATA (arm iii) or as a LABEL (arm i),
   never INSIDE the row.

5. **DEFER arm (iv) — a first-class monotone-Datalog sub-language (Flix route).** It's the ONE arm
   where Ameloot's theorem applies with zero transfer risk (same model), so keep it as the
   comparison/escape hatch — but it's a large non-native frontend addition that under-uses bang's
   "rows ARE the semilattice" thesis. Reserve for later; not the primary bet.

### Smallest publishable unit (the scope to actually build first)

6. **Build the SPU, not full CALM (§5.2).** Monotone `lat`-fragment + coordination-free replication
   handler + a proved CRDT-merge convergence law — discharging the `Bang.Distribution`
   `rowmonotone_coordination_free` conjecture FOR THE FRAGMENT (turning the marked `sorry` into a
   scoped theorem). Rides the KV-store hello-world. The general "monotone-row ⇒ coordination-free"
   theorem for bang is the STRETCH paper — named, not promised.

### ★ Operator-shaped forks (STOP-and-SHOW — a peer/IC cannot decide these)

- **★ Is the distribution axis a v1.x commitment or a post-v1 research track?** distributed-story.md
  says post-v1; this survey assumes that. If the operator wants to pull rung 3 forward, the SPU scope
  (§5.2) is the entry point and it depends on Q43 (rq43) landing first.
- **★ Determinism grade placement.** Arm (iii) needs a determinism/monotonicity grade BESIDE the row
  (Det vs QuasiDet, the LVish freeze-flip). Does that reuse the EXISTING `GradeVec Mult` channel
  (Q27's "same rig grades everything" thesis, the operator's k-grade unification), or is it a distinct
  determinism lattice? Q27's ruling (orthogonal axes, one rig) suggests reuse, but the monotonicity
  grade is a DIFFERENT semiring than QTT's 0/1/ω — this is a genuine design fork the operator should
  weigh. Recommendation to bring to that decision: reuse the *mechanism* (a grade beside the row) but
  likely a distinct *lattice* (monotone/non-monotone, not 0/1/ω) — confirm against the kernel's
  `EffSig` parametricity before committing.

---

## Sources

Local (verified on-disk this lane):
- `Bang/Distribution.lean` — `eff_join_semilattice`, `rowmonotone_coordination_free` (the marked
  conjecture this survey is the design study for), the algebra→mechanism spectrum comment.
- `Bang/Core/EffectRow.lean`, `Bang/Core/IR.lean` — `[Lattice Eff] [OrderBot Eff]`, rows as Mathlib
  Finset join-semilattice; Yoshioka ICFP'24 citation.
- `Bang/Witness/LawTest.lean`, `Bang/Frontend/TypeCheck.lean` (`lawInstancesOf`, `checkLawOn`) — the
  #60 law-discovery/shrinking machinery that becomes arm (iii)'s check.
- `docs/notes/distributed-story.md` (§2 rung 3, §4 KV hello-world), `docs/notes/q38-handler-surface-survey.md`
  (Flix findings, grade-as-dial prior art), `docs/notes/questions/Q27-surfacing-the-grade-axis.md`
  (the "do NOT grade the row" ruling, the three-channel/k-grade operator input).
- Invariants #2 (rows are sets), #3/ADR-0030 (STM-as-handler), #5 (five primitives) — CLAUDE.md.

Web (2026-07-09):
- [Keeping CALM: When Distributed Consistency is Easy](https://arxiv.org/abs/1901.01930) — Hellerstein
  & Alvaro, CACM'20 (63(9)). The theorem, the monotone/coordination-free definitions, the assignment-
  is-non-monotone caveat, the functional-immutable-is-monotone observation. HTML: [ar5iv](https://ar5iv.labs.arxiv.org/html/1901.01930).
- [Relational transducers for declarative networking](https://arxiv.org/pdf/1012.2858) — Ameloot,
  Neven, Van den Bussche (PODS'11) — the proof model (relational transducer networks) and the
  coordination-free ⟺ monotone theorem.
- [Weaker Forms of Monotonicity for Declarative Networking](https://dl.acm.org/doi/10.1145/2809784) —
  Ameloot & Ketsman (TODS'15) — the fine-grained ladder (weaker monotonicity ⟺ more coordination).
- [Logic and Lattices for Distributed Programming](https://mwhittaker.github.io/papers/html/conway2012logic.html)
  — Conway et al., SoCC'12 (BloomL) — the non-monotone/monotone/morphism method classification, user
  lattices, whole-program CALM analysis.
- [LVars: lattice-based data structures for deterministic parallelism](https://users.soe.ucsc.edu/~lkuper/papers/lvars-fhpc13.pdf)
  — Kuper & Newton, ICFP'13 — monotone writes (⊔), threshold reads, determinism.
- [Freeze After Writing: Quasi-Deterministic Parallel Programming with LVars](https://users.soe.ucsc.edu/~lkuper/papers/lvish-popl14.pdf)
  — Kuper/Turon/Krishnaswami/Newton, POPL'14 — λLVar determinism, λLVish quasi-determinism, `freeze`
  as the statically-`QuasiDet` escape. The closest functional-calculus transfer with a proof.
- [From Datalog to Flix: A Declarative Language for Fixed Points on Lattices](https://plg.uwaterloo.ca/~olhotak/pubs/pldi16.pdf)
  — Madsen, Yee, Lhoták, PLDI'16 — lattice semantics, monotonicity tracked by types ⇒ fixpoint exists.
  [Flix: A Design for Language-Integrated Datalog](https://plg.uwaterloo.ca/~olhotak/pubs/oopsla25b.pdf) (OOPSLA'25) — first-class constraints, stratified negation.
- [Keep CALM and CRDT On](https://arxiv.org/pdf/2210.12605) — recent CALM↔CRDT connection (VLDB'23).
- [LoRe: A Programming Model for Verifiably Safe Local-First Software](https://arxiv.org/abs/2304.07133)
  — Mogk et al., ECOOP'23 / TOPLAS'24 — reactive dataflow + Viper verification; derives coordination
  placement from invariants (the modern Blazes). The recent functional-flavoured evidence the derived
  approach is tractable.
- [Making Geo-Replicated Systems Fast as Possible, Consistent when Necessary (RedBlue)](https://www.cs.otago.ac.nz/cosc440/readings/osdi12-final-162.pdf)
  — Li et al., OSDI'12 — the red/blue manual consistency labelling (the *asserted*, not *derived*, foil).
- MixT (Milano & Myers, PLDI'18), Quelea (Sivaramakrishnan et al., PLDI'15), Gallifrey (Milano et al.)
  — the information-flow / contract consistency-type family; consistency as a declared label vs CALM's
  derived-from-monotonicity grade.
