<!-- note-status: active -->
# The taxonomy of laws — model-shaped vs morphism-shaped, and where a property lives

> Direction input (operator question, 2026-07-10): "is there a broader pattern hiding behind
> monotonicity, transitivity, and other properties?" Answer: yes, two-level. This note pins it
> as ADR-input for Q38 (Stage-7 unification) and as the standing criterion for every future
> "should X be tracked in the type system?" question. Grounds: `calm-as-grade-survey.md`
> (the leaf-law/composition split this generalizes), `proof-export-survey.md` (Q43 = the leaf
> prover), ADR-0068 (conditional laws), the binary-LR machinery (◊4 — the fundamental-lemma
> proof shape), Plotkin–Power (effects = algebraic theories).

## 1 · Two kinds of law (where the quantified variables live)

```
MODEL-shaped                              MORPHISM-shaped
"this thing IS a structure"               "this map PRESERVES structure"
────────────────────────────              ─────────────────────────────
assoc/comm/idem  (merge is a join)        monotone      (preserves ⊑)
transitivity     (R is an order)          linear/0-1-ω  (preserves resource count)
unit laws        (monoid identity)        pure/φ-bounded (preserves "at most φ effects")
                                          continuous · differentiable · strict …
```

Both are Horn clauses over a signature (∀ x̄, premises → equation) — ONE law machinery
(`lawInstancesOf` / `bang test` / Q43) checks both; `trans` and monotonicity are the same
ADR-0068 conditional-law shape. But they do different work:

- **Model-shaped laws license STRUCTURES** (three laws ⇒ semilattice ⇒ CRDT). Leaf-only by
  nature: nothing composes; check the object once at its definition.
- **Morphism-shaped laws license COMPOSITION** (monotone∘monotone = monotone). A property
  closed under composition + identity defines a category the program can live in — and a
  GRADE is the type system's bookkeeping of which category that is. Only these lift into
  rows/grades.

**The criterion (the reusable rule):** composition-closed → gradeable (a lattice instance on
the graded-row mechanism); not composition-closed → leaf law (fuzz → prove); implied by the
type alone → free (parametricity); neither → runtime fail-loud.

```
free       follows from the TYPE (parametricity, naturality)     zero obligations
graded     morphism-shaped, composes → row/grade tracks it       soundness = ONE fundamental lemma
law        model-shaped → checked at the leaf                    fuzz (today) → prove (Q43, total-only)
runtime    neither → fail-loud check                             escapedCap-style (ADR-0063)
```

## 2 · The retro-explanation of bang itself

The EFFECT ROW was already this pattern: "performs at most φ" is morphism-shaped and
composition-closed; rows compose by join. The row is the FIRST grade bang shipped;
multiplicity (0/1/ω, Q27) the second; monotonicity (calm-as-grade, ruled distinct-lattice)
the third. The operator's distinct-lattice ruling is this pattern as engineering: one
mechanism (grade lattice + join-on-composition), one instance per composition-closed
property. Soundness of ANY grade = a fundamental lemma of a logical relation over the
fragment (the paid-once composition lemma; LVish's quasi-determinism proof is exactly this;
bang's binary-LR machinery is the house proof shape for it).

## 3 · The Q38 punchline (Stage-7 ADR-input)

The constructs unify one level up:

| construct | is a presentation of | carrier | laws |
|---|---|---|---|
| **trait** | an algebraic theory | a data carrier (`Self`) | user-declared (`law comm(a,b): …`) |
| **effect** | an algebraic theory (Plotkin–Power) | computations | the effect's equations (state: get-get · get-put · put-get · put-put) |
| **module** | a named signature | — | none (visibility only) |

Not analogy — Plotkin–Power: effects ARE algebraic theories, handlers ARE their algebras.
This reframes Q38 from "can three syntaxes merge" to "one mathematical object, three coats;
what differs is the carrier and the binding time." Whatever surface Stage 7 picks, the
SEMANTIC unification is already fixed.

**Concrete near-payoff (post-Stage-7):** a user-written handler can be law-checked against
its effect's declared theory with the SAME `lawInstancesOf` machinery — handler correctness
as laws, no new construct. (A `handler H : State` that violates put-put is a red `bang test`,
today's machinery, tomorrow's surface.)

## 4 · What this note is NOT

Not a scoped unit. It decides nothing; it names the pattern so Q38's ADR and every future
"track X in types?" fork can cite one criterion instead of re-deriving it. First consumers:
the Stage-7 surface ADR (Q38), the monotonicity-grade implementation (post-v1), and the
handler-theory law-checking idea (backlog until Stage 7 lands).

## 5 · User-definable axes (operator direction, 2026-07-10)

> "If they're the same underlying pattern, the same machinery should support them all with
> different semantics." — Yes. The abstraction is a **user-defined grade axis**:

```
1. an ALGEBRA        the grade lattice/ordered semiring (join = composition)   ← user declares
2. LEAF assignments  which grade each op carries                               ← user annotates
3. PROPAGATION       fold the algebra along composition                        ← GENERIC (GradeVec,
                                                                                 the distinct-lattice ruling)
```

Users already extend one lattice today: a user `effect` decl (ADR-0092) adds POINTS to the
row's powerset lattice. Axes generalize that to new DIMENSIONS. Shipped precedent: **F# units
of measure** (user abelian group, type-level fold, zero semantic proof); Granule (security
lattices); taint = powerset; cost = ℕ semiring; monotonicity = the two-point lattice.

**The bootstrap:** an axis is admissible iff its algebra's own laws hold — assoc/comm/idem/
join-monotonicity are MODEL-shaped leaf laws, so the law machinery is the admissibility gate:
`lawInstancesOf` discovers them, `bang test` fuzzes, Q43 proves (total fragment — covered by
the total-only ruling). Laws gate grades; grades transport laws — §1's two halves close into
a loop.

**The soundness split (pricing):**
- **FREE tier** — axes whose meaning is "over-approximation of the trace fold" (taint, cost,
  units, the row itself): the fundamental lemma is proved ONCE, parametrically over
  `[Lattice G]` (Katsumata graded-monad semantics; the same shape as row soundness).
  One hard meta-level Lean proof, amortized over every future axis.
- **PRICED tier** — axes claiming behavior beyond the trace (monotonicity: a fact about the
  function's extension): owe a per-axis bridge proof (trace-fold ⇒ semantic claim), exported
  as a Lean obligation. Supported, opt-in, honestly expensive.

**The caveat, from banked evidence:** the rq38 census shows surface unifications pay at the
implementation layer — so unify the MACHINERY (one propagation engine + one law gate), keep
`trait`/`effect`/`axis` as separate surface declarations until the Stage-7 stress test rules.
Kernel invariant #5 untouched: axes are elaborator/type-layer; the five primitives never
learn they exist.
