<!-- note-status: active -->
<!-- describes: Bang/Core/Semantics/Eval.lean Bang/Spec.lean Bang/Meta/BinaryLR.lean Bang/Backend/AbstractMachine.lean Bang/Backend/Wasm.lean @ 5312ec0419dfc25fc38e1920f6e8dfc3cf298c8f -->
# Term Relation Algebras for bang — applicability of Gavazzo LICS 2026

> **Summary.** Gavazzo's Term Relation Algebras (TRAs) could become a useful
> **post-v1 metatheory sidecar** for deriving generic congruence or rewrite-system
> results. They are **not functionally relevant to bang's current kernel, LR, or
> compiler critical path**, and do not unblock a flagged headline. Extending TRA
> to bang's effectful, graded, fresh-identity setting is plausible research in its
> own right; adopt it only if a bounded effectful probe derives a real bang theorem
> with less semantic-specific machinery than the existing proof.
>
> **Read when:** considering algebraic/pointfree metatheory, a second relational
> semantics, declarative rewrite systems, or a post-v1 research paper on unifying
> effectful metatheory. This is research input, not an ADR.

## 0. Decision

| Question | Verdict |
|---|---|
| Can TRA close current `lr_*`, `zero_usage_erasable`, or compiler obligations? | **No.** The residuals are typed/indexed representation and simulation obligations outside the paper's proved envelope. |
| Can TRA replace graded CBPV, `Source.eval`, BinaryLR, CalcVM calculation, or Wasm simulation? | **No.** Those mechanisms solve different problems. |
| Could a TRA layer reduce future repeated metatheory? | **Maybe.** The strongest candidate is compatibility/congruence for an effectful operational relation or a future rewrite system. |
| Is extending TRA to bang scientifically useful? | **Yes, potentially.** Effects + grades + fresh handler identities + step-indexing go beyond the paper and could be a research contribution. |
| Is that extension product-critical? | **No.** It is a parallel post-v1 track unless a real proof family appears that it can replace. |

**Ruling:** record the technique; do not sequence it ahead of any current
checkpoint. Re-open only through the spike in §6.

## 1. What the paper buys

A TRA is a pointfree algebra of binary term predicates. It combines a complete
relation algebra with operations for compatible constructor closure, simultaneous
substitution, structural recursion/Howe extension, and open/closed terms
([gavazzo-lics26-tra], pp. 8–17).

The paper's central local-to-global bridge is:

```text
 deterministic ground rules + GIP (inversion) + GCP (conservation)
       ├─ parallel reduction is confluent
       ├─ induced big-step evaluation is deterministic
       └─ open applicative bisimilarity is a congruence
```

GIP says computation occurs only at the relevant introduction/elimination
interaction (p. 19). GCP says primitive computation is conserved by compatible
related operands/substitution (p. 23). The combined bridge is Theorem 37 (p. 24).

### Proven envelope versus bang

| Paper establishes | Paper leaves open or omits | bang requires |
|---|---|---|
| rewriting and parallel reduction | type-theory metatheory | typed configurations and stack typing |
| big-step evaluation determinacy | effects and quantitative relations | effect rows and multiplicity grades |
| applicative-bisimilarity congruence | logical relations | step-indexed biorthogonal LR |
| syntax-independent substitution laws | small-step/SOS development | CK stacks and identity-keyed dispatch |
| first/second-order and nominal term models | a mechanized proof artifact | Lean-checked definitions and axioms |

The publication page reports no proof-assistant artifact or repository. Several
central arguments are proof sketches. A faithful production adoption therefore
starts by mechanizing infrastructure, not merely instantiating an existing Lean
library.

## 2. Where it would sit

TRA would be a **derived layer above** the canonical syntax and dynamics:

```text
 Comp / Config + substitution + Source.step
                    │
          prove TRA structure + GIP/GCP
                    │
                    ▼
      generic congruence / confluence results
```

It does not occupy an arrow in the verified compilation spine:

```text
 Source.eval ──agreement── evalD ──calculation── CalcVM ──simulation── Wasm
      │
      └── BinaryLR ──adequacy── contextual equivalence
```

The distinction is structural:

- TRA proves global properties **within one formal system** from local laws.
- `evalD_agrees_source`, `compile_correct`, and `compile_forward_sim` relate
  **different systems** and must carry value/store/freshness correspondences.
- BinaryLR proves a typed, step-indexed, two-program contextual theorem; the
  paper's applicative bisimilarity is not that relation.

Evidence: `evalD_agrees_source` is the Source↔evalD bridge
(`Bang/Backend/AbstractMachine.lean:6839`); `compile_correct` is the evalD↔CalcVM
bridge (`Bang/Backend/AbstractMachine.lean:3452`); the source↔Wasm headline is
`Bang/Spec.lean:325`. ADR-0035 fixes LR-for-equivalence versus
simulation-for-compilation as complementary methods.

## 3. Fit with the current kernel

The pure fragment should fit the paper's operational decomposition: terms have
introduction/elimination forms, and β/let/force compute by substitution. That is
not the decisive case.

The decisive case is bang's actual configuration:

```text
Config = next-fresh identity × evaluation stack × focused computation
```

`Source.step` both performs substitution and manipulates machine state:

- handler installation mints a globally fresh identity;
- dispatch searches by capability identity, not nearest label;
- state/transaction/custom handlers reconstruct resumptive stacks;
- an unresolved escaped capability terminates fail-loud.

These operations are visible at `Bang/Core/Semantics/Eval.lean:78`. The paper
allows GCP to be reformulated around a computation operation other than
substitution (p. 23, fn. 11), but bang must then **design and prove** that custom
conservation law. If the law quantifies over the whole freshness/stack invariant,
it has merely moved the existing semantic proof into a new vocabulary.

### Determinism is a false-positive target

Do not adopt TRA because it re-proves evaluation determinism. `Source.step`,
`Config.run`, and `Source.eval` are functions (`Bang/Core/Semantics/Eval.lean:82`,
`:221`, `:234`), and cross-fuel consistency of completed results already follows
from `Config.run_done_add`. A TRA determinism proof would be useful only for a
new relational or nondeterministic semantics.

## 4. Why it does not unblock the flagged set

| Headline | Actual obligation | Why TRA does not supply it |
|---|---|---|
| `lr_sound` | raw-focus observation versus capability-substituted canonical reshape (`Bang/Spec.lean:233`) | representation/observation mismatch, not missing generic congruence |
| `lr_fundamental{,_closed}` | identity dispatch, fresh-counter alignment, resumption stacks, plus ordinary LR compatibility cases (`Bang/Meta/BinaryLR.lean:930`) | requires the existing typed step-indexed relation or a stronger replacement |
| `zero_usage_erasable` | two different fillers are contextually equivalent (`Bang/Spec.lean:165`) | quantitative grade-zero reasoning is outside the paper |
| `handler_compiles` | future cross-language handler equivalence; current predicates are placeholders (`Bang/Backend/Wasm.lean:2151`) | TRA has no cross-language compiler refinement result |

The surveyed `lr_sound` obstruction is statement-level: the observation needs an
answer/representation determined by construction. A different proof calculus does
not invent that missing carrier.

## 5. Where extension could be useful

### Functionally relevant route

TRA earns a production role only when bang has **multiple declarative relations**
that repeatedly need the same compatibility/confluence argument. Plausible future
consumers:

1. a declarative optimizer or user rewrite system;
2. an effectful operational equivalence lighter than full BinaryLR;
3. multiple surface/core rewrite passes sharing one orthogonality proof;
4. a relational nondeterministic semantics distinct from the executable oracle.

None exists as a current blocking proof family. Until one does, TRA is parallel
research rather than architecture.

### Research-relevant route

A faithful extension to bang would add several dimensions the paper names as
future work:

- algebraic effects and resumptive handlers;
- quantitative/graded predicates;
- step-indexed logical relations and recursive types;
- fresh generative identities and capability escape;
- configuration rather than term-only dynamics.

That combination is potentially publishable. Its value would be a theorem of the
form “one effectful quantitative local law yields several global metatheorems,”
not merely a TRA encoding of bang. The cost is research-scale because the paper
has no mechanized substrate and the extension risks reconstructing BinaryLR.

## 6. Falsifiable adoption spike

Create an inert probe under `scratch/`; do not change frozen semantics.

### Gate A — calibration, not success

1. Formalize only the relation-algebra fragment required for induced-evaluation
   determinism.
2. Instantiate `ret`, `let`, application, thunk and force.
3. Re-derive determinism.

Gate A checks mechanization cost. Passing it alone is **not** a reason to adopt.

### Gate B — the decision

Add one identity-keyed one-shot state handler, including fresh installation,
`perform`, dispatch, and resumption. Then require:

1. a local operational decomposition/GIP;
2. a BANG-specific conservation law proved from the transition rules;
3. generic compatibility/congruence of the induced applicative bisimilarity;
4. a bridge to one existing bang observation or law—no disconnected new
   equivalence relation.

### GO / NO-GO

| GO only if all hold | Stop if any holds |
|---|---|
| effectful Gate B closes without `sorry` or new axioms | only the pure/determinism calibration closes |
| GCP is local and reusable | GCP restates the whole machine simulation/invariant |
| one real proof becomes smaller or reusable | the probe rebuilds `Vrel/Crel/KrelS` under new names |
| the new relation connects to existing observations | bridging recreates the raw↔reshape/answer-carrier wall |
| infrastructure cost is proportionate to removed proof | generic framework exceeds the bang-specific proof it replaces |

## 7. Revisit triggers

Re-open this track only when at least one trigger fires:

- a second declarative reduction/rewrite semantics needs congruence or confluence;
- two or more direct proofs duplicate the same compatible-closure argument;
- the post-v1 paper programme explicitly targets effectful/graded TRA as a
  contribution;
- a maintained Lean/Rocq/Agda TRA artifact appears;
- BinaryLR is stable and the project deliberately funds an alternative
  operational-equivalence layer.

Do **not** re-open merely because a current `lr_*` proof is difficult: the paper
does not remove the current representation and indexing obligations.

## References

- [gavazzo-lics26-tra] Francesco Gavazzo, “An Algebraic Approach to Formal System
  Metatheory,” LICS 2026, DOI 10.4230/LIPIcs.LICS.2026.50.
- Architecture split: `docs/decisions/0016-two-hop-architecture-calcvm-and-wasmfx.md`.
- Proof-method split: `docs/decisions/0035-lr-for-equivalence-simulation-for-compilation.md`.
- Current proof position: `CONTEXT.md`.
