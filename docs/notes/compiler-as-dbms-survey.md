<!-- note-status: active -->
# Compiler-as-DBMS — design survey: the query-engine architecture for bang's tooling

> The operator's question (2026-07-10): *"The compiler is an interface over the IR of source code
> the way a DBMS is a query-builder + scheduler + data — can we take inspiration from DBMS
> literature for designing the engine and interface?"* This note mines that literature and the
> systems that already converged on the architecture, then prices each pillar against what bang has
> **already pinned** (ADR-0076, #80's `bang query dump`, Q34, Q43). It is an ADR-input note, not an
> ADR: it says which pillars bang adopts at which derivation rung, names the smallest shippable step
> on top of #80, and protects the novel claim — **verified views**. Web citations live in §References.

## 0 · The one-paragraph thesis

The analogy is not a metaphor — it is a **literal architecture that four industrial ecosystems have
independently converged on** (rustc/salsa, CodeQL/Glean/Kythe, Unison, Feldera/DBSP). A compiler
*is* a DBMS over the IR: `parse`/`elaborate` are the **loader** (source text → the extensional fact
base), the type-checker + analyses are **views** (derived facts computed from the base), the LSP and
build tool are **queries** against those views, incremental compilation is **incremental view
maintenance**, and diagnostics-with-blame is **provenance**. The DBMS literature already solved the
hard parts — the scheduler×rebuilder decomposition (Build Systems à la Carte), red-green
demand-driven invalidation (salsa/rustc), fact-extraction schema discipline (Glean/Kythe), and
incremental-view-maintenance-as-a-framework-property (DBSP). ADR-0076 already pinned the *spine* of
this (compiler-as-queryable-service + a content-addressed Merkle store); this survey supplies the
DBMS vocabulary that makes each pillar a **decision with named prior art and a named cost** rather
than a research cycle. The load-bearing finding: **bang's language constraints (immutability ·
purity · de-Bruijn ADTs · laws) are exactly the invariants a content-addressed incremental DBMS
requires** (the ADR-0076 thesis), so bang inherits the DBMS's best properties *by construction*
where Rust/Haskell bolt them on — and one property **no existing system has**: materialized views
whose derivation carries a machine-checked proof. That is the differentiator to name and protect.

```
   DBMS                          compiler-as-DBMS (bang)                    landed / pinned
   ─────────────────────────     ──────────────────────────────────────    ───────────────────────
   loader / bulk-insert          parse + elaborate  (source → Comp)         Bang/Frontend/*
   base relations (extensional)  the fact base: decls, rows, refs, laws     #80 `bang query dump`
   views (intensional)           type-check, effect-row infer, law-check    the checker (HM, f063c78)
   materialized view             a cached analysis result                   Q43 proof cache, #60 test cache
   query planner / optimizer     demand-driven query graph                  ADR-0076 #2 (queryable svc)
   incremental view maintenance  incremental compilation                    ADR-0076 (Merkle staleness)
   content-addressed storage     the Merkle module-DAG                      ADR-0076 (immutability ⟹ hash)
   provenance / lineage          diagnostics-with-blame, EXPLAIN            NEW — §6(f), unclaimed
   ─────────────────────────     ──────────────────────────────────────    ───────────────────────
   PROVEN materialized view      verified view (derivation = a Lean proof)  NEW — §7, the novel claim
```

---

## 1 · Pillar (a) — rustc's query system + salsa: demand-driven, memoized, red-green

**What it is.** rustc migrated from a pass-based pipeline ("run resolve, then typeck, then …") to a
**demand-driven** one: everything is a *query* — `type_of(def)`, `mir_of(def)`,
`typeck(body)` — and a query is a **pure function of its inputs, memoized** in a hashtable. The first
call computes; every later call with the same key returns the cached result. The **query DAG** is
*discovered during execution* (a query records which other queries it demanded), not declared up
front. salsa is this pattern extracted as a reusable Rust framework (used in rust-analyzer and
chalk); it is the direct descendant and the one to study for an implementation. [rustc-query],
[rustc-incr-detail], [salsa]

**The red-green algorithm (the incrementality core).** After a run, rustc persists the query DAG +
a **128-bit fingerprint (hash) of each query's result**. On the next run, `try_mark_green(node)`
walks the node's dependencies:

```
  dep is GREEN    → validated, check the next dep
  dep is RED      → an input changed; this node is dirty → re-execute
  dep is UNKNOWN  → recurse try_mark_green; still can't prove green → re-execute
  after re-exec   → hash the new result; == old fingerprint ⟹ mark GREEN anyway
                    (the "firewall": a changed input that produces an UNCHANGED result
                     stops the invalidation cascade dead)
```

The firewall is the subtle, valuable part: re-running a query whose *result* is unchanged does **not**
invalidate its consumers — invalidation propagates by *result-hash inequality*, not by
*was-re-run*. [rustc-incr-detail]

**What the migration cost, and what it bought — the two findings that price bang's version:**

1. **Fingerprint stability is the hard part, and it needs stable IDs.** rustc cannot hash a `DefId`
   (a numeric index that shifts when unrelated code moves); it must hash the *stable* `DefPath`
   (`std::collections::HashMap`) so the fingerprint is comparable across edits. Getting hashing
   "stable" is where the bugs live. [rustc-incr-detail]
   → **bang gets this for free.** The kernel is **de-Bruijn** (`Comp.subst`, `Val.shift`) and
   content-addressed (ADR-0076): the hash of an elaborated `Comp` is *already* rename- and
   position-invariant. bang has no `DefId`/`DefPath` split to reconcile — the content hash **is** the
   stable identity. The single hardest engineering problem in rustc's incrementality is a
   non-problem in bang, by construction.

2. **Fingerprinting is the *main reason* incremental rustc is sometimes slower than
   non-incremental** — computing and persisting result hashes is a real tax, and rustc pays it as a
   *separate step* layered onto compilation. [rustc-incr-detail]
   → **bang doesn't pay rustc's separate fingerprint tax.** The hash bang needs for the query cache
   is the *same* content-address it already computes for the Merkle module store (ADR-0076). One
   hash, two uses (staleness signal + store key) — "one construct per problem." The cost rustc
   eats twice, bang eats once.

**Adopt for bang:** the salsa **shape** — the checker is a graph of memoized, content-keyed queries;
change one input, only the transitively-dependent queries (by result-hash inequality) re-run. This
is ADR-0076 decision #2 made concrete. The near-term steer (ADR-0076, Q34) is unchanged: **carry
source spans + expose a type-at-position query now**; the memoization engine comes with the build
tool later.

---

## 2 · Pillar (b) — programs-as-a-database industrialized: CodeQL · Soufflé/Doop · Glean · Kythe

**What they are.** A family that made "the program is a database" literal: **extract facts once**,
then run **analyses as queries** (Datalog or a Datalog-dialect) over the fact base.

| system | fact store | query language | the lesson for bang's `dump` |
|---|---|---|---|
| **CodeQL** (GitHub) | extracted relational DB per repo | QL (OO Datalog) | extract-once, analyze-many; the schema is the product surface |
| **Soufflé + Doop** | Datalog relations | Soufflé Datalog | high-perf Datalog *compiles* the rules; join-order hints matter at scale |
| **Kythe** (Google) | the "Storage Model": entries `(source, edge, target, fact)` | graphstore / xrefs | a **tiny universal schema** (nodes+edges+facts) that every language indexer targets |
| **Glean** (Meta) | typed **predicates** (= tables), **facts** (= rows) | **Angle** (Datalog-style) | typed schema + derived predicates (= views); immutable **DB stacking** for incrementality |

**The schema-design lessons that transfer directly to #80's `dump` JSON contract:**

- **A predicate is a table; a fact is a row; a query returns facts** (Glean's framing). This is
  *exactly* `dump`'s shape: `decls` is a predicate whose facts are `{name, kind, type, row, span,
  visibility, module}`; `refs` is a predicate whose facts are name-reference edges; `laws` is a
  predicate whose facts are law instances. **`dump` already is a Glean-style extensional fact base** —
  the survey's job is to make that framing explicit so the schema is *designed*, not accreted.
  [glean-eng], [glean-repo]

- **Derived predicates = SQL views** (Glean's Angle "derives information automatically, either
  on-the-fly at query time or ahead of time"). This is the extensional/intensional split: `decls`,
  `refs` are **extensional** (extracted); `callers-of`, `every effectful decl whose row contains a
  user label` are **intensional** (derived). bang's curated CLI verbs (task #22 tier 3:
  symbols/effects/type/laws/def/refs) are **derived predicates over the extensional base** — which is
  *why* task #22 is right to implement them as thin filters over `dump`, not parallel extractors.
  One construct. [glean-eng]

- **Kythe's minimal universal schema** — everything is `(node, edge, node)` + facts on nodes —
  scales because indexers for N languages target one tiny schema. bang has **one** source language,
  so it can afford a *richer, typed* schema (Glean-style predicates) rather than Kythe's
  lowest-common-denominator triples. The lesson bang takes from Kythe is the **stability of a small
  core**: keep the extensional predicates few and stable; push richness into *derived* predicates.
  [kythe-indexer]

- **The scaling wall is fanout, and schema versioning is under-documented even at Meta.** Glean's
  incremental indexing is bounded by `O(fanout)` (a changed fact re-derives everything downstream),
  and — notably — Meta's own writeup is *silent on schema-versioning procedure*. [glean-eng] That
  silence is a **warning for bang**: an extensional fact schema exposed to users/agents (which `dump`
  is) is a **public contract**, and its evolution policy must be designed *before* v1, not
  retrofitted (see §6 the schema-evolution wall).

**Adopt for bang:** frame `dump` explicitly as **the extensional fact base of a Glean-style typed
schema**; the curated verbs are **derived predicates (views)** over it; version the schema as a
first-class public contract from day one (§6).

---

## 3 · Pillar (c) — Unison: the codebase AS a content-addressed database

**What it is.** Unison stores code **as its AST in a database, keyed by a 512-bit hash of the
syntax tree** (structure + the hashes of all dependencies — a Merkle DAG over definitions). **Names
are metadata** — a separate mapping from human names to hashes; code references dependencies *by
hash*, never by name. [unison-bigidea], [unison-lwn]

**The three consequences, and how each maps to / extends ADR-0076's Merkle pin:**

1. **Renames are free and non-breaking.** Because a caller references a callee by hash, renaming the
   callee changes only the name-metadata, not the hash — nothing downstream rebuilds or breaks.
   → **Extends ADR-0076.** ADR-0076 pins content-addressing at the *module* granularity; Unison shows
   the payoff at *definition* granularity. For bang this is the **Q34 hashing-boundary fork** made
   concrete: hash the elaborated core (like Unison's AST-hash) so that formatting, comments, and
   name changes — everything the frontend elaborates away — cannot bust the cache. bang's frontend
   already elaborates names/modules away (ADR-0076 #1, ADR-0075), so the elaborated `Comp` is exactly
   Unison's "structure, not names" hash target.

2. **Perfect caching: typecheck-once, cache-forever.** A hash-stable definition never re-typechecks;
   tests are re-run only when a dependency's hash moves.
   → **This is the shared substrate Q34's operator-input already identified** (2026-07-09): the same
   content-addressed engine serves incremental compile (ADR-0076), the Q43 proof cache, and the #60
   test cache. Unison is the existence proof that one content-addressed store subsumes all three —
   bang should build **one** engine (§5), not three caches.

3. **Content-addressing removes "dependency hell" and makes the codebase a queryable DB.** Unison's
   `ucm` codebase manager *is* a query interface over the hash-keyed store.
   → bang's `bang query` (#80) is the analog. The difference bang can exploit: Unison hashes an
   *untyped-until-checked* AST; **bang hashes an elaborated `Comp` that carries a verified semantics
   (`Source.eval`)** — so bang's content-addressed rows can carry *more* than Unison's (a proof, a
   census — §7).

**Adopt for bang:** resolve Q34's hashing-boundary fork toward **hash the elaborated core** (Unison's
lesson), with a *possible* second surface-AST hash for the LSP edit-loop (the two-hop analog Q34
names). Unison is the direct prior art for "the codebase is a content-addressed DB," which ADR-0076
already committed bang to at module granularity.

---

## 4 · Pillar (d) — DBSP / differential dataflow: incrementality as a *framework property*

**What it is.** DBSP (the engine behind Feldera; a simplification of Naiad's differential dataflow)
is a theory in which **any query expressed in the algebra is incrementalized automatically**. You
write a query over relations once; DBSP compiles it to an incremental version that, when inputs
change by a delta, recomputes **only the affected output rows** — no hand-written invalidation, no
watermarks, no manual merge logic. It represents relational deltas as **Z-sets** (rows with integer
multiplicities) and models time as a stream, so incremental maintenance is a *structural* property
of every operator (map, join, filter, aggregate, recursion). [dbsp-paper], [dbsp-blog], [feldera]

**The load-bearing question this pillar poses to bang:** could bang's **derived facts** (types,
effect rows, law instances) be expressed in an algebra so that **incrementality is *inherited*
rather than hand-written**? This is the deepest and most speculative pillar, and the honest verdict
is a fork:

```
  rustc/salsa model            DBSP model
  ─────────────────────        ─────────────────────
  invalidation is COARSE       invalidation is FINE
  (whole query re-runs;        (only changed output ROWS
   result-hash firewall        recompute; delta-precise)
   stops the cascade)
  incrementality = the         incrementality = a PROPERTY
  engine's job, per-query      of the query ALGEBRA itself
  easy to retrofit onto        needs analyses RE-EXPRESSED
  an existing checker          as algebraic relations
```

**Verdict for bang:** the salsa model is the **right v1 target** — it retrofits onto the existing HM
checker (a query is "check this decl"; the firewall is result-hash inequality) and delivers correct
incrementality at *query* granularity, which is plenty for a compiler (you rarely need
sub-declaration deltas). The DBSP model is the **north star for the fact base specifically**: `dump`'s
extensional predicates (`decls`, `refs`, `laws`) and simple derived predicates (`callers-of`,
`effectful-decls`) *are* relational, so a `dump`-over-DBSP would give **incrementally-maintained
queries for free** — an agent's saved query re-runs delta-precisely as the codebase changes. That is
a genuine post-1.0 capability, not a v1 need. **Name it, don't build it.** The seam is clean: salsa
for the *compile graph* (coarse, per-query, v1); DBSP-style IVM for the *fact-base query layer*
(fine, relational, post-1.0) if agent-query workloads justify it.

---

## 5 · Pillar (e) — Build Systems à la Carte: the scheduler × rebuilder decomposition (the unifier)

**What it is.** Mokhov/Mitchell/Peyton Jones (ICFP'18; JFP'20) show every build system factors into
**two orthogonal choices**, and *any* combination is a correct build system: [balc-paper], [balc-jfp]

```
  SCHEDULER   — in what ORDER are tasks built?
                topological (Make) · restarting (Excel) · suspending (Shake, salsa)
  REBUILDER   — is a task (re-)built, or is the cache reused?
                dirty-bit (Make) · verifying-traces / hashes (Shake) ·
                constructive-traces (Bazel/CloudBuild) · deep-constructive (Nix)
```

**Why this is the pillar that *unifies* all the others** — it is the abstract frame the operator's
Q34-input (2026-07-09) already reached for, and it names each other system as a `(scheduler,
rebuilder)` point:

| system | scheduler | rebuilder |
|---|---|---|
| Make | topological | dirty-bit (mtime) |
| salsa / rustc | **suspending** (demand-driven) | **verifying-traces** (result fingerprints) |
| Bazel | restarting/topological | **constructive-traces** (content-addressed action cache) |
| Nix | topological | **deep constructive** (hash the transitive input closure) |
| Unison | suspending | verifying (AST-hash) |

**The pin this gives bang.** ADR-0076 already commits bang to a **content-addressed Merkle-DAG**,
which in this vocabulary is a **constructive-trace / deep-constructive rebuilder** (Bazel/Nix rung —
the strongest, cache-a-hit-is-provably-right rung). The choice bang has *not* yet pinned is the
**scheduler**: it should be **suspending** (salsa's demand-driven order), because a suspending
scheduler is what lets the LSP ask "type at this position?" and compute *only* the transitively-needed
queries — the whole point of ADR-0076 #2. So in one sentence:

> **bang's tooling engine = a *suspending scheduler* (salsa) over a *deep-constructive-trace
> rebuilder* (the ADR-0076 Merkle store).** Both choices already have their prior art and their
> justification; à la Carte is the frame that says this combination is *correct by construction*.

**And the dogfood observation Q34 already made:** the repo's own `tools/` hand-rolls ~15 instances of
this pattern (every `gen-*.py --check` fitness leg is a *staleness query* = a one-off rebuilder). The
engine would **subsume them all** — the à la Carte point that a build system is *one* abstraction, not
N ad-hoc scripts. And because the engine's correctness precondition ("tasks are pure functions of
their hashed inputs") **is bang's language guarantee**, the engine is a natural *bang program*
post-IO — the ADR-0076 generative-constraints thesis applied one level up.

**Adopt for bang:** state the engine as `(suspending scheduler, deep-constructive rebuilder)`
explicitly in the eventual build-tool ADR; treat à la Carte as the design's correctness argument;
plan for the engine to subsume the `tools/ gen-*.py --check` legs as its first instances.

---

## 6 · Pillar (f) — provenance: why/how-provenance → diagnostics-with-blame (EXPLAIN for type errors)

**What it is.** Database **provenance** answers *why* a row is in a query result and *how* it was
derived. The Green et al. **semiring framework** is the deep result: annotate each base tuple with a
variable, then a query's output annotation is a **polynomial** in a semiring — **multiplication =
joint use** (a join needs both inputs), **addition = alternative derivations** (a union of two ways to
derive the same row). Coarser provenance (why-provenance = *which* input subsets suffice; lineage =
*which* inputs are relevant) are quotients of the full **how-provenance** polynomial. [prov-survey],
[prov-semiring]

**The mapping to compilers — this is the sharpest and least-exploited analogy:**

```
  DB provenance                     compiler analog
  ─────────────────────────         ─────────────────────────────────────────
  base tuple annotation             a source SPAN on a fact
  how-provenance polynomial         the DERIVATION TREE of an inferred type / effect row
  why-provenance (witness subset)   the MINIMAL set of decls that force a type error
  lineage                           "which source locations does this row's type depend on?"
  provenance-aware query            an EXPLAIN for a type error / an effect-row obligation
```

Type inference *is* a semiring-provenance computation waiting to be named: an inferred effect row is
a **join (∪) of contributing effects**, each traceable to the `perform`/handler that introduced it —
that union *is* the additive structure; the unification that forces two rows equal *is* the
multiplicative (joint-use) structure. So "why does this function have `Div` in its row?" has a
**principled answer**: the provenance polynomial names the exact `perform` sites and the derivation
path. This is EXPLAIN-for-type-errors with a database-theory foundation, not an ad-hoc heuristic.

**Why bang is unusually well-placed to ship this.** Provenance needs every derived fact to carry the
lineage of its inputs. bang's derived facts are computed by a **verified** semantics over a
**de-Bruijn** term with **spans** (ADR-0076 #2 mandates carrying spans *now*) — so the derivation
tree is *already present in the checker's structure*; provenance is a matter of *retaining* it, not
reconstructing it. And effect rows being **sets with a lattice join** (invariant #2, ADR-0018) means
the additive semiring structure is *literally the row algebra bang already has*.

**Adopt for bang:** name **diagnostics-with-blame / EXPLAIN** as a derived-fact capability the
queryable-service architecture *enables* (not a v1 build). The near-term steer is again just
ADR-0076 #2 (carry spans); the provenance polynomial is a post-1.0 view that the span-carrying
checker makes cheap. This is a *research-grade differentiator* worth a design note when the LSP lands.

**The schema-evolution wall (named honestly).** `dump` is a public fact schema; the Glean silence
(§2) warns that schema evolution is the under-designed part. bang's **0.x version policy** (pre-1.0,
breaking changes allowed) collides with "agents write scripts against `dump`'s JSON": every schema
change breaks every saved agent query. The mitigation is **schema versioning as a first-class
contract from v1**: `dump` emits a `schemaVersion` field; the reference documents the schema as a
versioned artifact; additive changes (new predicates/fields) bump a minor version, removals/renames
bump major. This is the *one* piece of DBMS discipline bang must adopt *eagerly* (not post-1.0),
because it governs an already-shipping surface (#80). Cost: a version field + a documented evolution
policy + a schema-snapshot test (the derivation-ladder "test" rung — a golden `dump` output that
fails CI when the schema drifts un-versioned).

---

## 7 · THE NOVEL CLAIM — verified views (the differentiator to protect)

**The claim.** Every system surveyed has **materialized views** — cached derived facts (rustc's
fingerprinted query results, Glean's derived predicates, Unison's cached typechecks, DBSP's
maintained views). **None has a *proven* materialized view: a derived fact that carries a
machine-checked proof of its own derivation.** bang can, because its content-addressed rows are
elaborated `Comp` terms with a *verified* semantics behind them.

```
  ordinary materialized view          VERIFIED view (bang)
  ──────────────────────────          ─────────────────────────────────────────────
  row = cached derived value          row = derived value + a Lean proof it's correct
  trust = "the engine computed it"    trust = "the kernel checked the derivation"
  staleness = hash inequality         staleness = hash inequality (same Merkle move)
  a wrong cache = a silent bug         a wrong cache = UNREPRESENTABLE (proof won't typecheck)
```

**Two concrete instances already sketched in the repo — this claim is not speculative, it names a
pattern two landed/designed pieces already exhibit:**

1. **Q43's content-addressed proof cache** (proof-export-survey.md) is *precisely* a verified view:
   a `law`'s obligation is elaborated to a `Comp`, a Lean proof is discharged and **cached on the
   term's hash**; a cache hit means "this exact term was proven," and a hash miss means the proof is
   about a *different* term (fail-loud, never silently trusted). The proof cache re-check on a clean
   kernel is the "a wrong cache is unrepresentable" backstop. In DBMS terms: **a materialized view
   whose maintenance guarantee is a machine-checked derivation.**

2. **The axiom census as a schema invariant.** bang's gate discipline (`#print axioms` ⊆ {`propext`,
   `Classical.choice`, `Quot.sound`}) is, in schema terms, an **integrity constraint on a verified
   view**: the census *is* metadata on the proof row asserting "this derivation uses only trusted
   axioms." A verified view carries its census as a schema invariant the CI re-checks — the DB
   analog of a `CHECK` constraint, but the checked property is *soundness*.

**Why no existing system has this.** rustc/salsa fingerprints assert *sameness*, not *correctness*
(a fingerprint says "the result didn't change," never "the result is right"). Glean/CodeQL derive
facts by Datalog rules trusted operationally, not proven. Unison caches a *typecheck* (a real
guarantee, but of type-safety, not of arbitrary user-stated laws). DBSP maintains views *correctly by
construction of the engine* — but the engine's correctness is a meta-theorem, not a per-row
certificate. bang's verified view is stronger on the exact axis all of them stop at: **the row
carries its own proof, kernel-checked, content-addressed, GC'd by Merkle-reachability.**

**Assessment as differentiator + paper.** This is a **genuine, defensible novelty** — "proven
materialized views / certified incremental view maintenance" is not, to this survey's knowledge, in
the literature (semiring provenance *records* derivations but does not *prove them correct*; verified
build systems prove the *engine*, not the *rows*). The paper shape: *"Verified Views: content-addressed
materialized views carrying machine-checked derivations, realized in a language whose own constraints
make the content-addressing sound."* The honest caveat (a wall, §8): the novelty is **per-row proof
obligations don't come free** — the Q43 fuzz→prove seam scopes them to the total fragment and to
*laws the user opts into proving*, so verified views are a **rung**, not the default; the claim to
protect is "bang *can* have them and no one else can," not "everything is proven."

---

## 8 · ADR-INPUTS (decision-shaped)

### The pillar-adoption table — which rung, which timing

The **derivation-strength ladder** (SOUL: generate > test > convention) maps directly onto
**materialized-view vs computed-view**: *generate* = a materialized (cached) view whose staleness is
hash-checked; *test* = a computed view checked against an oracle; *convention* = the anti-pattern
(hand-maintained, drifts). bang should climb to the highest rung each pillar affords:

| pillar | bang adopts | rung | timing |
|---|---|---|---|
| (a) salsa demand-driven queries | the checker as a memoized content-keyed query graph | **generate** (materialized, hash-keyed) | shape now (spans + type-at-pos query, ADR-0076 #2); engine w/ build tool |
| (b) Glean fact-schema | `dump` = extensional base; curated verbs = derived predicates (views) | **generate** (dump) / derived views | **`dump` shipping now (#80)**; schema versioning **eager** |
| (c) Unison content-addressing | hash the **elaborated core** (Q34 fork resolved) | **generate** (Merkle staleness) | pinned by ADR-0076; hashing-boundary decided at store-build |
| (d) DBSP IVM | fact-base query layer *could* inherit incrementality | **generate** (framework-incremental) | **post-1.0** — north star, not a v1 need |
| (e) à la Carte | engine = suspending scheduler × deep-constructive rebuilder | frames the whole | ADR at build-tool time; subsumes `tools/*.py --check` |
| (f) provenance | diagnostics-with-blame / EXPLAIN as a derived view | **test**→**generate** | post-1.0; spans-now makes it cheap |
| **(§7) verified views** | proven materialized views (Q43 proofs, census invariants) | **generate + PROOF** (novel top rung) | Q43 R1 first; the differentiator |

### The smallest shippable step (on top of #80's `dump`)

**`dump` as a versioned fact schema + a documented extraction contract.** Concretely, three moves,
all additive to the in-flight #80/#22 work, none requiring the build engine:

1. **`dump` emits `schemaVersion`** and the reference documents the JSON as a **versioned public
   contract** — framed in Glean's vocabulary (predicates = the top-level arrays; facts = their
   elements; the curated verbs are *derived predicates* over it). This closes the schema-evolution
   wall (§6) *before* agents accrete scripts against an unversioned surface.
2. **A schema-snapshot CI test** (the "test" rung of the ladder): a golden `dump` output that fails
   when the schema drifts without a version bump — drift becomes CI-caught, not convention-hoped.
   This is itself the à la Carte point in miniature (a staleness query the engine will later subsume).
3. **Document the extensional/intensional split in the reference**: which predicates are *extracted*
   (`decls`, `refs`, `laws`, `imports`) vs *derived* (every curated verb), so users/agents know the
   base they compose over is stable and the views are conveniences. This is a doc move, ~an afternoon.

This is the correct smallest step because it (i) rides #80/#22 verbatim, (ii) makes the DBMS framing
*real* rather than aspirational (a versioned schema *is* the "extensional fact base" claim, tested),
and (iii) buys the one piece of discipline (schema versioning) that is expensive to retrofit and
governs an already-shipping surface — the same "decide-now-because-retrofit-is-costly" logic ADR-0076
#2 used for span-carrying.

### What waits for post-1.0

- **The memoized query *engine*** (salsa-style suspending scheduler over the Merkle store) — pinned in
  shape by ADR-0076 + à la Carte (§5), built with the module system / build tool, which is behind the
  stdlib (Q34). Sequencing unchanged.
- **DBSP-style framework-incremental fact queries** (§4) — a north-star capability for agent-query
  workloads; the salsa model covers v1.
- **Provenance / EXPLAIN-for-type-errors** (§6) — a post-1.0 derived view the span-carrying checker
  makes cheap; worth a design note when the LSP lands.
- **Verified views beyond Q43** (§7) — Q43 R1 (export-goal-with-sorry) is the first instance; the
  general "proven materialized view" framing is the paper, post the proof cache landing.

### The novel claim to protect

**Verified views** (§7): content-addressed materialized views carrying machine-checked derivations —
Q43's proof cache and the axiom census as its first instances. No surveyed system (rustc, Glean,
Unison, DBSP) proves its *rows* correct; they cache *sameness* or prove the *engine*. This is bang's
defensible differentiator and a plausible paper — **name it in the eventual build-tool/query ADR so a
later session doesn't collapse it into "just a cache."** It is the ADR-0076 generative-constraints
thesis reaching its sharpest point: bang's constraints don't just make the cache *correct*, they make
the cached rows *proven*.

### Honest walls named

- **Lean-side fact-extraction cost.** `dump` extracts facts from the Lean-implemented frontend; each
  new predicate is Lean code in the extraction path, not free. Keep the extensional predicates few
  and stable (Kythe's small-core lesson, §2); push richness into derived views.
- **Schema evolution vs the 0.x version policy** (§6) — the collision between "breaking changes
  allowed pre-1.0" and "agents write durable scripts against `dump`." Mitigation = eager schema
  versioning; this is the wall the smallest-step directly addresses.
- **Verified views are a rung, not a default** (§7) — per-row proof obligations are real work, scoped
  by Q43 to the total fragment and to opt-in laws. The claim is "bang *can*, uniquely," not
  "everything is proven."
- **DBSP re-expression cost** (§4) — inheriting framework-incrementality needs analyses re-expressed
  as relational algebra; the salsa model avoids this and is the right v1 call. Named so a later
  session doesn't over-reach for DBSP elegance before agent-query workloads justify it.

---

## References

- **rustc query system / demand-driven compilation**: Rust Compiler Development Guide —
  "Queries: demand-driven compilation" (<https://rustc-dev-guide.rust-lang.org/query.html>),
  "Incremental compilation in detail" (the red-green algorithm, fingerprints, stable-hash cost)
  (<https://rustc-dev-guide.rust-lang.org/queries/incremental-compilation-in-detail.html>),
  "Salsa" (<https://rustc-dev-guide.rust-lang.org/queries/salsa.html>). [rustc-query],
  [rustc-incr-detail], [salsa]
- **salsa** (the reusable incremental-query framework; rust-analyzer, chalk):
  <https://github.com/salsa-rs/salsa>. [salsa]
- **CodeQL / Soufflé / Doop** (Datalog program analysis, fact extraction):
  Scholz et al., "On Fast Large-Scale Program Analysis in Datalog" (Soufflé);
  "Porting Doop to Soufflé"
  (<https://www.academia.edu/33743516/Porting_Doop_to_Souffl%C3%A9>);
  Youn et al., "Declarative static analysis for multilingual programs using CodeQL", SPE 2023
  (<https://onlinelibrary.wiley.com/doi/abs/10.1002/spe.3199>). [codeql-doop]
- **Glean** (Meta): "Indexing code at scale with Glean", Engineering at Meta, 2024-12-19
  (predicates=tables, facts=rows, Angle, derived predicates, immutable DB stacking, O(fanout))
  (<https://engineering.fb.com/2024/12/19/developer-tools/glean-open-source-code-indexing/>);
  repo (<https://github.com/facebookincubator/Glean>). [glean-eng], [glean-repo]
- **Kythe** (Google): the Storage Model + writing an indexer
  (<https://kythe.io/docs/schema/writing-an-indexer.html>). [kythe-indexer]
- **Unison** (content-addressed code): "The big idea"
  (<https://www.unison-lang.org/docs/the-big-idea/>); "Programming in Unison", LWN
  (<https://lwn.net/Articles/978955/>). [unison-bigidea], [unison-lwn]
- **DBSP / differential dataflow**: Budiu et al., "DBSP: Automatic Incremental View Maintenance for
  Rich Query Languages", VLDB 2023 (<https://arxiv.org/pdf/2203.16684>); Feldera
  (<https://www.feldera.com/>); "How Feldera Works"
  (<https://www.junaideffendi.com/p/how-feldera-works-a-true-incremental>). [dbsp-paper],
  [dbsp-blog], [feldera]
- **Build Systems à la Carte**: Mokhov, Mitchell, Peyton Jones, ICFP'18
  (<https://www.microsoft.com/en-us/research/wp-content/uploads/2018/03/build-systems-final.pdf>);
  JFP'20 "Theory and practice"
  (<https://ndmitchell.com/downloads/paper-build_systems_a_la_carte_theory_and_practice-21_apr_2020.pdf>).
  [balc-paper], [balc-jfp]
- **Provenance**: Cheney, Chiticariu, Tan, "Provenance in Databases: Why, How, and Where"
  (<https://homepages.inf.ed.ac.uk/jcheney/publications/provdbsurvey.pdf>); Green, Karvounarakis,
  Tannen, "Provenance Semirings" (the how-provenance semiring framework). [prov-survey],
  [prov-semiring]
- **Internal anchors**: ADR-0076 (compiler-as-queryable-service + Merkle content-addressed store —
  the pinned architecture this survey serves); `docs/notes/questions/Q34-module-system-tooling-forks.md`
  (the hashing-boundary + LSP-query forks + the 2026-07-09 reusable-engine operator-input);
  `docs/notes/proof-export-survey.md` (Q43 — the content-addressed proof cache = the first verified
  view); issue #80 / task #22 (`bang query dump` — the extensional fact base this survey frames);
  invariant #2 / ADR-0018 (effect rows are sets with a lattice join — the provenance additive
  structure); the SOUL derivation-strength ladder (generate > test > convention — the
  materialized-vs-computed-view mapping).
