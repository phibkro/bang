---
type: design-question
title: "Module-system + tooling SURFACE forks (file-vs-block · qualified-vs-open · visibility · the hashing boundary) — architecture pinned by ADR-0076"
description: "the concrete module-system surface forks (granularity · imports · visibility · hashing · LSP); architecture pinned by ADR-0076"
status: open
area: tooling
ties: ["Q32", "Q33", "ADR-0046", "ADR-0047", "ADR-0076"]
see-also: ["paths/archive/PATH-polymorphism.md"]
---
**Question**: the concrete SURFACE decisions for the module system + tooling, once it's built. The
ARCHITECTURE is pinned (**ADR-0076**: modules elaborate to the flat kernel · the compiler is a queryable
content-addressed service · the module DAG is acyclic + generated · incremental compilation falls out of
immutability+purity by construction — the constraints are generative). These are the remaining forks.

**Why deferred**: the module system is forced by a growing stdlib (PATH-polymorphism bites 1-2 → generic
`List`/`Monoid`/... modules); a FIRST generic stdlib can ship as an EXTENDED PRELUDE (like Char/Str today,
no modules). So the surface is decided when the prelude stops scaling / users want their own modules. Only
ADR-0076's decision #2 (checker → queryable: carry source SPANS, a type-at-position query) steers NOW.

**The forks (decide at build time):**
1. **Module granularity** — file-based (one module = one file, Rust/Python) vs explicit `module { … }`
   blocks (Lean). File-based is simpler + matches content-addressing (hash the file); blocks allow multiple
   per file.
2. **Namespacing / imports** — qualified-only (`List.map`) vs open/`use` (bring names into scope) vs both.
   Name-resolution strategy + collision rules (ambiguity = a loud error, per ADR-0046/0047's determinism).
3. **Visibility / interface** — public/private exports; deep modules (Ousterhout — narrow interface, deep
   impl; `codebase-design`). The Lean-modules lesson: the win is the interface REVEAL, not deep
   encapsulation everywhere (bang's proofs compute against def bodies — an impl-coupled caveat that may or
   may not transfer to bang PROGRAMS, which are less proof-coupled).
4. **The stdlib partition** — which modules (`List`, `Maybe`/`Option`, `Monoid`, `Functor`, `String`,
   `Map`, …), their dependency DAG, what's in the always-open prelude vs an explicit import.
5. **The hashing boundary (build-tool)** — content-address the surface AST? the elaborated core? BOTH at
   different layers (the two-hop analog — a surface hash for the LSP/edit loop, a core hash for the
   compile cache)? Determines cache granularity + what an edit invalidates.
6. **LSP query surface** — hover-type · go-to-def · diagnostics · completion · find-references; all VIEWS
   over the compiler (ADR-0076 #2), so the fork is which queries + the incremental (Salsa-style) engine.

**Recommended**: stdlib-as-extended-prelude first (no module surface needed); build the module system when
it's forced, deciding these then; start carrying source spans in the checker NOW (the one non-deferrable
bit, ADR-0076 #2). Reference lineage in ADR-0076 (git · Unison · Nix · Salsa · Bazel).

**Blocked on**: polymorphism (bites 1-2 → the generic stdlib that forces modules); ADR-0076 #2 (checker
queryability) is the only near-term steer. All post-v1.

**Revisit signal**: the prelude stops scaling / namespacing collides / users write multi-file programs
(build the module system); OR a content-addressed store / incremental compile / IDE integration is taken
up (the tooling — the ADR-0076 generative-constraints payoff). Ties ADR-0076, [[Q32 memoization]],
[[Q33 memory model]], PATH-polymorphism.

## Operator input (2026-07-09): three consumers converge + the reusable-engine framing

With ADR-0093 (modules) Accepted, THREE accepted directions now want the SAME content-addressed
infrastructure: incremental compile (ADR-0076), the Q43 proof cache (#prove results keyed by
elaborated-term hash), and the #60 test cache (law verdicts re-run only when their module's
hash moves). Fork 5's build tool is therefore a SHARED SUBSTRATE, not a speed optimization.

**Operator directive: design it as ONE reusable abstraction, not per-problem reimplementations.**
The generic shape (prior art: "Build Systems à la Carte" — Mokhov/Mitchell/Peyton Jones, build
system = scheduler × rebuilder over a memoized query store; Salsa — already in ADR-0076's
lineage): query = pure function of content-hashed inputs · staleness = hash inequality ·
dependency DAG discovered during execution. Instances become thin: compile, prove, test,
fmt-check — and note the repo's OWN tools/ already hand-rolls ~15 instances of this pattern
(every `gen-*.py --check` fitness leg is a staleness query); the engine would subsume them.

**The self-hosting observation**: the engine's correctness precondition (queries pure in their
hashed inputs) IS bang's language guarantee — so post-modules+IO the engine is a natural BANG
program: the ADR-0076 generative-constraints thesis applied one level up, and the strongest
dogfood available. Sequencing unchanged (build when compile times / Q43 / #60 bite first);
this note pins the SHAPE the eventual unit must take.

## Measurement input (2026-07-18): topology pays, but cannot provide the result-hash firewall

`PATH-queryable-module-graph` exposed the resolver's actual path-free DAG; its successor consumes
that public dump with `tools/module-impact.py`. On the existing six-module Calc project, one
hypothetical equal-weighted change to each module produces **15 dependency-aware module/change pairs
instead of 36 whole-program pairs**. A shared `Ast` change still affects all six modules; each leaf
change affects only that leaf plus `@entry`. JSON's four-node diamond measures 9 instead of 16.

This is structural reachability, not timing or a cache benchmark. It establishes two decisions:

1. **Keep the resolver DAG as the scheduler's coarse invalidation skeleton** — independent leaves
   are observably prunable without any new compiler graph.
2. **Do not mistake topology for staleness.** A comment/format-only edit is structurally upstream of
   every dependent even when its elaborated result is unchanged. Stopping that cascade requires the
   result-hash firewall described in the compiler-as-DBMS survey. This evidence therefore preserves
   the already-recommended **elaborated-core hash** direction and makes a canonical-core fingerprint
   probe the smallest justified successor; it does not yet justify a store, scheduler, persistence
   format, definition granularity, or compile-time claim.

## Fingerprint input (2026-07-18): the core boundary works; the module-result boundary does not exist yet

`PATH-core-fingerprint-probe` followed that successor through the public `bang query dump` route. It
also found that Q43 proof export already owned a hand-rolled `Comp` fold, so the implementation was
centralized as `Bang.CoreFingerprint` rather than duplicated. The tracer establishes:

1. **The elaborated `Comp` is observably canonical for the edits the firewall should ignore.** Through
   the compiled CLI, comment/format-only and local binder alpha-renaming variants return the same
   resolved-program digest, while a semantic `-1` → `-2` edit returns a different digest.
2. **The audit caught a real deterministic collision in the old fold.** It used `Int.toNat` plus one
   sign bit, collapsing every negative magnitude. v2 hashes canonical sign+magnitude spellings and
   also avoids pre-truncating arbitrary `Nat`s to 64 bits; direct falsification poles retain both.
3. **This remains a probe, not a cache key.** The public fact says `cacheKeySafe:false`: 64 bits is not
   collision-resistant, and compiler/kernel versions are not domain-separated. Proof export can use
   it only because its Lean goal is rechecked; an unchecked build cache cannot.
4. **Most importantly, the current result scope is `resolved-program`.** Modules merge at `Surf`, then
   elaborate together to one flat `Comp`. There is no per-module elaborated artifact to hash, so the
   topology DAG plus this whole-program fingerprint cannot yet stop invalidation at each module edge.

**Decision:** fork 5's semantic boundary is now evidence-backed—hash elaborated core, not source text—
but its useful granularity is still open. Before choosing SHA/BLAKE, a store, or a scheduler, identify
the smallest sound module-result/interface boundary that preserves ADR-0093's flat kernel semantics.
Cryptographic hashing is necessary for persistent keys but does not create that missing boundary.

## Interface input (2026-07-18): the public firewall is real; the code artifact is still missing

`PATH-module-interface-boundary-probe` preserved each resolved module's exact public-export provenance
and projected it onto the checked declaration facts already returned by `bang query dump`. The tracer
separates two boundaries that fork 5 previously bundled together:

1. **A useful checked interface firewall exists.** Editing a public value's body or a private helper
   changes the resolved core fingerprint but preserves the module-interface digest. Changing the
   public signature/shape changes the interface. Bodies and private declarations are absent.
2. **That interface is not a separately compiled code artifact.** Top-level values still lower into
   one whole-program lexical chain, and type/trait/effect environments are global. There is no module
   body that can be independently lowered, validated, stored, and linked behind the interface.
3. **Current identities are not independently stable.** User-effect labels are allocated by global
   declaration order. Adding an unrelated earlier effect changes an unchanged dependency's rendered
   capability from `Cap 4` to `Cap 5`, moving its interface digest. The end-to-end suite retains this
   as a falsifier instead of normalizing away the architectural coupling.
4. **The schema prevents premature cache claims.** Each interface names
   `scope=resolved-program-module-interface`, `cacheKeySafe=false`, and
   `separateCompilationReady=false`; invalid typed subjects report `moduleInterfaces:null`.

**Decision:** preserve the checked interface view as the analysis/type-check invalidation boundary,
distinct from the resolved core implementation result. The next justified architecture work is stable
symbolic cross-module type/effect identities, followed by an explicit independently lowerable body and
link/validation contract. Continue to defer a persistent store, scheduler, cryptographic key choice,
and cache-hit path: implementing those now would automate invalidation at a boundary the tracer has
shown to be globally coupled and artifact-incomplete.

## Stable-rendering input (2026-07-18): effect identity stopped leaking into the view, not the core

`PATH-stable-interface-effect-rendering` followed the first retained coupling and found a smaller,
more dangerous presentation bug than runtime allocation itself: checked rendering named `.cap` by its
dense numeral and failed to thread the effect table into rows nested under `.U`. Consequently an
unrelated effect caused false invalidation, while a real nested-row change could be hidden.

The shared decl-aware renderer now reverses checked labels through the elaboration environment,
including capability types, nested thunk rows, and generic folded arguments. Public checked rendering
refuses a label the environment cannot explain, and sorts semantic user-effect names because rows are
sets rather than resolver-ordered lists. CLI fixtures establish that an unrelated earlier effect
preserves the dependency interface, `{Trace}` add/drop moves it, and `LibA.Net`/`LibB.Net` remain distinct
across import-order swaps; a cross-module two-effect row remains stable under the same reversal.

This closes only the **checked presentation identity** leak. Dense runtime labels, global type-hole
numbering, whole-program environments, and the single lexical `Comp` remain. Equivalent import/use
spellings are not yet promised to canonicalize to one module identity. Therefore
`separateCompilationReady=false` remains correct and the next tracer must target a concrete lowered
module-body/link constraint—not a cache, store, scheduler, or cryptographic-key implementation.

## Consumer input (2026-07-18): type/shape fanout is decidable; public-law ownership is not

`PATH-interface-diff-consumer` finally consumes the accumulated facts from the build-tool author's
seat. `tools/interface-diff.py old.json new.json` compares complete projected module exports rather
than trusting the cache-unsafe 64-bit digest, composes the validated reverse closure from
`tools/module-impact.py`, and handles moved, added, removed, and dependency-changed modules. A
three-deep signature edit marks `Lib`, `Mid`, and `@entry`; a body-only edit marks none. Every result
keeps `actualChecksSkipped=false` and `artifactReuseAuthorized=false` because no reusable checked/code
artifact exists.

The strongest falsifier sharpened fork 5. `Lib` owns a public effect law and `Mid` owns its handler.
Changing only the law body preserves `Lib`'s interface because `declShapeJson` includes law names, not
bodies. The dump's global `laws` row does move, but its compatibility tuple has no stable module
relation key. The consumer therefore returns exit 2/`indeterminate` with gap
`module-owned-public-law-contract`; it does not guess from qualified presentation names or claim a
dependent can skip.

**Decision:** the dump is decision-shaped for checked public type/shape plus coarse resolver topology,
but not for complete public semantic contracts. Choose between law identity in exports and stable
module ownership on law facts in a separate additive-schema/systemic-review increment. Do not fold
that field into this consumer tracer. The result narrows—rather than removes—the later body/link/store
work: even a complete interface invalidation answer still would not create an independently validated
artifact. The successor must cover **declared** public laws, not only realized instances: without any
handler, a declaration-law edit is absent even from the global `laws` table. Separately, source-order
permutation of public exports still moves the ordered interface payload; that safe false invalidation
is recorded rather than locally canonicalized away from the producer's digest semantics.

## Declared-law input (2026-07-18): semantic contracts now cross the checked interface boundary

`PATH-module-law-contracts` follows the consumer's demonstrated gap rather than adding another probe.
Every exported trait/effect now carries owner-local declared laws as `{name, params, body}` records;
the body uses the existing canonical `showSurf` path. The interface algorithm is explicitly v2 because
the digest payload changed. The top-level `laws` table keeps its distinct instance/realization meaning.

The prior red journey is now ordinary fanout: editing `Lib.Gate.preserves` moves `Lib` and marks
`Lib`, `Mid`, and `@entry`. The stronger no-handler variant also moves `Lib`, even though both global
instance tables are empty. Private law declarations remain outside `moduleInterfaces`. The pre-scope
kill shot and committed gates show that an unrelated earlier effect and reversed entry import order
around two selected cross-module values preserve the declared law text and digest. A synthetic global
realization-law delta without any public declared-law movement still returns exit 2, so unexplained
evidence is not silently laundered into a complete answer.

Attribution is deliberately per contract rather than per edit cause. If a public law and a new private
realization for that same contract arrive together, the realization row is covered by the moved contract;
the owner and its dependents are already candidates and no work is skipped. A row for any other contract
remains unexplained, as the compound `Lib_Gate`/`Side_Other` falsifier requires.

**Decision:** checked module interfaces cover public types, shapes, and canonical-text law statements.
That is a law-aware invalidation boundary, not law enforcement, semantic equivalence, separate
compilation, or cache authority. Keep `cacheKeySafe=false` and `separateCompilationReady=false`; retain
export-order and global type-hole churn as known false-invalidation sources. Fork 5's next justified
tracer is now the independently lowerable module identity/body/link seam. A store, scheduler,
cryptographic key, or cache-hit path still arrives only after that artifact exists and is validated.

## BANG-consumer input (2026-07-18): the compiler fact graph has its first language-level reader

`PATH-bang-interface-consumer` inserts one dogfood tracer before the independently lowerable artifact
seam. The pre-scope probe passed the transport/performance question—a 6,249-byte live dump crossed
`Console.readLine` intact in about 0.54 seconds—but exposed a real library defect: empty arrays and
objects returned `JNilL` without consuming their closing delimiter. The two symmetric leaf repairs plus
`Parse.parseComplete` now let a freshly generated dump cross the full query → host effect → BANG JSON
path. That is the first actual yield of the “BANG tools consume compiler facts” project, not speculative
parser hardening.

The BANG witness reads two dumps and renders ordered preserved/moved/added/removed interface rows. Its
output is differentially checked against `tools/interface-diff.py` on the same moved, added, and removed
fixtures; malformed JSON, missing/wrong `moduleInterfaces`, invalid rows, and duplicate module identities
produce one `invalid dump` line before any partial result. It deliberately does **not** reproduce the
canonical consumer's topology validation, export/digest consistency check, law attribution, fanout, or
exit-code contract and authorizes no skipped work or artifact reuse.

**Decision:** retain the Python consumer as canonical and the BANG program as a dogfood witness. This
realizes the first half of ADR-0076's toolchain project without pretending a separately validated module
artifact exists. After convergence, return to the independently lowerable identity/body/link seam; a
store, scheduler, cryptographic key, and cache-hit path remain downstream of that artifact.

## Body-identity input (2026-07-18): the cheap projection is refuted; reachable slicing is bounded

The first pre-scope attempt composed the existing `withQueryBody` and `coreFingerprintOf` seams for one
export. That composition is not per-export: `foldLetDecls` still nests every top-level `let`/`let rec`
around the selected trailing body. In a live two-module fixture, changing only unused
`Lib.unrelated : Int = 7` to `8` preserved `Lib`'s checked interface exactly
(`1e689a399109f5aa`) while moving the selected-body proxy
`9ba6727b3122c4ac → 2aef16e70fe42aba`. No `moduleBodies` schema was added on that false boundary.

`PATH-reachable-module-body-slices` narrows the answer to a query projection, not a new lowering mode:
filter unreachable value declarations, keep the non-value elaboration environment whole, preserve source
order, and lower through the unchanged production pipeline. Its pre-scope falsifier found that the
selected export alone is an insufficient closure root: an implicitly selected impl body can reference a
top-level helper even when the export has no syntactic edge to that impl. Retained non-value declarations
therefore root the closure too; this safely over-retains their value dependencies, and any remaining miss
nulls the complete projection rather than emitting partial body facts.

Concrete `let`/`let rec` exports can now be measured. A bounded generic `fn` remains a template whose
standalone body cannot lower without an instantiation, so it receives an explicit unsupported row; every
other export receives an explicit no-body row. Inserting an unrelated earlier effect still moves an
effect-using sliced digest (`27c0555a0c82b9e4 → 1ce72041af068091`) because the environment and dense
runtime labels remain global. That red pole is retained as the next demand signal for label identity.

**Decision:** measure environment-relative reachable body slices with `cacheKeySafe=false` and
`linkReady=false`. Defer environment slicing, type-directed impl reachability, stable label allocation,
generic instantiation identity, import slots, artifact validation, linking, storage, scheduling, and
reuse authorization until this projection's actor journey supplies their concrete demand.

## Canonical body-effect input (2026-07-18): quotient the observation, not runtime allocation

`PATH-canonical-body-effect-identity` follows the published body-slice red pole at its narrowest real
boundary. The kernel `Comp` contains labels only in `Val.vcap` and the four `Handler` constructors;
a Query-local exhaustive traversal can therefore canonicalize the digest input without changing typing,
execution, allocation, or emission. Five exact mapping/collection guards witness every current position,
while identity and permutation-roundtrip guards establish consistent bijection on the traversed fields.

The pre-scope quotient audit caught a critical collapse before it reached schema: if canonical ranks are
assigned only to used effect names, a body using only `A` and an otherwise symmetric body using only `B`
both receive label 4. Body-slice v2 therefore hashes the canonically relabelled `Comp` and then the sorted
canonical-label-to-qualified-effect-name table. An unused earlier effect is absent from that table and no
longer moves the body observation; changing `A` to `B` moves the table hash. A user label that cannot be
reversed through the production elaborator table nulls the complete `moduleBodies` projection.

**Decision:** stable digest-side effect identity is not stable runtime identity. Keep dense production
labels and `linkReady=false`; hand relocation and import-slot validation to the next link-contract tracer
where those representations finally have a consumer. Keep `cacheKeySafe=false`: the composite remains a
versioned 64-bit change detector, not an artifact address or reuse authorization.

## Slice-execution input (2026-07-18): corpus fidelity is positive; initialization refutes generality

`PATH-slice-execution-boundary` executed entry-rooted slices rather than inferring meaning from their
digests. A hidden resolver-aware differential converts the resolved trailing body into a synthetic
declaration, applies the production `reachableValueSliceProg`, lowers both programs, and compares the
kernel oracle plus env engine at identical fuel. All **61/61** current examples agree; the env lane also
matches every committed `expected.txt`. This is useful corpus-relative confidence, not a theorem.

The stop-condition probe found the missing contract. Top-level declarations lower through
`foldLetDecls` as strict lets. If an unreachable top-level initializer calls a divergent function, the
whole program never reaches `main`, while the reachable body slice removes that initializer and returns.
The permanent witness reports whole oracle `outOfFuel` / env `stuck` versus slice `done:1` on both lanes.
Retaining every value declaration would recover that observation only by erasing the body-slice boundary
whose identity was just established.

**Decision:** keep the body schema unchanged and `linkReady=false`; body identity does not imply
standalone executability. A link contract must account for module initialization as well as runtime
effect labels and import slots. Before choosing a mechanism, census real top-level initializer shapes:
if inert descriptions dominate, consider making strict module initialization unrepresentable; if strict
computations are common, specify their order/effects explicitly. The census measures this fork and does
not itself impose a new surface restriction.

## Initializer-census input (2026-07-18): rows are cumulative; syntax bounds the residue

The cheapest proposed census—bucket each value declaration by its existing `DeclFact.row`—failed two
kill shots. `typeStringOfDecl` checks `withQueryBody p name`; `foldLetDecls` therefore leaves the whole
strict declaration chain around every selected result. In a minimized program with manifest values
before and after one divergent initializer, **all five** declaration rows are `{Div}`. The row is a
whole-query-projection effect, not an initializer-local effect, and effect sets cannot be recovered by
subtracting prefix rows. Separately, 273/274 strict initializer occurrences have a row: the runnable
generic `examples/list-basics` binding `length` reports `row:null` / `unbound variable length` because
the bare query projection supplies no specialization call-site.

`PATH-top-level-initializer-census` preserves both falsifiers and answers only what surface syntax can
soundly answer without duplicating elaboration. Across the 61 resolved example journeys, 274 strict
initializer occurrences divide into **233 manifest values**, **24 recursive definitions**, and **17
computation forms**. Forty journeys have no strict initializer, seven contain definition forms only,
and fourteen contain at least one computation form. The first two buckets total **257/274 (94%,
rounded)** under today's non-eager recursive-knot encoding. The residual is an upper bound: named
constructors retain application syntax until elaboration and therefore conservatively land there even
when they become values. Counts are occurrence-weighted—imports recur per
consumer, and the two generated reactive workloads contribute 209 manifest values—so declaration-count
dominance is not a unique-source census or a mandate for an inert-only language rule.

**Decision:** correct `DeclFact.row` documentation now; keep `linkReady=false`; use syntax only as a
one-sided inert-description lower bound. Probe checker-cooperative per-binding rows next, but require
source-safe attribution before any additive fact. Generic bare-projection coverage repair is a separate
defect. No schema/checker behavior, slicer, language rule, initialization order, or linker is changed by
this census.

## RHS-row attribution + residual-audit input (2026-07-18): provenance is a priced door, not a shortcut

`PATH-per-binding-rhs-row-probe` found the desired row at final inference: `synthSC`'s `.lett` arm holds
the binding name and RHS `Row` together, and a capture could be zonked against the run's final
substitution. The missing piece is identity. The checker sees one elaborated `Surf.lett` constructor for
source bindings, recursive knots, prelude/use aliases, monomorphized instances, and ANF temporaries.

Live kill shots reject both cheap mappings. Duplicate top-level `let x` declarations are accepted and
produce two outer `x` bindings; `let rec x` plus `let x` produces `#rec,x,x`; a user may itself bind
`#rec`; bare aliases disappear; and the generic `list-basics` source declaration `length` elaborates
beside `#mono0_Prelude_take`, `#mono0_Prelude_drop`, `#mono0_length`, and `#anf` lets. Neither name nor
outer-spine position identifies a source occurrence. Publishing a row on that basis would be unsound.

**Decision:** do not add an RHS-row schema and do not re-elaborate each RHS. Price explicit
binding-occurrence provenance through elaboration as a checker/elaborator refactor. Its one hard consumer
today is per-binding rows; file-aware diagnostics are a plausible half-consumer, not enough to prebuild
the representation. Reopen when a second concrete consumer arrives or independently justified
elaboration work supplies provenance.

The operator subsequently fixed the architectural boundary in ADR-0117: this result does **not** change
the language or make top-level declarations inert. Strict initializers remain legal and aggregate rows
remain authoritative. What is forbidden is building an attribution-dependent consumer from binder
names, let positions, cumulative-row subtraction, or isolated RHS re-elaboration. Provenance becomes
prerequisite work—not optional polish—when a second concrete consumer appears or when separate
compilation, per-definition capability manifests, initializer optimization, or source-precise effect
diagnostics needs it.

The enumerable fallback closes the immediate decision input without that machinery. Manual inspection
of all 17 computation forms finds 2 pure terminating and 15 effectful/Div-capable initializers. Every one
is entry-owned: 14 are `main` bindings (including `nqueens.main`), while the remaining three are
`nqueens.q4/q5/q6`. No imported library has a computation-form initializer in the resolved corpus. Thus
an inert-library contract has zero current corpus cost; an all-top-level rule would mostly collide with
the chosen `main` entry convention. The remaining fork is now an operator-visible surface decision, not
another measurement or cache implementation.

## Source initialization-order input (2026-07-19): preserve semantics without guessing effects

ADR-0117 leaves strict top-level computation legal, so initialization remains a first-class link input.
`PATH-module-initialization-order` exposes the resolver-owned source portion directly: imported modules
in dependency-first traversal order, entry last, and each module's `let`/`let rec` declarations in full
source-declaration order. `(module, sourceIndex)` distinguishes duplicate names before merge or
elaboration can destroy occurrence identity; ordinary lets are `strict-rhs`, recursive definitions are
`recursive-knot`.

The companion metadata is the limit, not boilerplate: `elaborationProvenance=false`,
`perBindingEffects=false`, and `linkReady=false`. Reversed independent imports reverse their published
initializer blocks, faithfully exposing today's observable order. No row, runtime label, or import slot
is joined to these source occurrences. Runtime relocation and slot validation remain the next artifact
wall, and crossing it must satisfy ADR-0117 rather than infer identity from the flattened let spine.
