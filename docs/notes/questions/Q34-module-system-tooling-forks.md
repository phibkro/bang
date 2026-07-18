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
