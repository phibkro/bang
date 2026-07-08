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
