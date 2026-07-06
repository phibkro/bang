# ADR-0076 · Language tooling by construction: modules elaborate to the flat kernel · the compiler is a queryable content-addressed service · incremental compilation falls out of immutability + purity (the constraints are generative)

<!-- adr-frontmatter -->

- **Status**: Accepted (the architecture; the module-system / build-tool / LSP BUILDS are sequenced behind the stdlib — this pins the decisions that must steer the checker's evolution NOW)
- **Summary**: The stdlib forces namespacing → a MODULE SYSTEM → multi-module BUILD TOOLS + an LSP. Three decisions, pinned early because retrofitting is expensive: (1) modules are a FRONTEND feature that ELABORATES to the flat kernel (invariant #5, same elaborate-away move as polymorphism/ADR-0075 and the injected prelude — the kernel stays flat, 5-primitive, untouched); (2) the compiler is a QUERYABLE SERVICE — the LSP + build tool are VIEWS over its analyses, NOT parallel type-checkers (a second checker is a single-source-of-truth violation that can DISAGREE with the compiler); (3) the module dependency graph is an ACYCLIC, GENERATED DAG (bang dogfoods its own `arch-check` V-structure + generated import-graph discipline). LOAD-BEARING RATIONALE — the operator's thesis: **bang's core constraints (immutability · purity · ADTs · laws) ARE exactly the invariants that content-addressed incremental tooling REQUIRES, so the tooling falls out BY CONSTRUCTION.** Immutability ⟹ stable content hashes ⟹ Merkle-DAG staleness ⟹ incremental compilation that is CORRECT BY CONSTRUCTION (a silently-stale cache is UNREPRESENTABLE — the hash IS the dependency check). Purity ⟹ memoized queries (Salsa-style). The constraints are generative.
- **Depends-on**: 0026 (stratification), 0075 (elaborate-to-mono — same move), 0001 (rows are sets)
- **Relates-to**: Q32 (memoization — the compiler's memoized queries), Q33 (immutability/content-addressing), Q30 (FBIP), #50/PATH-polymorphism (the stdlib that forces this)

- **Status:** Accepted (operator-approved 2026-07-06) — decisions pinned; the module-system / build-tool / LSP BUILDS come after the stdlib (which needs polymorphism, in flight)
- **Date:** 2026-07-06
- **Layer:** C + frontend + tooling (all elaborate-away / derive-from-compiler; the verified kernel is UNTOUCHED)
- **Builds on:** ADR-0075 (polymorphism elaborates to mono — modules elaborate to flat, same seam), ADR-0026
  (verified-core/tested-superset), the repo's own `arch-check` + generated import-graph (bang's self-hosted
  module discipline). Lineage: git (content-addressed immutable objects) · Unison (content-addressed code) ·
  Nix (hash-the-inputs reproducible builds) · Salsa/rust-analyzer (incremental memoized queries) · Bazel
  (content-addressed action-cache DAG).

## Context

A generic stdlib (PATH-polymorphism bites 1-2) needs organizing + NAMESPACING (`List.map` vs `Str.map`
can't both be `map`), which forces a MODULE SYSTEM, which forces multi-module BUILD TOOLS + an LSP (IDE
type hints, go-to-def, diagnostics). Most of that is sequenced LATER (behind the stdlib), but three
architectural decisions shape how the CHECKER + stdlib evolve TODAY — deciding them now avoids a costly
reversal (retrofitting a batch compiler into a queryable service is expensive).

## Decision

1. **Modules are a FRONTEND feature — they ELABORATE to the flat kernel.** A module system is
   name-resolution + linking in the frontend producing ONE flat program, erasing to the monomorphic
   5-primitive kernel (invariant #5). Namespacing, visibility, the DAG all live in the elaborator — the
   kernel/`Source.eval`/soundness stay flat + untouched. Same elaborate-away move as polymorphism
   (ADR-0075) and the injected Char/Str prelude.
2. **The compiler is a QUERYABLE SERVICE; the LSP + build tool are VIEWS, not reimplementations.** The
   compiler is a library answering queries — "type at this position," "definition of this name,"
   "dependency graph." The LSP's hover-type and the compiler's check are THE SAME HM inference (f063c78) —
   a second type-checker in the LSP is a single-source-of-truth violation that can DISAGREE with the
   compiler (the SSoT invariant forbids it by construction). NEAR-TERM consequence: the checker evolves
   toward queryability (carry source SPANS, expose a type-at-position query) — cheap to keep if decided
   now, expensive to retrofit. This is the decision that CANNOT WAIT even though the LSP itself is later.
3. **The module dependency graph is an ACYCLIC, GENERATED DAG.** Bang-the-project already solved this for
   ITSELF — `arch-check` (the V-structure, no import cycles) + a generated import-graph + narrow module
   interfaces (the Lean-modules lesson: the win is the interface REVEAL, not deep encapsulation
   everywhere; Ousterhout deep modules, the `codebase-design` vocabulary). The bang LANGUAGE's module
   system reuses those principles for bang PROGRAMS — nothing new to invent.

## The load-bearing rationale — the constraints are generative (the operator's thesis)

WHY these decisions are right, and why bang can have this tooling cleanly where Rust/Haskell bolt it on:
**bang's core constraints ARE the invariants content-addressed incremental tooling requires.**
```
IMMUTABILITY  ⟹  content hash is canonical + stable  ⟹  content-addressing (Merkle-DAG over modules)
              ⟹  staleness = hash inequality  ⟹  recompile a node iff its content or a dep hash changed
              ⟹  incremental compilation, CORRECT BY CONSTRUCTION: the artifact is a PURE fn of
                  (source, deps) ⟹ the hash fully determines it ⟹ a cache HIT is provably right; a
                  silently-STALE cache is UNREPRESENTABLE (the hash IS the dependency check — "make
                  illegal states unrepresentable" applied to the build cache).
PURITY        ⟹  every compiler analysis is a pure fn of its inputs ⟹ memoized, content-keyed (Q32)
              ⟹  the compiler is a graph of memoized queries; change one input → only the transitively
                  dependent queries re-run (Salsa/Adapton — "compiler-as-a-service" done right).
ADTs          ⟹  the compiler's OWN data (AST/types/module-DAG) is precise, pattern-matchable, structurally
                  hashable; illegal states unrepresentable IN THE COMPILER.
LAWS/relations⟹  reason about + rewrite-optimize by the laws; the laws ARE the differential-test spec.
```
The killer property is CORRECTNESS: incremental compilation is where build tools have their subtlest bugs
(stale caches, missed invalidations) — all from mutable dependency tracking that DRIFTS. Immutability makes
the drift unrepresentable. The constraint bang pays for in the LANGUAGE is the exact mechanism the TOOLING
needs. **The fixpoint:** bang's constraints make it the ideal language to WRITE the tools in AND make the
tools it NEEDS fall out by construction — language + toolchain co-designed around one generative constraint.

## Rejected / not-now

- **A separate type-checker in the LSP** — SSoT violation (two checkers can disagree — the hover says one
  type, the compiler errors with another). The LSP is a VIEW over the one compiler.
- **Modules in the kernel** — violates invariant #5; modules elaborate away like everything else.
- **Mutable dependency tracking for incremental builds** — the fragile, stale-cache-prone approach the
  content-addressed model exists to avoid.
- **Building the module system / build tool / LSP NOW** — sequenced behind the stdlib (which needs
  polymorphism, in flight). This ADR pins the DECISIONS, not the builds.

## Consequences

- The checker should start carrying source SPANS + move toward a query interface (decision 2) — the one
  thing to begin NOW; everything else waits for the stdlib.
- When built, the build tool is a git-object-model / Nix-style content-addressed Merkle-DAG; incremental
  compilation is correct by construction. The LSP is a Salsa-style memoized-query view.
- "Bang writes its own tools" sharpens to "bang writes its own CORRECT INCREMENTAL tools" — because its
  values hash.

## Revisit if

- The module-system surface is built → decide the forks (see the OPEN_QUESTION): file-vs-`module`-block,
  qualified-vs-open imports, visibility/export rules, the stdlib's module partition.
- A content-addressed store is built → decide the hashing boundary (hash the surface AST? the elaborated
  core? both, at different layers — the two-hop analog).
