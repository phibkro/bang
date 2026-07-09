# ADR-0093 · Module system v1: file-modules, qualified-by-default imports, elaborate-to-flat

<!-- adr-frontmatter -->

- **Status**: Proposed
- **Summary**: Q34's revisit signal has fired — the dogfood arc reached multi-file need (a JSON parser wanting the tokenizer's machinery; the operator names modules as the pending blocker for real projects). The ARCHITECTURE is already pinned (ADR-0076, Accepted: modules elaborate to the FLAT kernel · the compiler is a queryable service · the module DAG is acyclic + generated); this ADR decides Q34's v1 SURFACE forks inside those pins. **Decision: (D1) one module = one FILE — `import tokenizer` resolves `tokenizer.bang` relative to the importing file (then a project root); the module's name IS its filename, no module header, no blocks; (D2) qualified access by default (`tokenizer.lex input`) + EXPLICIT selective `use tokenizer (lex, Token)` — no glob/open-all import exists (implicit namespace pollution is the anti-agent-first move; a `use` collision is a LOUD error, ADR-0046); (D3, operator-amended 2026-07-09) declarations are PRIVATE by default; `pub` marks a declaration exported (riding the Rust convention — the dominant pattern-match for exactly this semantics). Private-by-default is the consistent agent-first choice: the module's interface is DECLARED at the definition site, nothing exports by accident, and `use`/qualified access can only name what the author deliberately revealed (the Q34 interface-reveal lesson, made structural); (D4) semantics = whole-program elaboration: imports parse + merge with name-qualification at the Surf level, THEN the existing single-program pipeline runs unchanged — the kernel never learns modules exist (the ADR-0075/0088/0091 elaborate-away move, fourth application); import cycles are a loud error (the 0076 DAG pin); the prelude stays the one always-open implicit module.** **Q38 posture (deliberate): v1 mints NO new interface construct** — a module is a file, not a signature; the module≟trait≟effect unification stress-test stays fully open for Stage 7, when the `effect` declaration surface (ADR-0092/0085-D4) either converges with `trait` syntax or diverges-documented. **Deferred per Q34's own sequencing**: the stdlib partition (prelude scales for now), the hashing boundary + incremental build, the LSP query surface (its non-deferrable prerequisite — spans in the checker — already landed via #52/#59). **Rejected**: module blocks (Lean-style `module { }` — nesting no v1 program needs; not foreclosed, a file is trivially one block); glob imports (`use tokenizer *` — resolution becomes context-dependent, breaking both ADR-0046 determinism and agent pattern-matching); an `export (…)` LIST as the visibility mechanism (a second place to look — the def site should carry its own visibility; kept conceivable as future sugar over `pub`); default-PUBLIC (the draft's original D3, operator-rejected — exports-by-accident and an undeclared interface).
- **Depends-on**: 0076 (the pinned architecture), 0075 (elaborate-to-mono precedent), 0046 (deterministic-or-loud resolution)
- **Relates-to**: Q34 (this decides its forks 1–3; 4–6 stay deferred), Q38 (posture: keep the unification testable, decide nothing), #33 (dogfood), ADR-0092/Stage-7 (the effect-decl surface that will test Q38), the dogfood lane's in-flight friction findings note (path linked here at acceptance, once it lands)

## Status

Proposed (2026-07-09, drafted while the dogfood lane runs — its module-shaped friction findings
feed this ADR's final form before implementation). Awaiting operator ruling. Implementation is
elaborator + CLI work (`Surface.lean` import parsing · `TypeCheck.lean` decl-merge — queue
behind current TypeCheck ownership; `Main.lean` file resolution), zero kernel surface.

- **Layer:** F (frontend) + CLI. Census untouchable by construction — the merged program
  elaborates through the SAME checkAndLower; a multi-file program and its hand-concatenated
  single-file equivalent produce identical kernel terms (that equivalence is the v1 oracle:
  a differential #guard).

## Context

Today a bang program is ONE file + the injected prelude. The tokenizer (ce6d738) fits; a JSON
parser wanting to REUSE the tokenizer does not — it must copy code, which is the update-anomaly
smell the whole project exists to kill. ADR-0076 pinned how modules must relate to the kernel
(elaborate to flat, invariant #5 untouched) and to tooling (queryable compiler, acyclic
generated DAG, content-addressing later); what remained were Q34's surface forks.

## Decision detail

- **D1 — file = module.** `import tokenizer` in `json.bang` loads `tokenizer.bang` (same
  directory, then the project root — the resolution order is fixed and documented; a miss is a
  loud error naming both probed paths). The module name is the filename stem; no header
  ceremony. Content-addressing (deferred) hashes the file — D1 is what makes that trivial.
- **D2 — qualified + explicit `use`.** `tokenizer.lex` works immediately after `import`;
  `use tokenizer (lex, Token)` brings exactly the named decls into scope. Re-declaring an
  imported name locally, or two `use`s colliding = loud error with both origins named
  (agent-first: the error TEACHES the fix). `data` constructors travel with their type
  (`use tokenizer (Token)` brings Token's ctors — match arms need them).
- **D3 — private by default, `pub` opts in (operator ruling 2026-07-09).** A bare decl is
  module-local; `pub let` / `pub data` / `pub effect` export it. Qualified access and `use` can
  only name `pub` decls; naming a private one is a loud error that SAYS it exists but is
  private (agent-first: the error teaches the fix, not just "unknown name"). `data` visibility
  is all-or-nothing in v1 (a `pub data` exports its ctors — the abstract-type refinement, ctors
  hidden while the type is public, is deferred until a consumer needs it). The main/entry file's
  decls need no `pub` (nothing imports it). Cost accepted: one keyword per shared decl — the
  interface-reveal is exactly the documentation an agent reading the module wants anyway.
- **D4 — whole-program elaboration.** Import resolution produces a topologically-ordered decl
  list (cycle = error), name-qualified at Surf level (`tokenizer.lex` becomes an ordinary
  qualified identifier the elaborator resolves — the same mangling move `data` ctor tags
  already use), then ONE elaboration pass exactly as today. Incremental/per-module compilation
  is the ADR-0076 payoff LATER (content-addressed, falls out of immutability); v1 recompiles
  the world, which at dogfood scale costs nothing (invariant #7).

- **D5 — entrypoint (operator fork, ruled 2026-07-09): `main` is a magic NAME, not a keyword.**
  A decl named `main` marks the file runnable (riding the C/Go/Rust convention — a keyword would
  be novel syntax for non-novel semantics, against the lens). The trailing-expression form STAYS
  as script mode (the REPL/eval/one-liner path and today's whole corpus); `main`-decl present →
  program mode; BOTH present → loud error (ADR-0046, no silent precedence); neither → a pure
  library file. `main` needs no `pub` (the runtime, not an importer, invokes it). **The pinned
  payoff — main's row is the program's capability MANIFEST**: `bang run` is the use site where
  the runtime installs handlers for exactly `main`'s declared row, so "runtime is a handler
  installed at the use site" (the kernel thesis) becomes the CLI's actual contract. Today that
  row can only be `⊥`/`{Div}`; when Stage 7 + ADR-0084 land IO, a row the runtime can't provide
  is a LOUD TYPE ERROR at the boundary — the program's powers become a checked fact of its
  signature. (This D pins the direction; the manifest-checking mechanics land with ADR-0084.)

## The v1 oracle

`elaborate(import-merged files) ≡ elaborate(hand-concatenated-and-qualified single file)` —
a differential #guard per corpus case, plus `check-examples` gains its first multi-file
example project. Same stratification as everything else: the tested superset rides an oracle.

## Revisit if

- The prelude stops scaling or the stdlib partition arrives → decide Q34 fork 4 (which modules,
  what stays always-open) as its own ADR.
- Stage 7 lands the `effect` declaration surface → run the Q38 stress-test THEN (module-as-file
  deliberately left no construct to collide with it).
- A consumer needs abstract types (public type, private ctors) → the `pub data` refinement, own slice.
- Multi-file compile times bite → the ADR-0076 content-addressed incremental build (Q34 fork 5).

## Evidence

ADR-0076 (the pinned architecture + generative-constraints rationale), Q34 (the fork list +
"revisit signal: users write multi-file programs" — fired 2026-07-09), Q38 (the
keep-it-testable directive), ADR-0075/0088/0091 (three prior elaborate-away wins), the
dogfood lane's in-flight findings note (concrete multi-file friction shapes; linked at acceptance).
