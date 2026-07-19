# 0118 — top-level declarations are inert except entry `main`

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: Ordinary top-level `let` declarations are semantic descriptions: their RHS must be an
  inert value. The one exception is the bare `main` declaration in an entry program, whose RHS may
  compute. Top-level `let rec` remains a suspended definition; a trailing entry body remains the
  program body and does not become a declaration. Enforcement uses the elaborator's authoritative
  constructor environment and reports stable diagnostic B019.
- **Depends-on**: [0007](0007-explicit-force-and-fixed-precedence.md) (description/force boundary),
  [0093](0093-module-system-v1-file-modules-elaborate-flat.md) (file modules and optional `main`),
  [0117](0117-per-binding-effect-facts-require-source-provenance.md) (no guessed initializer rows)
- **Date**: 2026-07-19
- **Deciders**: operator + Codex, after the 61-journey enforcement probe and Fable 5 review
- **Ties**: `paths/PATH-inert-initializer-contract-probe.md`,
  `paths/PATH-top-level-initializer-census.md`,
  `docs/notes/questions/Q34-module-system-tooling-forks.md`

## Context

The body-artifact arc reached the link boundary with strict initialization still observable. The
existing language allowed any top-level `let` RHS to compute, so a linker could not treat modules as
descriptions: it had to retain source initializer order even for unreachable declarations. ADR-0117
correctly rejected deriving a language restriction from unsound per-binding row attribution, but a
later independent probe supplied the missing product evidence.

The constructor-aware dry run resolves and elaborates all 61 example journeys through the production
frontend. An inert rule with one executable `main` would reject exactly three bindings:
`examples/nqueens/main.bang`'s `q4`, `q5`, and `q6`. No imported library currently relies on an eager
initializer. The classifier is feasible at the normal frontend seam: after module qualification and
constructor-environment construction, before declaration folding, lowering, or kernel entry.

## Decision

1. **Ordinary top-level `let` RHSs must be inert values.** Literals, variables, unit, thunks, sums,
   folds, pairs, annotations, quantity-use wrappers, zero-arity constructors, and named constructor
   applications with recursively inert payloads are accepted. Unknown or computation-shaped syntax
   fails closed.
2. **The entry program's bare `main` is the only computed declaration.** It may contain arbitrary
   well-typed computation. Module qualification makes a library's `main` become `Lib_main`, so it is
   not the distinguished binding. A source still in library context (`isLibrary=true`) receives no
   `main` exception; selecting a standalone file that contains `main` through a file-oriented
   `run`/`check`/query/rewrite-validation route flips it to program mode first. Stdin has no file
   entry role and stays a library context. Identification relies on these existing role/resolver
   facts, not suffix matching.
3. **`main` remains optional.** A program may still use its ordinary trailing body; that body is not a
   declaration and is therefore outside the initializer rule. This refines ADR-0093 D5 rather than
   replacing the expression-oriented entry surface.
4. **Top-level `let rec` remains legal.** Its tuple-of-thunks knot constructs a suspended definition;
   the recursive body does not execute during initialization.
5. **Enforcement is an elaboration well-formedness check.** It runs after the authoritative constructor
   table exists and before `foldLetDecls`. Consequently `run`, `check`, queries, emitters, and the raw
   `--no-typecheck` path agree: the escape skips type checking, not source-language well-formedness.
6. **Constructor resolution mirrors the language, including precedence.** `elabS` resolves a
   constructor application before ordinary-variable lookup. The initializer classifier uses the same
   qualified/bare ambiguity rule, so a same-named value binding cannot spoof `Some(3)` into an ordinary
   call. Constructor payload computations such as `Some(1 + 2)` remain eager and are refused.
7. **Diagnostic B019 owns the refusal.** It names the declaration and teaches both repairs: suspend the
   work in `{…}`, or move entry computation under `main`.
8. **One unspellable lifecycle binding is exempt.** The slice-fidelity harness relocates a trailing body
   into the reserved `$<bang-internal-slice-entry>$` declaration so the production slicer can select it.
   Source cannot spell that identifier; its collision check remains. The exemption is named beside the
   language rule and exists only to preserve the measurement apparatus.

## Consequences

- The strict-initializer divergence class becomes unrepresentable for valid programs. Module libraries
  are descriptions; entry computation has one declaration boundary.
- `nqueens.q4/q5/q6` move into `main`; both reference and compiled journeys must still return `21004`.
- `main` becomes BANG's first semantically distinguished user-spellable name. This is an intentional
  surface cost, not an implementation convention.
- Implicit compute-once constants are no longer expressible as library declarations. A library author
  can store an already-inert value or a thunk. If shared eager computation becomes a real need, prefer
  an explicit initialization construct or an ordinary memoizing handler; neither requires a kernel
  primitive, and neither is built speculatively here.
- Pure terminating syntax such as `base + 1` or `Some(1 + 2)` is conservatively refused outside `main`.
  Relaxing that one-sided rule would need an authoritative totality/effect fact tied to the source
  occurrence. If dogfooding makes this papercut concrete, it becomes the second consumer that reopens
  ADR-0117's provenance door.
- `linkReady` remains false. This closes the initialization-divergence leg only; independent body type
  validation, complete import slots, and an actual linker remain separate work. A body slice is not
  thereby standalone.

## Rejected alternatives

- **Require only libraries to be inert and retain ordered entry initializers.** This costs zero current
  migrations but makes entry ordering a permanent linker contract. The three-binding migration is
  cheaper and better matches BANG's descriptions-until-forced thesis.
- **Allow any pure or empty-row initializer.** The current checker has no source-safe per-binding row;
  names, let positions, cumulative rows, and isolated RHS re-elaboration were all refuted by ADR-0117.
- **Make `main` mandatory and remove trailing bodies.** This adds a surface migration unrelated to the
  initializer hazard; expression-first programs remain useful and unambiguous.
- **Add eager initialization or memoization now.** No current corpus or user journey requires it.
- **Treat `--no-typecheck` as a bypass.** That would make accepted source-language structure depend on
  a runtime flag and let query/emit routes disagree about whether the subject is a valid BANG program.

## Confirmation

- `tools/test-initializer-census.sh` pins legal constructor/thunk/trailing-body poles, library and entry
  B019 refusals, the strict-initializer refusal, and the migrated 61-subject census.
- `tools/test-explain.sh` requires B019 to reach both structured and human diagnostic surfaces.
- The normal example, engine-differential, WasmGC, slice-fidelity, query, generated-reference, fitness,
  and full verification gates remain authoritative.

## Relationship to earlier decisions

This ADR amends ADR-0117's temporary “keep the current language contract” outcome because a later
link-seam consumer and exact migration probe supplied the independent justification that decision
required. ADR-0117's provenance and no-guessed-attribution rules remain in force. It also refines
ADR-0093 D5: `main` is still optional, but is now semantically distinguished among top-level
declarations rather than merely selected by the CLI convention.
