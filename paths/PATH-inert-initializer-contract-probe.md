# PATH-inert-initializer-contract-probe — price the description-only top-level fork

> Dry-run an enforcement-grade inert-initializer rule after authoritative resolution and elaboration,
> close constructor-shaped false positives, and leave the surface decision to an explicit ADR.

## Seam

- **From checkpoint**: the syntax census and ADR-0117 preserved strict initialization because neither
  cumulative checker rows nor elaborated let positions identify source initializers soundly.
- **To checkpoint**: the language designer has exact corpus migration cost and a demonstrated checker
  seam for choosing description-only top levels versus retaining ordered entry initialization.
- **Contract preserved**: this is a hidden lifecycle probe. The checker, query schema, lowering,
  evaluator, module resolver, runtime, and accepted source language remain unchanged.

## Layer

- [ ] Kernel  [x] Compiler leaf  [ ] Surface language  [x] Meta (tests/docs)

## Actor journey / observable outcome

- **Actor / need**: a language and linker designer needs to know whether making top-level declarations
  inert is enforceable and what existing programs it would actually displace.
- **Public starting point**: all 61 `examples/*/main.bang` actor journeys, resolved by the production
  module resolver and elaborated by the production frontend.
- **Terminal observation**: the proposed all-top-level contract would refuse exactly three bindings:
  `examples/nqueens/main.bang`'s entry-owned `q4`, `q5`, and `q6`. Every `main` remains the proposed
  distinguished executable binding; no imported-library binding is refused.
- **Adverse / recovery route**: a constructor application whose payload computes is refused, while
  `Some(3)`, annotated `None`, nested computations behind `{…}`, and a same-named inert `Some` binding
  stay aligned with the elaborator's real constructor-precedence rule.
- **Downstream journey released**: an explicit Option A/Option B language-contract ADR; no provenance,
  linker, memoization handler, or ordering machinery must be pre-built to make that choice.

## Feeds the constraint

- **Binding constraint now**: strict initialization is observable and remains a required link input
  (`PATH-slice-execution-boundary`, ADR-0117), while body artifacts still publish `linkReady=false`.
- **How this path feeds it**: reuse resolver ownership and the elaborator's authoritative constructor
  environment to prove that the proposed refusal can live post-resolution and pre-lowering, where
  checker diagnostics already live.

## Prospective systemic review

| concern | horizon + evidence | likelihood / impact / late cost | disposition now | reopen trigger |
|---|---|---|---|---|
| global constructor lookup misclassifies an actually shadowed function call | adversarial same-named `Some` binding passes full elaboration only because constructor resolution deliberately precedes ordinary lookup | low / critical / low | **pin the semantic pole in the focused battery** | constructor/name-resolution precedence changes |
| a constructor hides eager work in its payload | `Some(1 + 2)` is an application whose elaboration A-normalizes the payload | high / high / low | **recurse through payloads and refuse this fixture** | initializer classification changes |
| a future surface value form is silently accepted without review | classifier is an enumerated conservative whitelist; unknown forms return false | medium / medium / low | **fail closed and require an explicit classifier edit** | `Surf` gains a value-shaped constructor |
| Option A removes compute-once library constants | the corpus has none, but a real package can eventually pull the pattern | medium / medium / medium | **preserve the door for an explicit init form or memoizing handler; do not pre-build either** | a program needs shared eager initialization |
| Option B turns entry ordering into durable linker debt | current resolver order is already observable and published by the initialization-order tracer | high at separate linking / high / high | **price it in the ADR, not in this probe** | operator chooses B or a linker consumes initializer slots |
| `main` becomes the first distinguished source name | Option A's only executable binding needs a stable spelling and diagnostic contract | realized if A / high / medium | **require an explicit ADR against ADR-0093 D5** | operator chooses A |

## Baseline, falsifier, and evidence

- **Baseline / red observation**: the one-sided syntax census conservatively treated named constructor
  applications as computation forms, so it could estimate neither an enforcement seam nor exact cost.
- **Smallest tracer bullet**: expose the existing constructor resolver over `elabProg`'s authoritative
  constructor table, recursively classify inert RHS syntax, and report exact `(subject,module,name)`
  refusals after full resolver and elaborator validation.
- **Positive evidence**: all 61 subjects resolve; exact output contains only `nqueens`'s `q4/q5/q6` and
  totals `requested-subjects=61 resolved-subjects=61 would-refuse=3`.
- **Negative or recovery evidence**: the multifile pole keeps library `Some(3)`, annotated `None`, entry
  `Some(4)`, and a same-named inert `Some` binding legal; it refuses library arithmetic, a constructor
  with a computing payload, and entry-local non-`main` arithmetic. A computed `main` stays legal.
- **Broader convergence gate**: `tools/test-initializer-census.sh` owns exact rows and accounting;
  `lake build bang`, the example journeys, batteries, audit, fitness, and full verify remain required.
- **Assumptions / exclusions**: this is not a language decision, contextual-equivalence proof, source
  provenance mechanism, initializer-local effect fact, DCE/reordering rule, linker, cache authority,
  explicit-init syntax, or memoization implementation.

## Plan

1. [x] Build the constructor-aware classifier at the checker/elaborator seam without calling it.
2. [x] Dry-run all 61 resolved example journeys and pin exact refusal identities.
3. [x] Close constructor payload, zero-arity, annotation, thunk, ordinary-call, and name-shadow poles.
4. [x] Obtain skeptical phase-placement review and persist the priced A/B fork.
5. [x] Run convergence and publish the decision input without changing language semantics.

## Status

- [x] Started 2026-07-19
- [ ] In flight: none; successor is the Option A/Option B operator decision and ADR
- [ ] Blockers: none in the probe; the successor intentionally requires operator guidance
- [x] Completed 2026-07-19
- Focused evidence: `tools/test-initializer-census.sh` passes **12/12**; compiled build passes **1456
  jobs**.
- Convergence evidence: the tracked product tree passes the full pre-commit `fitness` and `verify`
  compositions; focused evidence remains **12/12**, the compiled build remains **1456 jobs**, and no
  checker, query, lowering, runtime, or proof contract changed.
- Published product commit: `d170f007` on `codex/inert-initializer-contract-probe`.
- Retained failed gates / successors: cumulative-row attribution remains rejected by ADR-0117;
  compute-once constants retain an explicit-init/memoizing-handler door only if a program pulls it.
- Reopen / observe: rerun exact corpus rows when initializer syntax, constructor resolution, the example
  corpus, or entry-point semantics changes.

## Owner

- Agent / human: Codex, with persistent Fable 5 advisor in Herdr `lang-bang`
