# PATH-top-level-initializer-census — measure initializer shapes without misreading rows

> Census the strict declaration chain with a sound one-sided syntax classifier, retain the two
> falsifiers that block cumulative-row reuse, refute unsound checker attribution, and manually close
> the bounded computation-form residue.

## Seam

- **From checkpoint**: `PATH-slice-execution-boundary` proved that pruning an unreachable strict
  divergent initializer changes whole-program execution and made initialization a link-contract input.
- **To checkpoint**: every strict initializer occurrence in the 61-example resolved corpus is
  classified as manifest value, recursive definition, or conservative computation form; published
  `DeclFact.row` semantics are corrected before a consumer can mistake chain effects for RHS effects.
- **Contract preserved**: no query schema, checker behavior, slicer, language rule, linker, or runtime
  changes. The new command is hidden lifecycle instrumentation owned by its battery.

## Layer

- [ ] Kernel  [x] Compiler leaf  [ ] Surface language  [x] Meta (tests/docs)

## Actor journey / observable outcome

- **Actor / need**: a module-system designer needs evidence about whether real top-level initializers
  are mostly inert descriptions before choosing an initialization contract.
- **Starting point**: all 61 `examples/*/main.bang` files are resolved through the production module
  resolver, then the exact `letD`/`letRecD` chain consumed by `foldLetDecls` is inspected.
- **Terminal observation**: 274 occurrence-weighted strict initializers classify as **233 manifest
  values**, **24 recursive definitions**, and **17 computation forms**. Of 61 actor journeys, 40 have
  no strict initializer, 7 have definition forms only, and 14 contain at least one computation form.
- **Adverse / recovery route**: the public row shortcut is rejected twice: one divergent sibling
  makes `before`, `loop`, `divergent`, `after`, and `main` all report `{Div}`, while the runnable
  generic `list-basics.length` reports `row:null` / `unbound variable length`. Both are permanent gates.
- **Downstream journey released**: the automated RHS-row route was attribution-refuted; a bounded manual
  audit now classifies all 17 computation-form occurrences and releases the initialization-contract
  operator decision without building provenance machinery for one consumer.

## Feeds the constraint

- **Binding constraint now**: `DeclFact.row` comes from `typeStringOfDecl (withQueryBody p name)`, so
  every strict initializer still wraps the selected result. Rows are effect sets and cannot be
  prefix-subtracted into local effects; a separate apparatus would duplicate elaboration.
- **How this path feeds it**: correct the fact semantics, publish a syntax-only lower bound on inert
  descriptions, and turn the unresolved computation residue into a precise demand on the checker.

## Prospective systemic review

| concern | horizon + evidence | likelihood / impact / late cost | disposition now | reopen trigger |
|---|---|---|---|---|
| a chain row is consumed as a declaration-local row | five-declaration taint fixture | realized / critical / high | **correct docs and retain executable red pole** | row producer changes |
| generic specialization leaves a value fact uncovered | `list-basics` runs at 302 but `length` query fails | realized / high / medium | **pin the gap; separate repair increment** | bare generic projection is repaired |
| syntax unknown is overclaimed as effectful | `base + 1` is computation-form but pure | high / high / low | **call it conservative unknown, never effect evidence** | explicit binding provenance exists |
| named constructor syntax inflates the unknown residue | `Some(3)` parses as application before elaboration | high / medium / low | **treat 17 computation forms as an upper bound** | census moves post-elaboration |
| recursive definition bodies are mistaken for executed initialization | `letRecD` builds a knot; body runs only when forced | medium / high / medium | **keep a separate recursive-definition bucket** | recursion lowering changes |
| occurrence counts masquerade as unique definitions | imports repeat per consuming subject | high / medium / high | **say journey-weighted; claim no source inventory** | stable source identities exist |
| generated workloads dominate the manifest-value count | two reactive examples contribute 209 manifest occurrences | realized / medium / low | **also report subject buckets and raw residue** | corpus composition changes |
| hidden measurement becomes public CLI | resolver lives in `Main.lean` | medium / medium / high | **keep under `bang internal`; battery owns text** | a third consumer needs extraction |

## Baseline, falsifiers, and evidence

- **Baseline**: the predecessor named an initializer census but had only one semantic counterexample,
  not a corpus map.
- **First kill shot — coverage**: public dump rows exist for 273/274 strict initializer occurrences.
  The missing row is `examples/list-basics`'s generic `letRec length`; the program runs to `302`, but
  the bare query projection loses the specialization call-site and reports `unbound variable length`.
- **Second kill shot — meaning**: in `before=1; loop; divergent=loop 0; after=2; main=after`, every
  `DeclFact.row` is `{Div}`. The field is chain-cumulative and cannot drive an initializer-local census.
- **Smallest honest tracer bullet**: use surface form only. `letD` RHSs accepted by the current
  manifest-value subset are inert-description candidates; `letRecD` stays a separate definition
  bucket under today's tuple-of-thunks μ-knot encoding; every other `letD` is computation-form/unknown.
  New surface constructors default unknown. Named constructors are intentionally under-approximated:
  their surface application spelling remains unknown even when elaboration would reveal a value.
- **Measured result**: 233/274 manifest values, 24/274 recursive definitions, 17/274 computation
  forms. Thus 257/274 (**94%**, rounded) are already definition forms under a conservative syntactic
  test, while the 17/274 residual is an upper bound on genuinely effectful initialization. This is an
  occurrence-weighted resolved-journey census: imported declarations recur, and
  the two generated reactive workloads alone contribute 209 manifest-value occurrences. At subject
  level, 14/21 journeys with any strict initializers contain a computation form, so declaration-count
  dominance is not enough to impose an inert-only language rule.
- **Evidence owner**: `tools/test-initializer-census.sh` pins the 61-subject census, exact aggregate,
  strict witness classification, cumulative-row taint, runnable/null generic pole, and 273/274 coverage.
- **Assumptions / exclusions**: syntax classification is a one-sided measurement, not contextual
  equivalence or proof of safe pruning at an exact fuel boundary. No unique-definition census,
  initializer-local effect row, schema field, termination refinement, DCE rule, language restriction,
  initialization order, artifact, cache authority, import slot, runtime relocation, or linker is claimed.

## Manual residual audit

`PATH-per-binding-rhs-row-probe` found the authoritative final row but refuted source attribution, so the
bounded residue was read directly. “Effectful/Div-capable” includes a handled operation (the outer row may
be empty after discharge) or a call whose declared row contains `Div`; it is a behavior classification,
not a claim about the cumulative `DeclFact.row`.

| entry subject | decl | initializer shape | manual class |
|---|---|---|---|
| `caesar` | `main` | six calls to total cipher/round-trip thunks, then concatenation | pure terminating computation |
| `calc` | `main` | recursive lex/parse/eval/print calls under `Trace` handlers | effectful/Div-capable |
| `codec-contract` | `main` | `Shift7` encode/decode under its handler | effectful (handled) |
| `dst-rounds-const` | `main` | local `Div, Sched` recursive driver under `Sched` | effectful/Div-capable |
| `dst-rounds-lcg` | `main` | same local driver with the LCG policy | effectful/Div-capable |
| `hostio-echo` | `main` | console performs under `Io_Console` handler | effectful (handled) |
| `json` | `main` | recursive parse/print/tag calls | Div-capable |
| `ndet-repkv-fail-a` | `main` | `Choice.pick` delivery simulation under handler | effectful (handled) |
| `ndet-repkv-fail-b` | `main` | same simulation, one-drop policy | effectful (handled) |
| `ndet-replicated-kv-a` | `main` | `Choice.pick` order simulation under handler | effectful (handled) |
| `ndet-replicated-kv-b` | `main` | same simulation, alternate policy | effectful (handled) |
| `ndet-sim-kv-a` | `main` | six `Choice.pick` calls under handler | effectful (handled) |
| `ndet-sim-kv-b` | `main` | same simulation, alternate policy | effectful (handled) |
| `nqueens` | `q4` | call `solve 4`, whose declared row contains `Div` | Div-capable |
| `nqueens` | `q5` | call `solve 5`, whose declared row contains `Div` | Div-capable |
| `nqueens` | `q6` | call `solve 6`, whose declared row contains `Div` | Div-capable |
| `nqueens` | `main` | arithmetic over already-computed `q4/q5/q6` | pure terminating computation |

The result is **2 pure terminating** and **15 effectful/Div-capable**, with no constructor-application
false positives. More importantly, all 17 belong to entry files: **14 are `main` bindings** (including
`nqueens.main`), while the remaining three are `nqueens.q4/q5/q6`. No imported library contributes a
computation-form initializer in any resolved journey. Therefore:

- an inert-**library** declaration rule has zero migration cost in the current corpus;
- an inert-**all-top-levels** rule would fight the current `main` entry convention and rewrite 13 actor
  journeys for no module-linking benefit;
- if entry initialization is also forbidden, the concrete non-`main` cost is only `nqueens.q4/q5/q6`,
  which can move under `main` or become suspended definitions.

This completes the measurement input but does not choose the language contract. Whether `main` is a
distinguished executable initializer, entry files retain ordered initialization, or programs return to a
trailing body is an operator-visible surface decision.

The aggregate battery indirectly guards this conclusion: if its pinned computation-form count moves from
17, entry ownership and all manual classes must be re-audited before the inert-library conclusion is
re-cited.

## Plan

1. [x] Attempt the cheapest row-based census and stop on coverage/meaning falsifiers.
2. [x] Correct published row semantics and retain both red poles.
3. [x] Implement hidden resolver-aware syntax classification and census all 61 examples.
4. [x] Update Q34/live map, regenerate derived views, and close skeptical advisor review.
5. [x] Run full convergence and publish the bounded measurement.
6. [x] Refute name/position-based checker attribution and manually classify all 17 residual sites.

## Status

- [x] Started 2026-07-18
- [ ] In flight: none; successor completed in ADR-0118 and `PATH-inert-top-level-language-contract`
- [ ] Blockers: none
- [x] Completed 2026-07-18
- Focused evidence: the successor contract probe extends `tools/test-initializer-census.sh` to
  **12/12** while preserving this census and its row poles; compiled build passes **1456 jobs**.
- Convergence evidence: `CHANGELOG_STABLE_REF=73af9668 just fitness` and
  `CHANGELOG_STABLE_REF=73af9668 just verify` pass; direct battery execution passes **33/33**, both
  **61-example** engine journeys remain green, and live proof facts match. The persistent Fable 5
  audit found no blocker after independently checking classifier polarity, arithmetic/accounting,
  resolve-failure behavior, actor-journey tie-backs, constructor under-approximation, and recursive
  knot assumptions.
- Published baseline: `ab8ea3ea` on `origin/codex/top-level-initializer-census`.
- Successor outcome: Option A removed the three `nqueens.q4/q5/q6` computation occurrences. The
  current 61-journey census is 233 manifest + 24 recursive + 14 computed `main`s = 271; the 274/17
  figures above remain the historical pre-decision baseline that priced the migration.
- Retained successors: generic bare-projection coverage repair; explicit binding provenance only after a
  second concrete consumer; initialization-contract design now has complete corpus input.
- Reopen / observe: `linkReady` stays false; this census changes no artifact or linking authority.

## Owner

- Agent / human: Codex, with persistent Fable 5 advisor in Herdr `lang-bang`
