# PATH-reachable-module-body-slices — measure concrete export bodies without inventing artifacts

> Slice the merged value-declaration graph per concrete export, keep the elaboration environment
> whole, and expose exactly which body identity is measured and which reuse claims remain false.

## Seam

- **From checkpoint**: `PATH-bang-interface-consumer` closed the first language-level fact-consumer
  loop, while Q34 still had only one whole-program `Comp` and no independently observable export body.
- **To checkpoint**: `bang query dump` carries one explicit body row for every public export; concrete
  `let`/`letRec` exports have environment-relative reachable-slice digests, while generic and
  non-value exports state why no concrete body digest exists.
- **Contract preserved**: every slice runs through the unchanged production checker/lowerer; modules
  still elaborate into the flat kernel, the non-value environment remains global, and no artifact,
  linker, store, scheduler, cache hit, or separate-compilation claim is introduced.

## Layer

- [ ] Kernel  [x] Compiler query  [ ] Surface language  [x] Meta (tests/docs)

## Actor journey / observable outcome

- **Actor / need**: a build-tool author needs to distinguish a concrete exported body's reachable
  implementation from unrelated lexical siblings before designing any module artifact.
- **Public starting point**: `bang query dump <file.bang>`.
- **Terminal observation**: `moduleBodies` parallels `moduleInterfaces` by logical module. Every public
  export has `{id,name,kind,status,digest}`; concrete top-level `let`/`letRec` rows are `sliced`, a
  generic `fn` is `unsupported-generic-fn`, and a non-value kind is `no-body-kind`. The enclosing fact
  says `cacheKeySafe=false` and `linkReady=false`.
- **Adverse / recovery route**: if any concrete export's claimed closure fails production lowering,
  the entire `moduleBodies` projection is `null` while the rest of the dump survives. A consumer never
  mistakes a partial list for complete coverage.
- **Downstream journey released**: effect-label identity and then a body/link validation contract can
  start from measured environment coupling rather than a guessed independently compiled module.

## Feeds the constraint

- **Binding constraint now**: `withQueryBody` changes only the trailing expression; `foldLetDecls`
  still nests every top-level lexical value into the resulting `Comp`, so it is not per-export.
- **How this path feeds it**: remove only unreachable value declarations (`letD`/`letRecD`/`fnD`),
  preserve source order and every non-value declaration, root the closure at both the selected export
  and the retained environment, then ask the existing typed pipeline to validate the result.

## Prospective systemic review

| concern | horizon + evidence | likelihood / impact / late cost | disposition now | reopen trigger |
|---|---|---|---|---|
| ref under-coverage yields false preservation | pre-scope impl/helper probe: export-only closure failed lowering | realized / critical / high | **root every retained non-value declaration and null the whole projection on any slice failure** | a new declaration/binding form bypasses the gate |
| implicit dispatch keeps environment-reachable helpers globally live | the same impl probe; ref edges cannot decide type-directed impl selection | realized / medium / medium | **accept safe over-retention and name it** | type-directed impl/handler reachability exists |
| generic template is presented as concrete code | selecting a public bounded `fn` cannot lower without an instantiation | realized / high / high | **emit `unsupported-generic-fn` with `digest:null`** | a stable monomorphization identity/instantiation fact lands |
| omission is mistaken for forgotten coverage | additive public dump schema; export kinds can change | high / high / high | **emit one explicit row per public export** | schema versioning replaces additive evolution |
| body facts collapse the checked-interface firewall | body edits must preserve `moduleInterfaces` | high / critical / high | **keep `moduleBodies` as a parallel top-level fact and use a fresh hash domain** | a validated artifact deliberately composes both contracts |
| 64-bit observation becomes cache or link authority | first body digest consumer; no artifact verifier exists | high / critical / high | **emit `cacheKeySafe:false` and `linkReady:false`** | collision-resistant domains plus exact artifact/link verification land |
| global environment churn causes false invalidation | live unrelated-effect pole moves the effect-using sliced body | realized / high / high | **retain the red gate; do not relabel here** | effect-label identity stabilization is scoped |
| per-export lowering scales poorly | dump already repeats checked projections; no latency budget or large project exists | medium / medium / low | **record cost, make no performance claim** | measured dump latency crosses a named actor budget |
| invalid subjects or internal mismatch receive plausible rows | production lowering is the slice's soundness oracle | medium / high / low | **null the projection, preserve other facts** | typed partial-result schema is intentionally designed |

## Baseline, falsifier, and evidence

- **Baseline / red observation**: in a live two-module program, editing only unused `Lib.unrelated`
  preserved the exact `Lib` interface digest `1e689a399109f5aa` but moved the supposed selected-body
  proxy `9ba6727b3122c4ac → 2aef16e70fe42aba`. The cheap
  `coreFingerprintOf(withQueryBody p "Lib_selected")` composition is therefore refuted.
- **Pre-scope positive probes**: a prototype reachable slice preserved `acac0bff53879174` across an
  unused sibling edit, moved it to `85a5e48a1013feb7` when a transitive helper changed, and lowered a
  self-recursive export deterministically as `0f1294a8d46b9491`.
- **Pre-scope adverse probe**: an impl body referenced a top-level helper through ref edge
  `Inc → helper`. Export-only roots dropped it and lowering refused; adding retained non-value
  declarations as roots lowered successfully (`824ac35ad9ccc0ed`). This fixes the scope boundary
  before it hardens into schema.
- **Retained negative pole**: inserting an unrelated earlier effect moves an effect-using sliced body
  `27c0555a0c82b9e4 → 1ce72041af068091`. The environment is intentionally whole; this is the demand
  signal for stable lowered effect identity, not a defect normalized inside this tracer.
- **Smallest tracer bullet**: one imported `Lib` exports a selected value, its transitive helper, an
  unrelated sibling, a bounded-function dependency, and non-value exports; query the compiled CLI
  before and after sibling, reachable-helper, and effect-order edits.
- **Broader convergence gate**: focused query battery, example journeys, generated reference and fact
  views, exact-tree fitness, and `just verify`.
- **Assumptions / exclusions**: syntactic ref closure is a safe over-approximation only because the
  retained environment and its value dependencies are roots and lowering is the final oracle. No
  environment slicing, type-directed impl selection, stable runtime labels, generic-instantiation
  artifact, cross-program reuse, linker, storage, cache safety, separate compilation, or speedup is
  claimed. Each concrete export currently repeats full production checking/lowering; the first measured
  slow-dump actor report is the trigger for incremental query execution, not permission to optimize now.
  Surface `let rec … and …` groups are expression-local inside one declaration body, so they remain
  intact with that declaration rather than becoming separately sliced top-level siblings.

## Plan

1. [x] Refute the cheap `withQueryBody` composition and persist the whole-program contamination.
2. [x] Probe transitive/self-recursive closure, implicit environment dependencies, generic functions,
   and unrelated-effect coupling before freezing scope.
3. [x] Implement the pure reachable-value projection and additive `moduleBodies` fact.
4. [x] Gate explicit coverage, sibling stability, reachable sensitivity, refusal, and retained coupling
   through the compiled CLI.
5. [x] Regenerate public views, run full convergence, and report to the persistent advisor.
6. [x] Publish the converged increment and hand the retained red pole to the advisor-ranked successor.

## Status

- [x] Started 2026-07-18
- [ ] In flight: none; successor is the canonical body-effect identity tracer
- [ ] Blockers: none
- [x] Completed 2026-07-18
- Evidence: `lake env lean Bang/Frontend/Query.lean`; `lake build bang` (1452 jobs);
  `tools/test-query.sh` (264/264); `just autoquality`; `CHANGELOG_STABLE_REF=79adeeb3 just
  fitness`; and `CHANGELOG_STABLE_REF=79adeeb3 just verify` all pass. The persistent Fable 5
  implementation audit found no blockers.
- Published baseline: `ead8a94a` on `origin/codex/module-body-fingerprint-probe`; the successor keeps
  the observed `27c0555a0c82b9e4 → 1ce72041af068091` order-sensitivity as its dated red evidence.
- Reopen / observe: `linkReady` remains false until an unchanged dependency body can be validated and
  linked without whole-program elaboration; `cacheKeySafe` additionally requires collision-resistant,
  compiler/kernel-versioned identity.

## Owner

- Agent / human: Codex, with persistent Fable 5 advisor in Herdr `lang-bang`
