# PATH-module-initialization-order — expose source occurrences without inventing rows

> Make today's strict module-initialization sequence observable from resolver-owned source programs,
> distinguish duplicate binding occurrences, and keep every post-elaboration/link claim visibly false.

## Seam

- **From checkpoint**: body-slice execution proved strict initialization observable; the initializer
  census bounded real usage; ADR-0117 preserved the language while forbidding guessed per-binding rows.
- **To checkpoint**: `bang query dump` exposes the complete resolver-source `let`/`let rec` occurrence
  sequence, dependency-first and source-ordered, with duplicate-safe snapshot-local identities.
- **Contract preserved**: accepted programs, initialization semantics, checking, lowering, runtime label
  allocation, body/interface digests, and the kernel are unchanged.

## Layer

- [ ] Kernel  [x] Compiler query  [ ] Surface language  [x] Meta (tests/docs)

## Actor journey / observable outcome

- **Actor / need**: an artifact/link-tool author needs to know which source initializers today's flat
  lowering sequences before the entry body, without assuming initializer-local effect attribution.
- **Public starting point**: `bang query dump <entry.bang>`.
- **Terminal observation**: `moduleInitialization` states
  `scope=resolver-source-initializer-order`, `order=dependency-first-source-order`,
  `sourceOccurrencesComplete=true`, and keeps `elaborationProvenance`, `perBindingEffects`, and
  `linkReady` false. Flat `moduleInitializers` rows carry snapshot-local `id`, `module`, full
  `sourceIndex`, global `order`, `name`, `kind`, and `strict-rhs|recursive-knot` mode.
- **Adverse / recovery route**: two declarations with the same name retain different IDs; reversing
  two independent imports reverses their initializer blocks rather than being canonicalized away.
- **Downstream journey released**: runtime-label relocation and import-slot work can now name the
  source initialization obligation explicitly. It still cannot join a row or lowered slot to one of
  these occurrences without the provenance ADR-0117 requires.

## Feeds the constraint

- **Binding constraint now**: current modules elaborate to one flat lexical `Comp`, where imported
  source initializers execute before entry initializers. A body slice alone does not encode that chain.
- **How this path feeds it**: retain the resolver's unmerged source programs in the exact order supplied
  to `mergeModules`, then project strict declarations before qualification or elaboration can erase
  aliases, duplicate names, or occurrence identity.

## Prospective systemic review

| concern | horizon + evidence | likelihood / impact / late cost | disposition now | reopen trigger |
|---|---|---|---|---|
| duplicate binder names collapse an initializer identity | retained two-`same` fixture | realized / critical / low | **key rows by module + full source declaration index** | source identity representation changes |
| import order is sorted away as “mere topology” | reversed independent imports | realized / critical / medium | **publish exact resolver traversal order** | language adopts order-independent initialization |
| source order is mistaken for final elaborated binding provenance | ADR-0117 kill shots | high / critical / high | **emit negative metadata; claim source scope only** | explicit provenance survives elaboration |
| `let rec` bodies are described as eagerly executed | current recursive-knot lowering | medium / high / medium | **separate `recursive-knot` from `strict-rhs`** | recursion lowering changes |
| implicit prelude/generated bindings are silently claimed complete | elaborator injects and rewrites after resolution | high / high / medium | **`sourceOccurrencesComplete` names the boundary; `elaborationProvenance=false`** | artifact consumes elaborated initialization |
| rows authorize DCE/reordering | missing per-binding row result | high / critical / high | **`perBindingEffects=false`, `linkReady=false`** | ADR-0117 revisit trigger fires |
| occurrence ID is promoted to a cross-edit content identity | source indices move on insertion | medium / high / medium | **document snapshot-local address, no digest/cache field** | stable source identities gain a consumer |

## Baseline, falsifiers, and evidence

- **Baseline**: `moduleDeps` exposed topology and `moduleBodies` exposed environment-relative export
  slices, but no fact represented the strict declaration chain whose divergence refuted standalone
  slice execution.
- **Smallest tracer bullet**: one dependency containing duplicate `let same` declarations plus an
  entry containing ordinary and recursive declarations. The compiled query returns six distinct,
  monotonically ordered occurrence rows.
- **Order falsifier**: `import A; import B` yields `A,B,@entry`; `import B; import A` yields
  `B,A,@entry`. Both programs run, and the fact preserves the current semantic ordering choice.
- **API boundary**: `moduleInitializerFactsOf` is a pure public projection over ordered
  `(module, Prog)` inputs. The IO resolver retains those unmerged inputs once and passes them to the
  existing `dumpJsonP`; no second filesystem walk or parser exists.
- **Assumptions / exclusions**: source occurrence completeness covers explicit resolver-owned
  `letD`/`letRecD` only. No implicit Prelude/generated binding inventory, RHS row, lowered binder
  identity, import slot, runtime relocation, artifact, cache key, linker, DCE, reordering, or separate
  compilation claim is made.

## Plan

1. [x] Preserve unmerged resolver source modules in dependency-first order.
2. [x] Add the pure duplicate-safe source occurrence projection and negative contract metadata.
3. [x] Gate single-file shape, duplicate names, recursive-knot mode, and reversed import order.
4. [x] Regenerate public views and run full convergence.
5. [ ] Publish the increment and hand the remaining runtime-label/import-slot wall forward.

## Status

- [x] Started 2026-07-19
- [x] In flight: source initialization contract tracer
- [ ] Blockers: none
- [ ] Completed
- Convergence evidence: `lake build Bang.Frontend.Query bang` passes **1452 jobs**;
  `tools/test-query.sh` passes **276/276**, and
  `CHANGELOG_STABLE_REF=2d92d9f1 just verify` passes the full repository gate.
- Reopen / observe: source occurrence rows remain useful if provenance later lands, but their IDs are
  snapshot-local and must not be retroactively treated as elaborated binding identities.

## Owner

- Agent / human: Codex
