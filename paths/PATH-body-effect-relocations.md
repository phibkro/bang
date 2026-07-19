# PATH-body-effect-relocations — expose the digest/runtime label correspondence

> Reify the already-validated body-digest effect quotient as per-export relocation rows, while
> keeping canonicalized artifacts, initializer slots, and linking authority explicitly absent.

## Seam

- **From checkpoint**: body-slice v2 already reverses every used user-effect runtime label through
  the elaborator table, sorts by qualified semantic name, and relabels only its digest input.
- **To checkpoint**: every sliced export exposes that exact table as
  `(name, canonicalLabel, runtimeLabel)` rows; decided-absence exports carry `null` and effect-free
  slices carry the complete empty list.
- **Contract preserved**: accepted programs, checking, lowering, runtime allocation, emitted code,
  initialization order, digest values, interfaces, and the kernel are unchanged.

## Layer

- [ ] Kernel  [x] Compiler query  [ ] Surface language  [x] Meta (tests/docs)

## Actor journey / observable outcome

- **Actor / need**: an artifact/link-tool author needs to see which contextual runtime labels a
  body observation would have to relocate to its stable semantic effect identities.
- **Public starting point**: `bang query dump <entry.bang>` → a sliced `moduleBodies[].exports[]` row.
- **Terminal observation**: `effectRelocations` contains every used user effect, semantic-name sorted.
  `canonicalLabel` is dense from 4 within the digest-local domain; `runtimeLabel` is the current
  whole-program allocation. Built-ins 0-3 are fixed and omitted.
- **Adverse / recovery route**: inserting an unrelated earlier effect preserves semantic name,
  canonical label, and body digest while moving the runtime label `4 → 5`. Changing only the effect
  identity moves both the semantic row and digest. Missing reverse lookup still nulls all body facts.
- **Downstream journey released**: an actual canonical body artifact can consume this table rather
  than rediscover label identity. Import/initializer slots remain separately gated.

## Feeds the constraint

- **Binding constraint now**: body identity is semantic, but the lowered `Comp` still contains
  resolver-contextual dense labels and is not serialized as an artifact.
- **How this path feeds it**: publish the precise correspondence already used by the fail-closed
  digest computation. Do not mutate or claim an artifact until a consumer carries canonicalized code.

## Prospective systemic review

| concern | horizon + evidence | likelihood / impact / late cost | disposition now | reopen trigger |
|---|---|---|---|---|
| contextual runtime label is mistaken for stable identity | unrelated-earlier-effect pole realizes `4 → 5` | realized / critical / high | **pair it with qualified name + canonical label and document contextuality** | runtime allocation changes |
| digest-local canonical label is mistaken for encoded artifact label | no body artifact exists | high / critical / medium | **retain `linkReady=false`; state no production `Comp` is rewritten** | canonical artifact bytes land |
| partial user-effect table looks complete | existing exhaustive kernel traversal + fail-closed reverse lookup | low / critical / high | **derive rows from the same `canonicalBodyEffects` result as the digest** | label-bearing kernel shape changes |
| effect-free and unsupported exports both appear as no data | current coverage has both cases | realized / high / low | **use `[]` for sliced/effect-free and `null` for decided absence** | status vocabulary changes |
| built-in labels appear silently missing | built-ins are fixed 0-3 | medium / medium / low | **scope rows explicitly to relocatable user effects** | built-in labels become relocatable |
| rows are joined to source initializers | ADR-0117 provenance gate | high / critical / high | **no initializer/source ID, row, slot, DCE, or reorder field** | stable binding provenance lands |
| new nested field breaks consumers | additive schema policy | medium / high / medium | **always-present field; existing consumers ignore unknown keys** | schema compatibility policy changes |

## Baseline, falsifiers, and evidence

- **Baseline**: the body-digest implementation consumed a private sorted
  `(qualifiedName, runtimeLabel)` table and discarded it after hashing; users could observe stability
  but not the relocation it implied.
- **Smallest tracer bullet**: reuse the two existing `Target` fixtures. Both body digests remain equal;
  rows remain `Lib_Target, canonicalLabel=4`, while `runtimeLabel` moves from 4 to 5.
- **Identity falsifier**: symmetric `Alpha` and `Beta` bodies both use canonical label 4 but expose
  distinct qualified names and distinct digests.
- **Coverage falsifier**: a pure sliced export emits `[]`; generic and structural decided-absence
  exports emit `null`, so omission cannot masquerade as an empty complete table.
- **Single construct**: `moduleBodyObservation` calls `canonicalBodyEffects` once and returns both the
  unchanged v2 digest and the exported rows. There is no second traversal, reverse lookup, or parser.
- **Assumptions / exclusions**: this is a query observation, not canonicalized code. No serialized
  `Comp`, import slot, initializer slot, linker, relocation application, artifact validation,
  cache authority, DCE, reordering, separate compilation, or per-binding effect attribution lands.

## Plan

1. [x] Define the relocation contract at the existing fail-closed digest seam.
2. [x] Return digest and relocation rows from one canonical-effect observation.
3. [x] Gate contextual runtime movement, semantic discrimination, empty, and null coverage poles.
4. [x] Regenerate public projections and run full convergence.
5. [x] Publish the increment and hand canonical artifact encoding forward.

## Status

- [x] Started 2026-07-19
- [ ] In flight: body-effect relocation tracer
- [ ] Blockers: none
- [x] Completed 2026-07-19 at `a958b7e3`
- Convergence evidence: `lake build Bang.Frontend.Query bang` passes **1452 jobs**;
  `tools/test-query.sh` passes **276/276** without changing any body digest; the full `just verify`
  semantic/runtime/proof batteries and the staged `CHANGELOG_STABLE_REF=4baba161 just fitness` pass.
- Reopen / observe: `runtimeLabel` is deliberately unstable under environment changes;
  `canonicalLabel` becomes an artifact contract only if future serialized code actually uses it.

## Owner

- Agent / human: Codex
