# PATH-module-law-contracts — make checked interfaces aware of declared public laws

> Attribute every exported trait/effect law to its owning declaration so interface invalidation
> sees the language's semantic contracts without mistaking a declaration for enforcement or reuse.

## Seam

- **From checkpoint**: `PATH-interface-diff-consumer` can decide checked type/shape fanout but
  returns `indeterminate` when global instance-law evidence moves without a module-owned contract.
- **To checkpoint**: each public trait/effect export carries its declared `{name, params, body}` law
  contracts; changing one moves the owning interface and its reverse-transitive candidates even when
  no handler or impl exists.
- **Contract preserved**: top-level `laws` remains an instance/realization view. The new fact is a
  declaration projection, not a second discovery walk, proof result, cache key, or artifact.

## Layer

- [ ] Kernel  [x] Compiler query  [ ] Surface language  [x] Meta (consumer/tests/docs)

## Actor journey / observable outcome

- **Actor / need**: a build-tool author compares two dump snapshots after a library's public law
  statement changes and needs to attribute that contract movement before computing dependent work.
- **Public starting point**: `bang query dump <entry.bang>`, followed by
  `python3 tools/interface-diff.py old-dump.json new-dump.json`.
- **Terminal observation**: the owning public export's declared law changes, its v2 interface digest
  moves, and the ordinary interface fanout marks the owner and all reverse-transitive dependents.
- **Adverse / recovery route**: the same change with no handler/impl is still visible; a global law
  instance delta not explained by a public declared-law delta remains fail-loud `indeterminate`.
- **Downstream journey released**: the checked interface boundary covers public types, shapes, and law
  statements, leaving lowered identity/body/linking—not missing semantic contract ownership—as the
  next artifact constraint.

## Feeds the constraint

- **Binding constraint now**: the shipped consumer's machine-checked red gate named
  `module-owned-public-law-contract`; declaration laws are BANG's differentiating semantic surface.
- **How this path feeds it**: add the smallest owner-local declaration fact and consume it through the
  already shipped comparison journey, rather than designing a cache or another measurement surface.

## Prospective systemic review

| concern | horizon + evidence | likelihood / impact / late cost | disposition now | reopen trigger |
|---|---|---|---|---|
| law text inherits merge-context churn | strongest pre-scope falsifier; `showSurf` sees qualified merged `Surf` | high / critical / high | **gate unrelated-effect insertion and reversed import order before schema acceptance** | unchanged law text/digest moves |
| declared laws are confused with discovered instances | existing `laws` is a realization cross-product | high / high / high | **new export field; join both views only by stable `contractId`; retain fail-loud residue** | a consumer joins by presentation name |
| private law bodies leak into public interfaces | public schema addition | medium / critical / high | **project only resolver-owned exported declarations** | a private trait/effect law appears in `moduleInterfaces` |
| interface algorithm silently changes meaning | digest payload gains a field | certain / high / high | **bump the interface algorithm to v2 and reject cross-algorithm comparison** | old/new payloads share an algorithm label |
| textual equality is overclaimed as semantic equality | v1 uses formatted surface syntax | high / high / high | **state canonical-text identity only; retain alpha/normalization exclusions** | equal semantics needlessly churn in a real workload |
| law declaration is mistaken for enforcement | no dependent proof/check artifact exists | high / critical / high | **retain explicit no-skip/no-reuse flags and name non-enforcement** | output implies the law was discharged |
| schema addition expands into cache/artifact work | lowered body/link contract remains absent | high / high / high | **keep cache/artifact/store/linker out of scope** | independent lowered artifact lands |
| export payload/performance grows unexpectedly | laws are small source declarations in current projects | low / medium / low | **emit full canonical text; measure before hashing/indirection** | representative dump size or latency crosses a budget |
| one explained delta masks an unrelated law-instance delta | skeptical compound-edit review found existence-based attribution | high / high / medium | **attribute changed rows per stable contract ID and gate combined edits** | combined changes yield a stronger verdict than either alone |
| three version domains are conflated | dump schema v1, interface algorithm v2, diff result v2 | high / medium / medium | **name each domain explicitly and diagnose pre-v2 dumps before field parsing** | docs or errors call one version another |

## Baseline, falsifier, and evidence

- **Baseline / red observation**: a public `Lib.Gate` law-body edit moved global instance evidence but
  preserved `Lib`'s name-only interface; with no handler it was completely invisible to the dump's law
  evidence and the consumer could not produce a complete decision.
- **Pre-scope kill shot**: existing `showSurf` law-instance text stayed byte-identical when an unrelated
  earlier effect was inserted and when entry import order was reversed around a law using two selected
  cross-module values (`Lib_one`/`Lib_zero` after qualification). This permits the narrow schema tracer;
  the same journeys become committed end-to-end gates over the declared export fact.
- **Smallest tracer bullet**: add declared laws to public export records, version the digest algorithm,
  and teach the existing two-dump consumer when a global law delta is explained by that public fact.
- **Skeptical-review falsifier**: combining `Lib_Gate`'s explained public-law edit with a new private
  handler for `Side_Other` must remain indeterminate for `Side_Other`; per-row `contractId` attribution
  prevents the explained Lib delta from masking the unrelated realization row.
- **Strongest falsifier**: an unchanged law-bearing `Lib` export changes digest/body text under unrelated
  module insertion or import-order reversal. If fixing it requires qualification/representation redesign,
  stop and ship no schema field.
- **Assumptions / exclusions**: law identity is canonical rendered surface text, not alpha-equivalence,
  normalization, theorem equivalence, enforcement, or behavioral truth. Export order, global type-hole
  markers, dense lowered labels, independent checking/lowering, artifact validation, linking, persistence,
  cryptographic keys, scheduling, cache hits, and speedups remain outside the claim. Attribution is
  contract-granular: a new private realization row for a contract whose public law moved in the same diff
  is covered by that moved contract; this is safe because the owner and dependents are already candidates.

## Plan

1. [x] Rank the consumer's demonstrated gap with the persistent advisor and probe rendering stability.
2. [x] Add owner-local declared-law facts to public exports and version the interface digest contract.
3. [x] Upgrade the consumer and gate handler-free visibility, attribution, privacy, and stability.
4. [x] Regenerate governed docs, obtain skeptical review, run convergence, and publish.

## Status

- [x] Started 2026-07-18
- [ ] In flight: none
- [ ] Blockers: none
- [x] Completed 2026-07-18
- Focused evidence: `tools/test-query.sh` — **223 passed, 0 failed** with Python + jq available.
- Convergence evidence: exact-tree `just verify` passed both Lean builds (**1447** verification jobs,
  **1452** battery jobs), **31/31** batteries, the live 33-theorem axiom audit, all architecture/proof
  falsification poles, and the full fitness bundle.
- Skeptical closure: the Fable 5 advisor found that existence-based attribution could let one explained
  public-law edit mask an unrelated realization edit. Stable per-row contract IDs plus the combined-edit
  journey closed that hole; the advisor re-reviewed the correction as ready for convergence.
- Retained stop condition: if committed merge-context invariance gates fail and repair crosses into
  resolver qualification or semantic law normalization, remove the schema work and persist the finding.
- Reopen / observe: any unexplained global law-instance delta reported as complete, any private law in a
  public export, or any interpretation of a declared contract as a checked proof or reusable artifact.

## Owner

- Agent / human: Codex, with persistent read-only Fable 5 strategic advisor in Herdr
