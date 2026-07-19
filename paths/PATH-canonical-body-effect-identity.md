# PATH-canonical-body-effect-identity — bind semantic effect names into body observations

> Quotient declaration-order label allocation at the query digest boundary while preserving the
> qualified effect identity that makes two otherwise symmetric bodies semantically different.

## Seam

- **From checkpoint**: `PATH-reachable-module-body-slices` published environment-relative concrete
  export digests, with one retained red pole: an unrelated earlier effect moved an unchanged
  effect-using body from `27c0555a0c82b9e4` to `1ce72041af068091`.
- **To checkpoint**: body-slice v2 hashes a canonically relabelled `Comp` together with the sorted
  canonical-label-to-qualified-effect-name table actually used by that slice.
- **Contract preserved**: runtime allocation, typing, lowering, execution, Wasm emission, interfaces,
  and the kernel remain byte-for-byte on their existing label representation; this is a Query-local
  change-detector refinement only.

## Layer

- [ ] Kernel  [x] Compiler query  [ ] Surface language  [x] Meta (tests/docs)

## Actor journey / observable outcome

- **Actor / need**: a build-tool author compares an unchanged exported body after an unrelated effect
  declaration is inserted earlier in the resolved program.
- **Public starting point**: `bang query dump <file.bang>`.
- **Terminal observation**: the export retains its body digest under unrelated effect-label shifts;
  `algorithm` says `bang-module-body-slice-comp-v2-uint64`.
- **Adverse / recovery route**: changing the effect identity from qualified `A` to qualified `B`, or
  failing to reverse a lowered user label through the elaborator's effects table, cannot produce a
  plausible preserved row: the former changes the digest and the latter nulls all `moduleBodies`.
- **Downstream journey released**: import-slot/link measurement can distinguish an honest body
  identity from the still-order-sensitive runtime relocation problem.

## Feeds the constraint

- **Binding constraint now**: the reachable slice is structurally scoped, but `hashComp` observes the
  elaborator's dense user labels, so declaration order still leaks through handler identity.
- **How this path feeds it**: canonicalise only the digest input, binding both structure and semantic
  names, while leaving runtime labels untouched for the later link contract that genuinely consumes
  them.

## Prospective systemic review

| concern | horizon + evidence | likelihood / impact / late cost | disposition now | reopen trigger |
|---|---|---|---|---|
| one-effect slices collapse `A` and `B` to the same rank | pre-scope quotient audit | realized / critical / low | **hash the sorted rank-to-qualified-name table with the relabelled `Comp`** | a new identity source is not table-bound |
| a label-bearing kernel position is missed | five current positions across `Handler`/`Val` | medium / critical / high | **exact mapping guards per position plus exhaustive matches** | an existing constructor gains a label field |
| identity/round-trip checks are overclaimed as coverage | advisor audit | realized / medium / low | **claim bijection only; use exact position guards for completeness** | traversal evidence prose drifts |
| unknown user label is normalized plausibly | valid lowered programs should be table-total | low / critical / high | **refuse the complete `moduleBodies` projection** | producer/table inconsistency is observed |
| digest canonicalisation is mistaken for runtime stability | runtime and emitters retain dense labels | high / critical / high | **keep `linkReady:false`; document relocation residual** | a link consumer exists |
| 64-bit composite is promoted to cache authority | unchanged probe strength | high / critical / high | **keep `cacheKeySafe:false` and bind the empty table uniformly** | collision-resistant versioned artifacts land |
| Query-local traversal drifts from kernel shape | new constructors break exhaustive compilation; new fields do not | medium / high / medium | **document the update obligation and gate all five current positions** | `Val`/`Comp`/`Handler` changes |

## Baseline, falsifier, and evidence

- **Published red baseline**: `ead8a94a` exposes `27c0555a0c82b9e4 → 1ce72041af068091` when only an
  unrelated earlier effect is inserted; interface identity remains unchanged.
- **Pre-scope representation probe**: a total Query-local mutual traversal compiles over every
  `Comp`, `Val`, and `Handler` constructor. Current label positions are exactly `Val.vcap` and
  `Handler.state`/`throws`/`transaction`/`custom`.
- **Pre-scope algebra probes**: identity mapping and a permutation followed by its inverse preserve
  the structural hash. These establish consistent bijection on traversed positions, not completeness.
- **Pre-scope falsifier caught**: rank-by-used-name alone maps a single used `A` and a single used `B`
  both to label 4. The digest must also bind the qualified-name table or it destroys discrimination.
- **Smallest tracer bullet**: flip the published unrelated-effect pole green, then change only the
  effect name/owner in a symmetric body and require the digest to move.
- **Broader convergence gate**: five exact label-position guards, focused query battery, generated
  public views, full build/audit/fitness/verify, and persistent-advisor skeptical review.
- **Assumptions / exclusions**: qualified elaborator names are the semantic identity already used by
  checked interfaces. No runtime relabeling, allocation change, alpha-equivalence theorem, proof-spine
  claim, emitter change, artifact, linker, store, scheduler, cache hit, or speedup is claimed.

## Plan

1. [x] Publish the body-slice baseline and retain its order-sensitive red pole.
2. [x] Probe total traversal, identity/round-trip behavior, and the single-effect identity collapse.
3. [x] Implement uniform composite v2 hashing and fail-closed reverse lookup.
4. [x] Gate five exact label positions and end-to-end invariance plus semantic discrimination.
5. [x] Regenerate public projections, run full convergence, and close skeptical advisor review.
6. [ ] Publish the converged increment and hand its residual to the link-seam successor.

## Status

- [x] Started 2026-07-18
- [x] In flight: implementation and convergence complete; publication next
- [ ] Blockers: none
- [ ] Completed
- Focused evidence: `Bang/Frontend/Query.lean` compiles; `tools/test-query.sh` passes **268/268**;
  `just autoquality` passes.
- Convergence evidence: `CHANGELOG_STABLE_REF=5e57d4a9 just fitness` and `just verify` pass;
  the latter builds **1452 jobs**, passes all **31/31** batteries and both **61-example** engine
  journeys, and matches live proof facts. The persistent Fable 5 skeptical audit found no blockers
  after independently checking every kernel label carrier and `ClauseKey`.
- Reopen / observe: `linkReady` remains false until runtime label relocation and import-slot
  validation have a real link consumer; `cacheKeySafe` retains the body-slice collision/version bar.

## Owner

- Agent / human: Codex, with persistent Fable 5 advisor in Herdr `lang-bang`
