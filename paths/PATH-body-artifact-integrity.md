# PATH-body-artifact-integrity — bind canonical bytes to stable relocation identity

> Add a domain-separated SHA-256 address and a verifying backend consumer for the exact canonical
> body artifact plus semantic relocation identity, without laundering integrity into type or link safety.

## Seam

- **From checkpoint**: canonical `Comp` bytes round-trip structurally and reach unchanged backends, but
  the published 64-bit body digest remains an experimental change detector and no consumer verifies a
  collision-resistant address before decoding.
- **To checkpoint**: one SHA-256 address binds the versioned artifact JSON and sorted
  `(semanticName, canonicalLabel)` rows; a backend consumer recomputes that address before decoding,
  compiling, or running the body.
- **Contract preserved**: the v2 body digest, runtime relocation rows, checking/lowering, runtime labels,
  complete dump, emitted code, initialization order, and all negative validation/link flags are unchanged.

## Layer

- [ ] Kernel  [x] Core hashing/address  [x] Compiler query  [x] Backend consumer  [x] Meta (tests/docs)

## Actor journey / observable outcome

- **Actor / need**: an artifact-store or linker author needs to reject corrupted/substituted body input
  before it reaches a backend and to compare stable identities without trusting a 64-bit probe.
- **Public starting point**: `bang query body-artifact <export-id> <entry.bang>`.
- **Terminal observation**: the result carries a 64-hex SHA-256 address. The backend's verified entry
  point accepts artifact bytes, stable semantic relocation rows, and the claimed address only when
  recomputation agrees, then delegates to the existing structural decoder and backend.
- **Adverse / recovery route**: byte changes, semantic-name changes, canonical-label changes, malformed
  addresses, and wrong domain versions fail loud before decode/compile/run. Contextual runtime-label
  movement does not change the address.
- **Downstream journey released**: a store can key immutable envelope content without inventing hashing
  or silently aliasing distinct semantic effects. Independent typing and complete link inputs remain open.

## Feeds the constraint

- **Binding constraint now**: Q34's canonical-artifact record and the public
  `ModuleBodyArtifactFact` flags establish that supplied core bytes are neither independently typed nor
  complete linker input; treating their 64-bit observational digest as durable authority would compound
  that trust gap.
- **How this path feeds it**: give consumers collision-resistant, semantic-effect-aware envelope
  integrity while preserving `independentlyTypeValidated=false`, `cacheKeySafe=false`, and
  `linkReady=false`; this isolates the remaining checker/link contract instead of hiding it.

## Why integrity, not type validation

The existing lowered-`Comp` `TypeCheck.checkC` is explicitly a pure-fragment spike: it rejects caps,
folds, performs, handlers, and other current constructors. The production checker runs on annotated
`Surf` before lowering, so replaying it does not independently validate supplied artifact bytes. Calling
either result independent validation would be a sustained correctness debt. A complete executable core
checker plus a soundness connection to `HasCTy` is a separate, consumer-pulled project; this tracer keeps
`independentlyTypeValidated=false`.

## Prospective systemic review

| concern | likelihood / impact / late cost | disposition now | reopen trigger |
|---|---|---|---|
| 64-bit probe becomes persistent authority | high / critical / high | **add SHA-256 with an explicit address domain** | cryptographic policy changes |
| same canonical code aliases different named effects | realized / critical / high | **bind semantic name + canonical label beside bytes** | relocation model changes |
| contextual allocation destroys stable addresses | high / high / medium | **exclude runtime labels; retain them as checked link inputs** | runtime labels become canonical |
| ambiguous concatenation creates second-preimage structure | medium / critical / high | **hash one canonical JSON array preimage** | address format v2 |
| home-grown SHA implementation is subtly wrong | medium / critical / medium | **standard vectors + differential CLI oracle in tests** | crypto dependency becomes available |
| integrity is mistaken for typing/linking | high / critical / high | **keep all validation/cache/link flags false and name the guarantee narrowly** | independent checker + link envelope land |
| hash work bloats complete dumps | medium / high / low | **compute only in the existing on-demand point query** | measured bulk consumer appears |

## Baseline, falsifiers, and evidence

- **Baseline**: `digest` is 16 hex digits and deliberately not collision-safe; `artifact` has no address.
- **Smallest tracer**: a point-query artifact reports a deterministic address; a verifying consumer runs
  the unchanged pure and effectful samples only after recomputation succeeds.
- **Cryptographic poles**: SHA-256 empty/`abc`/multi-block standard vectors and a system `sha256sum`
  differential over produced preimages.
- **Identity poles**: unrelated earlier effects preserve the address despite runtime `4 → 5`; equal
  canonical bytes under different qualified effect names produce distinct addresses.
- **Tamper poles**: modified bytes, name, canonical label, domain, or claimed digest reject.
- **Exclusions**: no type certificate/checker, cache hit, persistence layer, scheduler, compiler-version
  compatibility promise, import/initializer slot, relocation application, linker, DCE, or reuse skip.

## Plan

1. [x] Record the integrity/type-validation boundary and exact address preimage.
2. [x] Implement and standard-vector gate a pure SHA-256 utility.
3. [x] Bind canonical bytes plus stable relocation identity and add verified backend entry points.
4. [x] Expose the address on demand and gate identity/tamper journeys end to end.
5. [x] Regenerate projections, run full convergence, publish, and hand core typing/link inputs forward.

## Status

- [x] Started 2026-07-19
- [ ] In flight: body artifact integrity tracer
- [ ] Blockers: none
- [x] Completed 2026-07-19 at `e60d2426`
- Convergence evidence: the full build passes **1456 jobs**; `tools/test-query.sh` passes **289/289**
  with an independent Python `hashlib` oracle, runtime-label invariance, semantic-name discrimination,
  and negative trust flags; all **33/33** end-to-end batteries pass; live proof facts agree at **23 Spec
  headlines / 33 Audit reports**; `just audit`, the exact-tree `just verify`, and the commit hook's
  independent fitness + verify rerun all pass with `CHANGELOG_STABLE_REF=934d1512`.
- Reopen / observe: the SHA-256 address is integrity authority for exact canonical body bytes and stable
  effect identity only. Open a separate path when a concrete cache/link consumer pulls an executable
  core checker or explicit import/initializer/relocation application envelope; do not reinterpret
  integrity as typing, cache-hit, or link authority.

## Owner

- Agent / human: Codex
