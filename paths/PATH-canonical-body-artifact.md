# PATH-canonical-body-artifact — round-trip the canonical body slice

> Turn the existing digest-side canonical `Comp` into a versioned, strictly decoded body encoding,
> then consume the decoded term through an unchanged backend without claiming link or cache authority.

## Seam

- **From checkpoint**: a sliced export has a stable canonicalized `Comp`, a body digest, and the exact
  semantic/canonical/runtime effect relocation rows, but the canonical term is discarded after hashing.
- **To checkpoint**: `bang query body-artifact <export-id> [<file>]` materializes one deterministic
  `bang-core-comp-json-v1` encoding on demand; the public inverse rejects malformed, oversized,
  wrong-version, wrong-arity, and unknown-constructor input; an unchanged backend compiles/runs the
  decoded `Comp` in the tracer corpus.
- **Contract preserved**: checking, lowering, runtime allocation, body digest values, initialization
  order, interfaces, production execution, and emitted code are unchanged.

## Layer

- [ ] Kernel  [x] Core artifact codec  [x] Compiler query  [x] Backend consumer  [x] Meta (tests/docs)

## Actor journey / observable outcome

- **Actor / need**: an artifact/link-tool author needs actual canonical code that can be reconstructed,
  not a digest plus a relocation hint from which code would have to be guessed.
- **Public starting point**: `bang query dump <entry.bang>` → a sliced
  `moduleBodies[].exports[]` row.
- **Terminal observation**: use the row's stable `id` with `bang query body-artifact`; its `artifact`
  contains the versioned canonical `Comp` JSON value. The shared codec decodes it back to the exact
  canonical encoding, and `Bang.BodyArtifactConsumer` feeds that decoded term into the existing
  abstract-machine compiler/evaluator.
- **Adverse / recovery route**: malformed/version-mismatched/oversized encodings fail with `Except.error`;
  unsupported/no-body/unknown IDs return `ok:false`; a producer round-trip inconsistency refuses the
  requested artifact. The complete dump never embeds body bytes.
- **Downstream journey released**: a later validator/linker can consume concrete code and the already
  exposed relocation rows. It no longer needs to invent an IR serializer.

## Feeds the constraint

- **Binding constraint now**: the reachable slice is producer-checked but is neither independently
  type-validated nor complete with module initialization/import slots.
- **How this path feeds it**: make the body bytes and inverse real, then keep `linkReady=false` and
  `cacheKeySafe=false`. The next consumer must supply validation/link inputs before any reuse skip.

## Prospective systemic review

| concern | horizon + evidence | likelihood / impact / late cost | disposition now | reopen trigger |
|---|---|---|---|---|
| encoder-only format becomes write-only debt | no inverse exists today | realized / critical / high | **ship encoder and strict decoder together** | constructor set changes |
| permissive decoder accepts ambiguous artifacts | persistent inputs are eventually untrusted | high / critical / high | **exact version, tags, arities, scalar kinds, and trailing-input rejection** | format v2 |
| pathological input exhausts the consumer | decoder is a new input boundary | medium / high / medium | **bound UTF-8 byte length and recursive constructor depth** | representative artifacts approach bounds |
| encoding changes existing body identity | v2 digest is already published | medium / high / high | **keep digest algorithm and values unchanged; artifact is additive** | collision-safe address replaces probe digest |
| canonical labels detach from semantic rows | artifact and relocations share one producer observation | medium / critical / high | **encode the exact canonical term produced beside the existing rows** | artifact becomes standalone envelope |
| structural decoding is mistaken for typing validation | no decidable core validator/type certificate exists | high / critical / high | **say producer-checked, not independently validated; keep reuse/link flags false** | checked certificate or independent validator lands |
| pruned body is mistaken for full module initialization | strict initializer counterexample is committed | high / critical / high | **artifact remains export-body-only; no initializer/import slots** | ADR-0117 provenance gate opens |
| JSON payload growth dominates dumps | the first embedded design broke the 100-formula query journey at the shell argument limit | realized / high / high | **point-query one artifact by existing export ID; keep `dump` compact** | a bulk-transfer consumer with measured batching needs appears |

## Baseline, falsifiers, and evidence

- **Baseline**: `moduleBodyObservation` computes a canonical term only long enough to hash it, then
  discards it. No repository function reconstructs a `Comp` from bytes.
- **Smallest tracer bullet**: one pure and one effectful sliced export encode, decode, re-encode
  byte-identically, and feed the decoded term through the current backend with the same observation.
- **Malformed-input poles**: wrong format version, unknown constructor, wrong arity, invalid scalar,
  trailing JSON, depth exhaustion, and byte-limit overflow all reject.
- **Identity pole**: unrelated earlier effects preserve artifact bytes while runtime relocation moves;
  distinct semantic effect names may share canonical label 4 but retain distinct outer body digests/rows.
- **Transport falsifier**: embedding every artifact in the complete dump duplicates shared reachable
  syntax across wide exports and exceeded the shell argument-size boundary on the 100-formula workload.
  The published point query keeps that workload and the 61-example dump corpus green.
- **Assumptions / exclusions**: no cryptographic address, store, scheduler, cache hit, type certificate,
  standalone module environment, generic instantiation artifact, import/initializer slot, linker, DCE,
  reordering, or per-binding effect row lands here.

## Plan

1. [x] Fix the format, trust boundary, and explicit non-claims.
2. [x] Implement the exhaustive versioned `Comp` JSON encoder/decoder with resource bounds.
3. [x] Emit one canonical encoding on demand from the same body observation as digest and relocations.
4. [x] Consume decoded code through the existing backend and gate round-trip/adverse/equivalence poles.
5. [x] Regenerate public projections, run full convergence, publish, and hand validation/linking forward.

## Status

- [x] Started 2026-07-19
- [ ] In flight: canonical body artifact tracer
- [ ] Blockers: none
- [x] Completed 2026-07-19 at `0085f879`
- Convergence evidence: the full build passes **1454 jobs**; `tools/test-query.sh` passes **285/285**
  including on-demand, strict-round-trip, unrelated-effect, dump-absence, and unsupported-export poles;
  all **33/33** end-to-end batteries pass; live proof facts agree at **23 Spec headlines / 33 Audit
  reports**; `just fitness`, the exact-tree `just verify`, and the commit hook's independent fitness +
  verify rerun all pass with `CHANGELOG_STABLE_REF=13737e76`.
- Reopen / observe: `artifact` is intentionally structural and producer-checked only. Open a new path
  when a concrete consumer pulls independent type validation, collision-safe addressing, or explicit
  import/initializer link slots; do not reinterpret this artifact as cache or link authority meanwhile.

## Owner

- Agent / human: Codex
