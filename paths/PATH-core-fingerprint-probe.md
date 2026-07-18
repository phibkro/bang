# PATH-core-fingerprint-probe — observe the result firewall before building its cache

> Reuse one structural fold over the production elaborated `Comp`, expose its honest whole-program
> scope, and falsify canonicality/discrimination claims without treating 64 bits as a cache key.

## Seam

- **From checkpoint**: `PATH-module-invalidation-measurement` showed that the resolver DAG prunes
  independent leaves but propagates every upstream edit regardless of semantic result.
- **To checkpoint**: `bang query dump` carries an optional, versioned resolved-program core
  fingerprint whose invariance, discrimination, unsafe-key status, and failure route are exact.
- **Contract preserved**: the query runs `checkAndLowerProg`, the same typed lowering path as `run`;
  no second elaborator, module resolver, persistent store, scheduler, or cache-hit path is introduced.

## Layer

- [x] Kernel utility  [x] Compiler query  [ ] Surface language  [x] Meta (tests/docs)

## Actor journey / observable outcome

- **Actor / need**: a build-tool author needs to know whether the chosen result boundary suppresses
  noise-only invalidation before committing to cache machinery.
- **Public starting point**: `bang query dump <file.bang>`.
- **Terminal observation**: the `coreFingerprint` fact names `scope=resolved-program`, the versioned
  algorithm, a 16-hex digest, and `cacheKeySafe=false`.
- **Adverse / recovery route**: an ill-typed program reports `coreFingerprint:null` while retaining
  dump's declaration/reference diagnostics; the caller fixes the subject rather than hashing failure.
- **Downstream journey released**: a module-result/interface design can now start from the observed
  fact that whole-program elaboration has no intermediate per-module result for the DAG to firewall.

## Feeds the constraint

- **Binding constraint now**: topology is module-granular, but the only elaborated result is one flat
  whole-program `Comp`; collision-resistant hashing alone cannot bridge that granularity mismatch.
- **How this path feeds it**: demonstrate canonicality at the existing boundary, then make its scope
  and safety limits machine-readable so follow-up design cannot quietly assume separate compilation.

## Prospective systemic review

| concern | horizon + evidence | likelihood / impact / late cost | disposition now | reopen trigger |
|---|---|---|---|---|
| duplicate hash implementations drift | first compiler consumer; Q43 already had a fold | high / high / medium | **centralize** in `Bang.CoreFingerprint` | a second encoding consumer appears |
| scalar encoding creates systematic collisions | first adversarial review found all negative magnitudes collapsed | realized / high / low | **fix and retain falsifiers** for negative `Int` and large `Nat` | scalar alphabet changes |
| 64-bit equality is treated as cache correctness | first public fingerprint field | high / critical / high | **emit `cacheKeySafe:false`** and forbid persistent-hit claims | collision-resistant, versioned key is gated |
| whole-program digest is presented as module incrementality | current modules merge before elaboration | high / high / high | **name scope `resolved-program`** | a real per-module artifact seam lands |
| query hides invalid subjects behind a digest | malformed/type-error route | medium / high / low | **return null** from typed-lowering failure, preserve other facts | result/error schema is redesigned |
| hashing every dump creates premature performance work | no representative query latency measurement | low / medium / low | **accept one production lowering in the tracer**, make no latency claim | measured query use crosses a named budget |

## Baseline, falsifier, and evidence

- **Baseline / red observation**: ProofExport's private v1 fold mapped `vint (-1)` and `vint (-2)` to
  the same child fingerprint because `Int.toNat` erased negative magnitude.
- **Smallest tracer bullet**: one-declaration programs differing only by layout/comment, binder name,
  or a negative integer literal, observed through the compiled query CLI.
- **Positive evidence**: formatting/comment and alpha variants have equal digests; `-1` versus `-2`
  differs; the field's scope/algorithm/safety metadata is exact.
- **Negative or recovery evidence**: invalid typed input produces null; kernel guards reject the old
  negative-`Int` collapse and a pre-truncated `Nat` collision at `2^64`.
- **Broader convergence gate**: focused query battery, all-module build/audit, documentation and
  architecture/proof facts, `just fitness`, and `just verify`.
- **Assumptions / exclusions**: fingerprint inequality witnesses these tracer edits only; equality is
  not a proof of `Comp` equality. No collision-resistance, cross-version portability, per-module
  artifact, cache hit, store, scheduler, separate compilation, or latency/speedup claim.

## Plan

1. [x] Audit elaborated-core renderers/hashes and find the existing ProofExport fold.
2. [x] Centralize/version the fold and repair deterministic scalar collisions.
3. [x] Expose one optional resolved-program fact through the production query path.
4. [x] Gate formatting, alpha, semantic, invalid-subject, and safety-metadata outcomes end to end.
5. [x] Run full convergence, record the module-boundary decision, and publish.

## Status

- [x] Started 2026-07-18
- [ ] In flight: none; successor is the module-result/interface boundary probe
- [ ] Blockers: none
- [x] Completed 2026-07-18
- Focused evidence: `tools/test-query.sh` — **135 passed, 0 failed** in the standard dev shell.
- Convergence evidence: `just verify` — **31/31 batteries passed**, including **63/63** module
  checks; `just fitness` and the exact-tree provenance checks passed.
- Decision: elaborated `Comp` is the evidenced semantic boundary, but the current artifact is one
  resolved-program result. Design the module-result/interface seam before cryptographic storage.
- Reopen / observe: set `cacheKeySafe:true` only when collision resistance, compiler/kernel version
  domains, and exact artifact verification make an unchecked persistent hit sound.

## Owner

- Agent / human: Codex
