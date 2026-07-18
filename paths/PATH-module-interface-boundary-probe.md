# PATH-module-interface-boundary-probe — separate the interface firewall from the missing code artifact

> Preserve resolver-owned exports, project their checked public contract, and retain the falsifiers
> that prevent an interface digest from masquerading as separate compilation.

## Seam

- **From checkpoint**: `PATH-core-fingerprint-probe` established one canonical resolved-program
  implementation result but found no per-module elaborated artifact.
- **To checkpoint**: `bang query dump` distinguishes checked module interfaces from the whole-program
  core and names the architectural conditions still blocking an independent module artifact.
- **Contract preserved**: ADR-0093's modules still elaborate away into the flat kernel; the tracer
  reuses resolver provenance and existing checked declaration facts rather than adding a second checker.

## Layer

- [ ] Kernel  [x] Compiler query  [ ] Surface language  [x] Meta (tests/docs)

## Actor journey / observable outcome

- **Actor / need**: a build-tool author needs to distinguish implementation invalidation from public
  type/shape invalidation without assuming separately compiled module bodies exist.
- **Public starting point**: `bang query dump <file.bang>`.
- **Terminal observation**: `moduleInterfaces` groups body-free checked exports by logical module and
  reports versioned digests with `cacheKeySafe=false` and `separateCompilationReady=false`.
- **Adverse / recovery route**: invalid typed input reports `moduleInterfaces:null`; a resolver/fact
  mismatch also refuses the projection rather than emitting a partial interface.
- **Downstream journey released**: stable cross-module identities and a real module artifact/link seam
  can now target demonstrated coupling rather than starting with a cache implementation.

## Feeds the constraint

- **Binding constraint now**: BANG's public module DAG is file-granular, while elaboration produces a
  global environment and one lexical `Comp`; the core probe documented this granularity mismatch.
- **How this path feeds it**: isolate the useful public-contract boundary, then retain global-label and
  flat-body counterexamples that identify what must change before an artifact can cross it.

## Prospective systemic review

| concern | horizon + evidence | likelihood / impact / late cost | disposition now | reopen trigger |
|---|---|---|---|---|
| interface is mistaken for compiled code | first build-tool consumer; bodies are absent | high / critical / high | **emit `separateCompilationReady:false`** | an independently lowerable body + link contract lands |
| implementation edits are ignored for execution | body-only tracer moves core but not interface | high / critical / medium | **retain core and interface as distinct facts** | artifact validation subsumes the core observation |
| global labels cause false cross-module invalidation | earlier unrelated effect moves `Cap 4` to `Cap 5` | realized / high / high | **retain the negative pole; do not normalize it away** | effect/type identities become stable across module order |
| private implementation leaks into the contract | private-body tracer and resolver `pubNames` | medium / high / medium | **project only public non-`impl` declarations; omit bodies** | export semantics change |
| 64-bit digest becomes an unchecked key | inherited core-fingerprint risk | high / critical / high | **emit `cacheKeySafe:false`** | collision-resistant version domains + artifact verification land |
| invalid programs receive plausible interfaces | checked lowering may fail | medium / high / low | **return null and preserve other dump diagnostics** | typed error/interface schema is redesigned |

## Baseline, falsifier, and evidence

- **Baseline / red observation**: resolver exports were discarded after merge, so the query could show
  module ownership and all declarations but not each module's checked public boundary.
- **Smallest tracer bullet**: one imported `Lib` with a private helper and public value, varied across
  public-body, private-body, and public-signature edits through the compiled CLI.
- **Positive evidence**: body/private variants retain the exact `Lib` interface digest while changing
  the resolved core; a signature change moves both. Facts contain checked types/shapes but no bodies.
- **Negative or recovery evidence**: inserting an unrelated earlier user effect changes an unchanged
  exported capability type from `Cap 4` to `Cap 5` and moves its interface digest; invalid input is null.
- **Broader convergence gate**: focused query battery, all-module build/audit, generated reference and
  tool index, architecture/proof facts, `just fitness`, and `just verify`.
- **Assumptions / exclusions**: the digest is a change detector, not proof of interface equality. No
  stable type identity, separately compiled body, linker, cryptographic key, store, scheduler, cache
  hit, compile-time measurement, or speedup is claimed.

## Plan

1. [x] Audit resolver merge, type environment, top-level lowering, and effect-label allocation.
2. [x] Preserve exact public-export provenance through the resolver's completed walk.
3. [x] Project checked body-free interface facts and a versioned experimental digest.
4. [x] Gate implementation/signature discrimination, invalid input, and global-label coupling end to end.
5. [x] Run full convergence, record the Q34 input, and publish.

## Status

- [x] Started 2026-07-18
- [ ] In flight: none; successor is stable cross-module identities and the code-artifact seam
- [ ] Blockers: none
- [x] Completed 2026-07-18
- Focused evidence: `tools/test-query.sh` — **153 passed, 0 failed** in the standard dev shell.
- Retained failed gates / successors: global effect-label allocation and the flat top-level body are
  deliberate falsifiers. `PATH-stable-interface-effect-rendering` subsequently repaired the checked
  presentation leak while preserving this original failed observation here; runtime labels and the flat
  code artifact remain successor constraints.
- Convergence evidence: `just verify` completed the 1452-job build and **31/31 batteries** before its
  stale proof-source projection refused; regeneration plus exact-tree audit/fitness then passed.
- Reopen / observe: set `separateCompilationReady:true` only after an unchanged dependency interface
  can be consumed without whole-program elaboration and an independently validated code artifact links.

## Owner

- Agent / human: Codex
