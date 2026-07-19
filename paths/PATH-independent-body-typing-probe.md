# PATH-independent-body-typing-probe — can a body artifact earn its validation flag?

> Determine the smallest representation from which an external consumer can check the kernel typing
> judgment for canonical body bytes, without replaying or trusting the source elaborator.

## Seam

- **From checkpoint**: canonical body bytes have strict decoding and collision-resistant envelope
  integrity, but honestly report `independentlyTypeValidated=false`.
- **To checkpoint**: either freeze a representation-complete executable-validator tracer, or record the
  exact information erased before `Comp` that prevents one. Do not flip a trust flag during the probe.
- **Contract preserved**: artifact bytes/addressing, producer checking, runtime relocation, cache and
  link flags, frontend acceptance, kernel judgments, and backends remain unchanged.

## Layer

- [x] Kernel typing boundary  [x] Compiler artifact boundary  [ ] Surface  [x] Meta (probe/docs)

## Actor journey / observable outcome

- **Actor / need**: a build-tool author holding body bytes needs to distinguish “these bytes match their
  address” from “this decoded computation conforms to its claimed kernel interface.”
- **Public starting point**: `bang query body-artifact <export-id> <entry.bang>`.
- **Terminal observation**: the probe says exactly which additional type/signature/grade evidence a later
  validation route must carry, backed by kernel-checked witnesses rather than a schema sketch.
- **Adverse route**: a structurally valid body with the wrong claimed type must remain consumable only by
  structural APIs; no existing `false` flag may turn `true` from producer trust or source replay.
- **Downstream journey released**: a representation-complete certificate producer+validator tracer, if
  the production route remains smaller than a second elaborator.

## Feeds the constraint

- **Binding constraint now**: `ModuleBodyArtifactFact.independentlyTypeValidated=false` and
  `PATH-body-artifact-integrity` explicitly leave an executable-core checker open; `Bang/Core/Typing.lean`
  defines only the Prop-valued `HasVTy`/`HasCTy` judgments.
- **How this path feeds it**: determine which erased judgment witnesses must cross the artifact boundary
  before an executable consumer can check those rules without trusting the frontend.

## Kill-shot questions

1. Is `(Comp, claimed root type, effect signature)` sufficient to reconstruct all internal typing
   choices, or did lowering erase choices that must travel as an explicit certificate?
2. Are custom clauses, `fold`/`unfold`, and capability typing checkable from kernel-local evidence, or
   does any rule require unencodable elaborator state?
3. Does “independently type validated” include exact QTT grade vectors and effect rows? The default is
   **yes**: those are part of `HasVTy`/`HasCTy`, not optional decoration.

## Prospective systemic review

| concern | horizon + evidence | likelihood / impact / late cost | disposition during probe | reopen trigger |
|---|---|---|---|---|
| root type launders erased local choices into “validated” | ordinary discarded let; `BodyTypingProbe.lean` | high / critical / high | construct an ambiguity witness before schema work | a complete local certificate is identified |
| source checker replay is called independent validation | artifact consumer accepts external bytes | high / critical / high | validator input begins at decoded core bytes; source is not evidence | never |
| grades are silently scoped out | `HasVTy`/`HasCTy` index every derivation by grades | high / high / high | require exact kernel judgment evidence or keep the flag false | an explicitly weaker, separately named flag is justified |
| effect names/labels drift across contexts | canonical/runtime relocation already diverges under insertion | high / critical / high | identify the canonical signature rows the checker actually consumes | relocation envelope v2 |
| a checker is assumed sound because it is executable | current pure spike has examples, not reflection | medium / critical / high | tested-stratum wording; a `HasCTy` soundness proof is separate | proof consumer pulls it |
| typing is mistaken for cache/link safety | all three artifact trust flags are independently false | high / critical / high | keep `cacheKeySafe=false` and `linkReady=false` | their own contracts land |

## Non-goals

No linker, import graph, cache hit, DCE, persistence, semantic equivalence, source re-elaboration,
frontend behavior change, backend change, or trust-flag flip. This probe may add only a machine-checked
witness and its decision record.

## Baseline, falsifier, and evidence

- **Baseline / red observation**: structurally decoded bytes can reach unchanged backends while the
  artifact truthfully reports no independent type validation.
- **Smallest tracer bullet**: this probe does not flip the product route; it decides whether its proposed
  `(Comp, root type, signature)` input is sufficient before a public validator is promised.
- **Positive evidence**: direct Lean checking of `scratch/BodyTypingProbe.lean`; local premise inventory
  against `HasVTy`, `HasCTy`, and `HasClauses`.
- **Negative or recovery evidence**: the same body/root judgment has `Int` and `Unit` hidden-identity
  derivations, refuting unique recovery of erased local evidence.
- **Broader convergence gate**: `tools/check-paths.sh`, `just fitness`, and direct Lean checking.
- **Assumptions / exclusions**: feasibility of certificate checking does not yet prove certificate
  production is tracer-sized, nor establish validator soundness, cache safety, or link readiness.

## Plan

1. [x] Exhibit whether one claimed root type determines the erased local type choices.
2. [x] Inventory the custom-handler, recursive-type, capability, effect-row, and grade premises.
3. [x] Classify the minimal honest input: root claim, annotated core, or proof-relevant certificate.
4. [x] Freeze the next tracer or stop at the named representation wall; run focused/full doc gates.

## Kill-shot result

### Root claim + signature is insufficient

`scratch/BodyTypingProbe.lean` machine-checks one closed `Comp` at one root judgment in two concrete
ways, and in fact proves the judgment for **every** hidden value type `A`. The term binds an identity
thunk and discards it. Its bytes and root type are fixed, while the erased let-bound type can be
`U {} (Int -> Int)`, `U {} (Unit -> Unit)`, or infinitely many other types. The existing pure
`Bang.TypeCheck.checkC` already exposes the corresponding algorithmic fact: a `lam` is check-mode
only, while `letC` must synthesize its head. Therefore a root-type-only checker cannot recover the
information needed at exactly this ordinary let boundary; picking a guessed default would test one
derivation search heuristic, not validate the producer's claimed interface.

### No elaborator-only semantic premise blocks a certificate

The three hard rule families are locally checkable once their erased witnesses travel explicitly:

| kernel rule family | explicit evidence a validator needs | source of truth |
|---|---|---|
| `fold` / `unfold` | expected `mu A`, locally checked `unrollMu A`, exact value grade | `HasVTy.fold`, `HasCTy.unfold` |
| capability / perform | capability label/type, op argument/result types, claimed row membership, exact `q` and grade vectors | `HasVTy.vcap`, `HasCTy.perform`, finite `EffSig` |
| custom handler | parameter type, finite clause modes/op types, clause value judgments, body/result type, residual row, `qc`, exact grades, coverage and B-occ checks | `HasCTy.handleCustom`, `HasClauses` |

The universal-looking interface premises are finite checks only if the envelope carries the complete
operation inventory for each referenced canonical label. This is the first honest import-slot content:
canonical label, operation name/mode, argument type, and result type. Runtime labels remain relocation
inputs, not typing identity.

### Grade scope decision

Validation means the full concrete `HasVTy`/`HasCTy` judgment: exact QTT vectors, returner/argument
multiplicities, and effect rows. A type-only approximation would need a different name and flag. QTT is
finite, so local vector/scalar equations are executable checks; there is no reason to erase them at this
boundary.

### Representation verdict

The smallest honest input is a **proof-relevant typing certificate** aligned structurally with the
canonical `Comp`, plus canonical `VTy`/`CTy`, complete referenced effect signatures, and exact grades.
The validator checks every local rule and byte/tree alignment without consulting source or trusting the
certificate producer. This is tested-stratum evidence until a separate reflection theorem connects the
checker to `HasCTy`.

An annotated-core replacement would conflate executable code and evidence and force a v2 code codec.
Unbounded proof search would reconstruct evidence the producer already had and makes validation cost and
termination harder to state. A sidecar certificate preserves `bang-core-comp-json-v1`, can be
content-addressed with its interface, and can later be discarded after checking.

The remaining implementation risk is **certificate production**: today's surface inference returns only
the root `(CTy, row)` and lowering returns only `Comp`; neither retains a derivation tree. The next tracer
must first prove it can emit certificates for the lowered artifact corpus without a second trusted source
replay. Until that producer+validator journey exists, `independentlyTypeValidated` stays false.

## Status

- [x] Started 2026-07-19
- [ ] In flight: none — the representation finding is banked
- [ ] Blockers: none
- [x] Completed 2026-07-19
- Convergence evidence: `scratch/BodyTypingProbe.lean` checks directly; `tools/check-paths.sh` passes;
  Fable 5 independently audited the witness and conclusion **ACCEPT**.
- Retained failed gates / successors: root type + effect signature is insufficient; certificate
  production is not tracer-sized without a real consumer.
- Reopen / observe: reopen when an actual linker or external artifact consumer needs the flag, or when
  source-provenance work independently instruments the typed-lowering seam. Those consumers should share
  one evidence-preserving refactor rather than traverse ANF/monomorphization/knot lowering twice.

## Owner

- Agent / human: Codex, with read-only Fable 5 advisor
