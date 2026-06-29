# 0056 — The capability-escape soundness gap (the ⊥-row gate does NOT rule out escape)

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: ADR-0054 asserted "first-class-thunk escape is ruled out by the EXISTING `LWT` non-escape gate (`preservation_returnEscape`), NOT by second-class thunks." That assumption is **machine-checked FALSE** (inc-5, B2): a capability can escape its handler and get STUCK even in a well-typed-at-⊥, `VcapFree` program, because **typing is by LABEL (ℓ) but dispatch is by IDENTITY (n)** — the ⊥-row gate is label-based and cannot see the identity-escape. Witness `progB` (the `DiagonalFalsifyProbe` `diagonal_is_false`, axiom-clean): `HasConfigTy (0,[],progB) ⊥ (F 1 unit)` ∧ `VcapFree progB` ∧ `¬ NonEscape (0,[],progB)` ∧ `Source.eval progB = .stuck`. So the **inc-5 diagonal** (`HasConfigTy ⊥ ∧ VcapFree → NonEscape`) — the source-level soundness payoff — is FALSE, and **the language is unsound as it stands** (a well-typed source program gets stuck). This is the WC keystone-2c, only HALF-solved: ADR-0055 global-fresh fixed the *collision* (wrong-handler resolution), but the *escape* (cap → nothing → stuck) remains. The fix requires a real non-escape discipline. **DECISION: explore the design space first** (operator ruling, 2026-06-26) before committing — same approach as the ADR-0053→0054 pivot.

- **Refines**: 0054, 0055
- **Depends-on**: 0054, 0055, 0030, 0023
- **See-also**: 0026, 0016

## Status

Accepted (2026-06-26): the GAP is recorded; the FIX is **pending a design-space exploration** (operator
ruling). inc-5's diagonal + A2's value-cap-scopedness arms are HELD until the fix lands. `type_safety` (stated
over `HasConfig = HasConfigTy ∧ NonEscape`) is NOT violated — it's vacuous for `progB` (NonEscape fails) — but
the *source-level* claim "well-typed source → safe" requires the diagonal, which is false. The non-escape parts
of inc-5 (the LR re-key, `run_rename`, `run_plug`, `krelS_staticSplit_decomp` re-derivation) are unaffected and
proceed.

## Context

The same failure shape as ADR-0053: an *assumed* soundness rationale, build-refuted.
- ADR-0053 (absolute caps): assumed "a cap-carrying thunk can't escape; migration only inserts above" → the
  insert-below witness refuted it.
- ADR-0054 (identity caps): assumed "escape ruled out by the LWT gate, not second-class thunks" → `progB`
  (re-handled escape) refutes it.

`progB = letC (handle (state 1) (ret (thunk (perform (vvar 0) "get" unit)))) (handle (state 1) (force (vvar 1)))`
— the inner handler is minted then POPPED; its `perform`-carrying thunk escapes in the return value and is
forced under a FRESH same-label handler. Both effects are label-1, so the whole types at ⊥. But the escaped cap
names the popped handler BY IDENTITY (`vcap 0`), and under global-fresh the fresh handler has a different id
(`1`), so `splitAtId [handleF 1] 0 = none` → stuck. The ⊥-row discipline only sees that ℓ=1 is discharged
*somewhere*; it cannot see that the cap names a dead handler.

This is the long-flagged WC keystone-2c (`scratch/IdentityCollisionProbe.lean`; `Bang/Witness/CapEscapeWitness.lean`
calls `progB` "the known type-directed sorry"). It was deferred under the (now-refuted) belief the gate handled it.

## Decision

**Explore the non-escape design space before committing** (operator ruling). The candidate disciplines — to be
surveyed (literature + bang-kernel mapping) and compared on cost / what they change / whether they close the
diagonal — are:

1. **Surface-enforced (second-class caps at the surface).** The inc-7 elaborator forbids returning a live-cap
   thunk past its handler; kernel `HasCTy` stays permissive. Safety becomes "well-ELABORATED source → safe"
   (the stratification model: permissive kernel, verified surface restriction). Cheapest; localizes to inc-7.
   Reverses ADR-0054's "not by second-class thunks"; the kernel diagonal stays false.
2. **Kernel coeffect/region discipline.** Strengthen `HasCTy` so a `Cap ℓ` is untypeable in an escaping return
   position → the diagonal becomes TRUE at the kernel (well-typed → NonEscape). Correctness-by-construction,
   kernel-sound. Biggest: touches the core typing judgment + everything proven over it (the LR, the STD block).
3. **(open) other** — e.g. Effekt System Ξ second-class capabilities, Frank/Koka scoped-handler disciplines,
   a `▷`/region-indexed `Cap`. The exploration surveys these.

## Consequences

- inc-5 SPLITS: the non-escape-INDEPENDENT work (LR re-key, `run_rename`/`run_plug` integration, the
  `splitAtId`-keyed `krelS_staticSplit_decomp` re-derivation) PROCEEDS; the diagonal + the value-cap-scopedness
  arms are HELD (named-sorry, "pending escape-discipline decision") until the fix lands.
- The chosen fix becomes a follow-on ADR (0057+), and likely shapes inc-6/inc-7 (the surface option lands in
  inc-7; the kernel option re-touches the type system + the LR).
- The witness `progB` (DiagonalFalsifyProbe + IdentityCollisionProbe + CapEscapeWitness) is the regression
  oracle for whichever fix lands — the fix must make `progB` untypeable/un-elaboratable, then the diagonal closes.

## Alternatives considered (rejected)

- **Wire the diagonal in as-stated** — UNSOUND (it's machine-checked false); would propagate a false soundness
  claim into Audit/Spec. Rejected (B2 correctly left it documented-FALSE, not closed).
- **Weaken NonEscape so `progB` satisfies it** — `progB` genuinely escapes (resolves to nothing); a NonEscape
  weak enough to admit it is the ADR-0055 too-weak failure again. The fix belongs in TYPING/SURFACE (make the
  escaping program unrepresentable), not in NonEscape.
