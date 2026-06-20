# ADR-0016 — Two-hop architecture: graded-CBPV reference, CalcVM as executable spec, WasmFX as verified compiler target

## Status
Accepted. Supersedes ADRs 0003 (own-the-runtime) and 0004 (calculated-VM-canonical),
which it subsumes. Folds in the renumbered effect-row-algebra ADR
(originally drafted under bang-lang-wasmfx/).

## Context
Through K0–K3 the project established a calculated-VM-as-canonical-target stance
(ADR-0004) and rejected transpilation to Effect TS (ADR-0003). With eight proven
machines and CalcReify under bisimulation, the operational reference is mature.
The third design revision (bang-lang-wasmfx/) raises the substrate to graded
CBPV (Torczon et al. OOPSLA 2024), introduces logical-relations-based contextual
equivalence (Biernacki et al. POPL 2018), and commits to WasmFX as a concrete
compilation target via verified forward simulation (Benton-Hur / CakeML model).

The question is whether the calculated VM survives or is replaced.

## Decision
The calculated VM is REFRAMED, not replaced. The architecture is two-hop:

    Source AST
        │
        ▼  (graded-CBPV reference semantics)
    Source.eval                  ← the SPECIFICATION (denotational)
        │
        ▼  (Bahr-Hutton calculation; exec ∘ compile ≡ eval)
    CalcVM                       ← the EXECUTABLE INTERPRETER
        │                          (canonical operational meaning)
        ▼  (Benton-Hur LR; compile_forward_sim)
    WasmFX module                ← the OPTIMIZED COMPILER OUTPUT
        │
        ▼  (wasm3 / wasmfx-runtime execution)
    Observed values

This is the CakeML / Benton-Hur verified-compilation model, with the front half
replaced by Bahr-Hutton calculation rather than hand-designed IR.

## Why this model
1. The CalcVM is runnable today; users running bang-lang programs run the spec,
   not an approximation.
2. The CalcVM constitutes constructive evidence for the front half of compiler
   correctness; the LR starts from a machine, not from raw syntax.
3. CalcReify's resume-frames are structurally adjacent to WasmFX typed
   continuations; the compiler is closer to syntactic than semantic.
4. Each hop has its own native proof methodology (calculation vs LR); neither
   is overloaded.
5. Diff-testing applies independently to each hop, sharpening fault localization.

## What it commits to
- WasmFX is the primary compilation target. wasm3 is the interpreter runtime
  used for testing and bootstrapping; wasmfx-aware runtimes are the production
  target.
- Effect TS is NOT a target (formerly ADR-0003).
- The CalcVM is the canonical *operational meaning* of a bang-lang program;
  optimizations in the WasmFX backend must preserve contextual equivalence
  (compile_forward_sim).
- Graded CBPV is the source substrate (replaces ad-hoc CBN/CBV variants).
- The effect-row algebra remains Finset Label, extended with lacks-constrained
  row variables to enforce no_accidental_handling.

## Consequences
- ADR-0003 and ADR-0004 are subsumed and DELETED (not just superseded);
  this ADR is the new statement.
- ADRs 0010-0014 (per-machine calculations) become historical execution
  records; collapsed into a single retrospective in a follow-up commit.
- CalcReifySim bisimulation effort is PAUSED; the LR provides stronger
  contextual equivalence and is what compile_forward_sim consumes.
- The project gains a second proof-methodology spine (LR alongside
  calculation); team capacity must accommodate both.
- The K5 "optional lowerings" framing is dropped; lowering is no longer
  optional, it's the contribution.

## Rejected alternatives
- (A) WasmFX as canonical, calculated VM discarded.
  Rejected: throws K3 work that already provides front-half correctness;
  the semantic gap from source to WasmFX is larger than source→CalcVM,
  making the LR harder.
- (B) Calculated VM canonical, WasmFX as one of many K5 lowerings.
  Rejected: undersells the WasmFX commitment, leaves wasm-as-target
  perpetually deferred; OOPSLA-grade contribution requires a target.
- (C) Keep two parallel architectures and choose later.
  Rejected: bifurcates the proof effort; future contributors face
  ambiguity about which spec is canonical.

## Revisit if
- group_recovers fails to hold for the chosen ≈ — may require revising the
  observation predicate at the WasmFX seam.
- WasmFX proposal stalls or is superseded by a different stack-switching
  primitive; the architecture is target-agnostic but the proof bindings
  are not.
- An interpreter-first user community develops that needs CalcVM as the
  shipped artifact, not just the spec.
