# ADR-0004 · The canonical target is a calculated VM; Effect TS et al. are optional lowerings

- **Status:** Accepted
- **Date:** 2026-05-31
- **Related:** 0002 (the VM is calculated against the Lean reference), 0003 (this is *how* we own the runtime)

## Context

Given the decision to own the runtime (0003), what is the compilation target? Bahr–Hutton "calculating correct compilers" *derives* a `(compiler, machine)` pair from a semantics by equational reasoning, so the machine is correct-by-construction.

## Decision

The **canonical target is a VM calculated from the Lean `eval` semantics** (Bahr–Hutton). `Effect TS`, Koka-style C, and WasmFX become **optional K5 lowerings**, not the foundation.

## Rationale

- Calculation yields `(compile, Code, exec)` correct-by-construction; **the machine is an output of the derivation**, not hand-designed.
- You *cannot calculate* a transpiler to Effect TS: calculation needs the target as an output, and Effect TS is a fixed, external, unsound, unformalized language. Transpiler correctness there would be translation validation against an unformalized target — far worse effort/payoff.
- Lean compiles `exec` to C, so the calculated machine is a runnable owned runtime.
- Lowerings stay honest by differential testing against `exec` (invariant 1).

## Rejected alternatives

| option | why not |
|--------|---------|
| hand-design a VM, then verify a compiler against it | = CompCert mode: more work, none of the calculation's elegance; the machine should *fall out*, not be posited |
| Effect TS as canonical | can't calculate against it; unsound substrate (this is the demotion) |
| LLVM native | overkill; performance is second-class (invariant 7) |

## Consequences

- **STM is axiomatized as machine primitives, not derived** (consistent with it being the one privileged primitive). 
- **Multi-shot handlers are deferred** (frontier): the machine must reify continuations.
- Divergence handled via the partiality monad (Lean coinduction is the effortful spot — see 0002).
- The design doc's **kernel/library table is the VM's primitive boundary**: kernel column native, library column compiles to ordinary code.
- Calculation is **staged** — pure core → effects (swap the monad) → divergence → concurrency — each a calculated pass; composition gives end-to-end correctness.

## Revisit if

The calculation proves intractable for the **handler core** in Lean within budget → fall back to verify-after-the-fact (CompCert mode) for that one pass only, keeping the rest calculated. Do **not** silently drop the reference.
