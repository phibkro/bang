# bang-lang architecture — the 30-second orientation

> Top-level map of how a bang program goes from text to execution, and where the type
> system sits. This is the ORIENTATION tier — it links out, it does not restate. For depth:
> `docs/notes/compiler-overview.md` (the comprehensive, citation-grounded pipeline + the Lexa
> comparison) and `docs/architecture/core-overview.md` (the module/coupling map). Code is the
> source of truth; ADRs are the why.

## The pipeline

```
  SURFACE              CORE  =  the graded-CBPV IR              CalcVM             WasmFX
  ┌──────────┐ parse   ┌────────────────────────────┐ Bahr-   ┌──────────┐ ann.  ┌──────────┐
  │ String   │────────▶│ Comp / Val   (the AST)      │ Hutton  │ Code     │ fwd-  │ Wasm     │
  │ Surf AST │ lower   │ ── THE TYPE SYSTEM lives here│ calc.   │ (calc'd  │ sim.  │ Instr /  │
  │          │────────▶│   HasVTy / HasCTy            │────────▶│  machine)│──────▶│ Module   │
  └──────────┘         │   rows = Finset Label        │ inv #4  │ types    │ ADR-  │ host wasm │
   Surface.lean        │   grades = GradeVec Mult     │         │ ERASED   │ 0035  │ validates │
   (untyped today)     │ reference exec: Source.step  │ CalcVM  │          │       │           │
                       └────────────────────────────┘ .lean   └──────────┘       └──────────┘
   ◀──────── VERIFIED CORE (proof) ────────▶│◀──── two verified compiler hops ────▶│◀ host ▶
```

## Five facts that orient everything

1. **The VM is *calculated*, not lowered-to.** The CalcVM is *derived from* the Core semantics by
   Bahr–Hutton equational calculation, so VM-execution ≡ IR-semantics **by construction** (invariant #4).
   The arrows are verified equivalences, not best-effort translations. (ADR-0016)

2. **The type system lives at Core — and nowhere else.** `HasVTy`/`HasCTy` (`Bang/Core/Typing.lean`), intrinsic
   and resource-enforcing. It carries three things: the CBPV value/computation split (`VTy`/`CTy`,
   `Bang/Core/IR.lean`), the **effect row** (`EffRow = Finset Label`, a set — idempotent join, invariant #2),
   and the **grades** (`GradeVec Mult`, Torczon multiplicities). The row is a function's *paradigm*.

3. **Types erase below Core.** The CalcVM machine is grade-blind (`HasConfigTy` ignores the config counter;
   the machine never branches on a grade). Types do their work at the Core check and vanish; Wasm then
   validates with its own type system. One type system, at the IR.

4. **Two hops, two methods, no optimizer** (invariant #7: performance is second-class):
   - Core → CalcVM: **Bahr–Hutton calculation** (`Bang/Backend/AbstractMachine.lean`).
   - CalcVM → WasmFX: **annotated forward simulation** — `compile_forward_sim` (`Bang/Backend/Wasm.lean`,
     ADR-0035). NOT the biorthogonal/Benton–Hur LR, which proves ◊4 *contextual equivalence* (a separate
     theorem). "Passes" here means verification stages, not optimizer passes.

5. **The stratification seam IS the effect row.** verified core + tested superset, type-visible seam
   (ADR-0026): the total fragment (`⊥`-row, terminating, proved) vs the `Div` fragment (fuel-bounded,
   Turing-complete, differential-tested). `Div` in the row = you have *descended* from the proved-total
   core into the tested superset; `Source.eval`'s fuel parameter is that descent made operational.

## Current vs aspired

| | what |
|---|---|
| **LANDED** | Core kernel + type system · reference CK-machine (`Source.eval`, `Bang/Core/Semantics.lean`) · CalcVM CBPV-spine calculation · Compile/WasmFX statements · untyped Surface tracer (`Bang/Frontend/Surface.lean`) |
| **IN-FLIGHT** | inc-5 soundness diagonal (`type_safety`) — the keystone |
| **RE-KEY** | inc-6 full CalcVM re-key · inc-7 typed Surface elaborator (unify-infer into Core; soundness proved, MGU differential-tested) |
| **FRONTIER** | `Bang/Reify/CalcReify.lean` — multi-shot / non-tail continuation reification (post-v1) |

Today's runtime is `Source.eval` (the fuel-bounded CK interpreter); the IR→VM→wasm chain is the *verified*
path being re-keyed onto the current kernel hop by hop.

## See also

- `docs/notes/compiler-overview.md` — the comprehensive pipeline + the Lexa comparison (PROVEN/IN-FLIGHT tags)
- `docs/architecture/core-overview.md` — the module/coupling map
- `docs/decisions/0016-two-hop-architecture-calcvm-and-wasmfx.md` — the two-hop architecture
- `docs/decisions/0035-lr-for-equivalence-simulation-for-compilation.md` — why simulation (not LR) for compilation
- `CLAUDE.md` — invariants, glossary, architecture-in-force (the always-loaded core)
