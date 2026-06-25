# 0048 — The library tiering: Frontend / Core / Backend, a dependency V with an apex

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: Make the architectural seams VISIBLE in the module structure. The `Bang` library tiers into three namespaces — `Bang.Frontend` (the human/agent edge: surface, elaborator, the writable `NamedCore` IR, tooling; tested-not-verified), `Bang.Core` (semantics + IR + proofs; the single source of truth), `Bang.Backend` (the machine edge: CalcVM + the verified WASM compiler) — plus an APEX (`Spec`/`Audit`/`Distribution`) that aggregates across all three. The dependency rule is a **V, not a line**: data FLOWS Frontend → Core → Backend (text → IR → WASM), but DEPENDENCIES point inward at Core (`Frontend → Core ← Backend`); Core imports nothing outward. A fitness function (`tools/arch-check.sh`) enforces this as a TESTED rung — direction drift is a build failure. Rollout is **seam-first**: `Bang.Frontend` is established now (`NamedCore`); the physical move of the existing flat modules is DEFERRED until they are green again (the ADR-0045 pivot left them build-red; moving red files is unverifiable churn), and the Core-internal sweep waits for `lr_sound`.
- **Depends-on**: 0046, 0047, 0026, 0016

## Context

ADR-0046/0047 settled the SURFACE architecture (two syntaxes, one core; sugar → named-explicit core → kernel). But the `Bang` library stayed FLAT — every module in one namespace — so the verified-core / tested-superset / machine-backend seams were conceptual, not structural. The contract between deep modules IS their public interface; if the tiers are invisible in the module structure, the interface is a convention, not a boundary.

The operator's framing: a tiered architecture with a unidirectional dependency, in the spirit of functional-core / imperative-shell (FCIS) — push I/O to the edges, keep a deep pure core. The instinct is right; the labels needed correcting against the actual import graph.

## Decision

1. **Three tiers + an apex.**
   - `Bang.Frontend` — the human/agent-facing edge: the surface sugar, the elaborator, the writable `NamedCore` S-expression IR (ADR-0046 ①), and the future tooling surface (LSP/linters/formatters, ADR-0047). Tested-not-verified.
   - `Bang.Core` — semantics, the IR, and the proofs (kernel · typing · operational · metatheory · LR). The single source of truth; depends on nothing outward.
   - `Bang.Backend` — the machine edge: the calculated VM (CalcVM) and the verified source→WASM compiler. Verified.
   - **Apex** (`Spec`, `Audit`, `Distribution`) — the frozen theorem manifest + axiom gate + research appendix. Aggregates across all tiers; not part of the V.

2. **The dependency rule is a V, not a line.** Data flows Frontend → Core → Backend (the compiler pipeline). DEPENDENCIES are the dual: `Frontend → Core ← Backend`. Core is the sink. This inward-pointing V (dependency inversion) is what makes Core a reusable, self-contained root — and what makes the writable IR a clean plugin surface (a tool consuming `NamedCore` depends on Core alone).

3. **Enforced as a fitness function** (`tools/arch-check.sh`, in the `just fitness` / `just audit` block): Core must not import Frontend or Backend; Frontend and Backend must not import each other; the apex is unrestricted. Pure import-grep (no Lean build), so it gates even on a mid-pivot-red tree. Layer assignment is a declared map now → path-derived (`Bang/Frontend/*`, `Bang/Backend/*`) once the moves land — a CONVENTION rung climbing to GENERATE.

4. **Seam-first / incremental rollout.** `Bang.Frontend` is established now (`NamedCore`, gated green in isolation). The `git mv` of the existing flat modules is DEFERRED: the pivot left `Surface`/`CalcVM`/`Compile`/`Compat` build-red, and moving red files is unverifiable churn (it violates "gate the committed content"). Each module moves when it is green again; the Core-internal sweep waits for `sorryAx`-zero `lr_sound`.

## Rejected alternatives

- **FCIS taken literally (functional core / imperative shell).** The right DEPENDENCY rule (edges depend on the core; the core on nothing), but the wrong SHAPE: the edges here are not thin I/O orchestration — the Backend is a deep, *verified* compiler (the biggest tier). "Imperative shell" mislabels it. The honest shape is the compiler triad frontend/IR/backend; FCIS supplies the invariant, not the name.
- **`Bang.Machine` for the backend.** "Machine" is overloaded in this repo — the CK step in `Operational` and the CalcVM (invariant #4: "the machine is an output of the calculation") are both "the machine," and both are Core/semantics, not the WASM backend. `Backend` is unambiguous.
- **The dependency as a line `Frontend → Core → Backend`.** That would make Core import Backend, destroying Core as the self-contained SSoT (and the proofs would depend on the compiler). The line is the DATA FLOW; the dependency is a V.
- **Full restructure now.** Rewrites the live LR battlefield (`Compat`/`LR`/`Spec`) mid-pivot — high collision risk, and unverifiable on the red tree. Seam-first defers the churn to where it can be gated.
- **Convention only (no enforcement).** The seam tangles silently as modules grow; the project's ethos is drift-as-build-failure. The fitness function is the tested rung.

## Consequences

- `Bang.Frontend.NamedCore` is the first resident of the new structure: the writable IR, depending on Core alone — the concrete plugin/LSP/linter surface (ADR-0047), and the agent-precision mode (ADR-0046) made real.
- `Spec`/`Audit` are correctly seen as the apex (manifest + gate), not Core — they import across tiers; the fitness function exempts them.
- The fitness function runs pre-build, so the architectural contract is enforced continuously, independent of the LR pivot's red tree.
- A new module cannot be added without classifying its tier (an unclassified module fails `arch-check`) — the layer map stays complete by construction.
