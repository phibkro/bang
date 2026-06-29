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

## Amendment — Phase-2 restructure executed (2026-06-29)

The deferred physical move (Decision §4) is **done**. The tree is now green
(`lr_sound` `sorryAx` notwithstanding — the move preserves the exact axiom census),
so the seam-first deferral has been discharged. Three units, each gated by a
**byte-identical `#print axioms` census** (the ungameable proof the move changed no
proof).

### A. Dead-engine removal (#103)
`Bang/Model.lean` (the 4323-line typeless soundness-diagonal engine, route-β) + its 5
refute/probe witnesses (`LwscgLengthRefute`, `CohSubstRefute`, `LwscgOfTypedRefute`,
`ReturnEscapeRefute`, `WsCfgInterfaceProbe`) were a **closed dead island** — out of the
gated closure (ADR-0063 routed v1 soundness through typing-preservation, not the
diagonal). Removal left the census byte-identical → machine-checked proof they were
dead. Git preserves them; ADR-0061 (the retrospective record) cites the old path via
`tools/refs-allow.txt`.

### B. The rename slate (#108) — legibility by name
`Core→IR · Operational→Semantics · CalcVM→AbstractMachine · Syntax→Typing ·
Mult→Grade · Metatheory→Soundness · Compile→Wasm · Compat→BinaryLR`. Module/file
renames only. **The census-gated theorem NAMESPACES are frozen**: `Bang.CalcVM.*`
(4 headlines) and `Bang.Surface.*` keep their qualified names even though their
modules became `AbstractMachine`/`Frontend.Surface` — a module-name ⊥ namespace seam,
the only way to rename the module while keeping the census byte-identical.

### C. Tier folders + path-derived enforcement
Every module moved into its tier directory; module names `Bang.X → Bang.Tier.X`;
imports rewritten; **no namespace touched** (so the census holds). Two tiers were
ADDED beyond the original three:
- `Bang.Meta` — the binary-LR / relational proofs (`LR`, `BinaryLR`): proofs ABOUT
  the core that the gated kernel closure does NOT depend on.
- `Bang.Witness` — the build-gated regression/escape witnesses.
- `Bang.Reify` — the `CalcReify*` reification spike.
`tools/arch-check.sh` `layer_of` is now **PATH-DERIVED** (the tier is read from the
`Bang/<Tier>/` directory in the module path — GENERATE, not a hand-maintained map),
with a **rank model**: Core=0 (sink) · Frontend=Backend=1 (incomparable siblings) ·
Meta=Witness=Reify=2 (consumers) · Apex=3 (unrestricted). Forbidden = importing
strictly upward, plus the Frontend⊥Backend cross-edge.

### The Soundness→Core finding (an import the tiers REVEALED)
The first tier sketch put `Soundness` (the syntactic STD metatheory:
preservation/progress/type_safety + substitution) in `Meta`. The move revealed a
**`Core → Meta` edge**: the gated kernel closure
`Audit → Backend.AbstractMachine → Core.CapCoh → Core.Freshness → Soundness` DEPENDS
on it. The dependency graph therefore FORCES Soundness Core-foundational — it is not a
"proof about" that sits above the core, it is part of the core's own metatheory that
the live caps/coherence layer consumes. Resolved by tiering **Soundness into Core**;
`Meta` holds only the binary-LR. (Soundness imports only `Core.*`; no Core module
imports `LR`/`BinaryLR` → the V holds by construction, path-derived.)

### Encapsulation finding (the honest limit)
Deep-module ENCAPSULATION (hiding implementation behind a narrow public interface,
ADR-0026/0048 §Context) was **build-refuted for the proof spine**: the LR/metatheory
modules are mutually-recursive proof developments whose lemmas reference each other's
internals; a narrow public face strangles them. What the restructure DID buy is real
and sufficient: **reveal** (module headers + privatized internals, Phase-1), the
**verified/tested seam made structural** (the `Witness` tier + the `PropTest`
module-exception), and **tier legibility** (the V enforced by directory structure).
Encapsulation of the spine is not the win; the legible boundary is.
