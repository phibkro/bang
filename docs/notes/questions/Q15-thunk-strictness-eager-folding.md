---
type: design-question
title: "Thunk strictness: uniform laziness vs demand-driven eager folding"
description: "uniform-lazy semantics + an effect-row-gated fold pass (the evaluation-stage axis)"
status: open
area: surface
ties: ["ADR-0005", "ADR-0006", "ADR-0007"]
see-also: []
---
**Question**: should the surface/compiler evaluate pure closed expressions (e.g. `4+2`) eagerly
("declare/resolve thunks upfront") and suspend only genuinely-deferred ones (`4+x`, or anything
effectful), or keep the kernel semantics **uniformly lazy** (everything is a thunk; `force` is the
only observation, ADR-0007) and treat eager evaluation purely as a *compiler optimization*?

**Why it matters**: it is the surface manifestation of the §5 evaluation-stage axis (when/where a
thunk is forced). Get the boundary wrong and you either bloat every program with thunk allocations
(naive uniform-lazy) or perform effects at the wrong stage (naive eager — unsound).

**Detail**: the discriminant for "safe to fold now" is NOT "has a free variable" — it is **pure
(`⊥` effect row) AND closed**:
- `4 + 2`       `⊥`, closed         → safe to fold at compile-time (`$comptime`)
- `4 + x`       `⊥`, x unbound       → residual; fold once x is known (partial evaluation)
- `print(); 2`  row ⊇ `{IO}`         → MUST NOT fold early — folding performs the effect
The **effect row is the license to fold** (constraints-are-generative). A thunk in THIS kernel is the
minimal `vthunk : Comp → Val`; the richer "scoped env + deps + cached return" structure is a
**reactive cell** (ADR-0005/0006, rung 4) — an enrichment built *over* the minimal thunk, not the
thunk itself. Don't enrich the kernel thunk (collapses the moat / the five-primitive invariant).

**Options**: (1) **uniform-lazy semantics + an effect-row-gated fold/eager pass in the compiler**
*(recommended)* — one thunk concept; folding is an optimization that must preserve observable
behavior (invariant #7); (2) two syntactic thunk kinds (eager/lazy) at the surface — a second
concept, rejected unless (1) proves insufficient; (3) binding-time analysis as a surface-visible
stage annotation (`$comptime`/`$runtime`, §5) — likely the eventual UX, *layered on* (1).

**Prior art / framing** (the established names for option-1's "fold pass", for the ◊5 compiler
session): the loop "fold what's static, iterate to fixpoint, emit the residual" is **partial
evaluation driven by binding-time analysis** (Jones/Gomard/Sestoft 1993); the fold step is
**constant folding** enabled by **constant propagation** (a forward dataflow analysis); "safe to
force eagerly in a lazy language" is **strictness analysis** (Mycroft 1980); the fixpoint is the
least fixed point of a monotone map over a lattice — the shape shared by dataflow analysis and its
superframe **abstract interpretation** (Cousot² 1977). bang's edge: facts (1) purity and (2) usage
come FREE from the effect row + QTT grade (the type IS a precomputed static analysis); only
(3) constant-ness needs the dataflow pass. The static/dynamic partition = the compile-/run-time
stage assignment (Futamura), which is the §5 axis — bang layers MetaML-style explicit `$comptime`
staging (option 3) on top of the inferred default. Compiler ARCHITECTURE for hanging these passes:
the **nanopass/micropass** discipline (Sarkar-Waddell-Dybvig 2004; Keep-Dybvig 2013) — many tiny
typed-IL passes — is the compiler-level echo of the kernel's correctness-by-construction, and the
right host for a VERIFIED two-hop pipeline (each small pass individually provable; cf. CompCert).

**Blocked on**: nothing now (v1 ships uniform-lazy per invariant #7).

**Revisit signal**: building the `$comptime` stage, the reactive cell (rung 4), or a perf pass that
wants to elide thunk allocations.
