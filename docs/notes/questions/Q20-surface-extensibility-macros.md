---
type: design-question
title: "Surface extensibility: pseudoinstructions via aliasing + macros"
description: "hygienic macros expanding to core Comp — keep the kernel at five primitives as the surface grows"
status: open
area: surface
ties: ["ADR-0006", "ADR-0020"]
see-also: ["Bang/Frontend/Surface.lean"]
---
**Question**: the surface is sugar over the semantics (formatter, linter, **pseudoinstructions**). The
*principle* is set: **never add a kernel primitive for something expressible as a composite of existing
primitives** (invariant #5) — instead provide **aliasing + metaprogramming** that expands to primitive
composites (like assembly pseudo-ops). Open: the *mechanism* — how macros/aliasing work, and how much
syntactic extensibility the surface offers.

**Why it matters**: this is "write your own constructs" from the vision, and the discipline that keeps
the kernel at five primitives as the surface grows. Get it right and new paradigms/notations are
libraries; get it wrong and the kernel bloats or the surface fragments.

**Detail**: levels of extensibility — (a) plain *aliasing* (a name for a composite, no new syntax);
(b) *hygienic macros* that expand to core terms before lowering (Lean 4 elaboration, Racket
`define-syntax`, Scheme); (c) full *user-defined notation* / reader extension (custom operators,
mixfix — Lean `notation`, Agda mixfix). Hygiene (capture-avoidance) interacts with ADR-0006/0020 (no
implicit capture; de Bruijn). The *semantic* DSL mechanism already exists (effects + handlers = a
little language per effect); this Q is about *syntactic* extension on top.

**Options**: (1) elaboration-style hygienic macros expanding to core `Comp` (recommended; Lean 4 model
— composes with the existing lowering pass in `Bang/Frontend/Surface.lean`); (2) aliasing only (no new syntax —
minimal, may be too weak for ergonomic DSLs); (3) full reader/notation extension (most powerful, most
rope). The five-primitive invariant + "no new primitive if composite" is the *constraint*; the
mechanism is the *choice*.

**Blocked on**: nothing now — a surface-layer concern (liquid); meaningful once the surface grows past
the rung-0/1 toy parser.

**Revisit signal**: the surface accumulating repeated composite patterns that want a name; or building
the first user-defined construct/notation.
