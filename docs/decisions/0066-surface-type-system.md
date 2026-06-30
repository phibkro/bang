# ADR-0066 · Surface type system — a bidirectional checker targeting the kernel `HasCTy` (tested-superset, grades-deferred)

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: The surface gains a TYPE LAYER — a bidirectional type-checker (`check ⇐` / `synth ⇒`) over the surface AST that produces typing conforming to the kernel's graded `HasVTy`/`HasCTy` relation. The relation stays the single source of truth; the checker is an ALGORITHM in the TESTED superset (its soundness vs `HasCTy` is differential-tested, not proven in v1). v1 checks type structure + effect rows; grades default to `ω` (grade-checking is a separable refinement). Unblocks #5 (effect-typed signatures), #24 (lawful algebra — type-directed operator resolution), #21 (scoped capability types).
- **Resolves**: the "type-checking the surface is a later issue" deferral stated in `Bang/Frontend/Surface.lean`
- **Depends-on**: 0019, 0020, 0028, 0029

- **Status:** Accepted (architecture + staging locked; the type-expression grammar + checker are staged below).
- **Date:** 2026-06-30
- **Layer:** S (surface) / T (tooling) — the kernel `HasCTy` relation is UNTOUCHED; this adds the surface ALGORITHM that targets it. **Not** a K-ADR (no kernel change).
- **Resolves:** the surface's own deferral — *"It produces no typing derivations … type-checking the surface is a later issue"* (`Bang/Frontend/Surface.lean` header). This is that later issue, designed.
- **Builds on:** ADR-0019/0020 (graded de-Bruijn context — `GradeVec`/`TyCtx`, the `HasVTy`/`HasCTy` the checker targets). ADR-0028 (verified-core / tested-superset stratification — the checker's tier). ADR-0029 (iso-recursive ADTs — `sum`/`prod`/`μ` the checker must handle).
- **Reference:** Dunfield–Krishnaswami, *Bidirectional Typing* (ACM CSUR 2021 — the survey; check/synth modes, annotation placement). Levy, *Call-by-Push-Value* (the value/computation split the checker respects). Atkey, *Syntax and Semantics of Quantitative Type Theory* (the QTT grade discipline, deferred here).

## Context — the surface runs, but does not type

The pipeline today is `String → parse → Surf → lower → Comp → Source.eval`. The surface deliberately
produces NO typing (it lowers to grade-free `Comp` and runs). The kernel HAS a full graded typing
relation — `HasVTy : GradeVec → TyCtx → Val → VTy` and `HasCTy` for `Comp` (ADR-0019/0020), proven
sound (`progress`/`preservation`/`type_safety`) — but it is a **declarative relation**, not an
algorithm, and nothing connects it to surface programs.

This blocks the typed future. The northstar **#24 (lawful algebra)** needs `a + b` to resolve its
operator instance *by the type of `a`/`b`*, and its laws are *typed* propositions — neither is possible
without types flowing through the surface. **#5 (effect-typed signatures)** and **#21 (scoped capability
types)** are the same gap. So the type layer is the critical path; this ADR designs it.

## Decision

### 1. Algorithm = bidirectional typing (`check ⇐` / `synth ⇒`)

Two mutually-recursive modes over the surface AST:
- `synth : TyEnv → Surf → Except TypeError (Ty × Eff)` — infer a term's type (and effect row).
- `check : TyEnv → Surf → Ty → Except TypeError Eff` — check a term against an expected type.

CBPV maps cleanly: **values** synth/check at `VTy`; **computations** at `CTy`; `force`/`thunk` cross the
adjunction (mode switch). Eliminators are checking-driven (the scrutinee synthesizes); introductions
check against the expected type (so `Left(e)` checks `e` against the `A` of an expected `A + B`).
**Annotations** carry the burden where inference can't: function parameters (`fun (x : Int) => …`) and
top-level (`e : T`); everything else is inferred. (Rejected: full Hindley–Milner — doesn't fit graded
CBPV + effects + future user-operators; bidirectional is the modern standard for rich systems. Rejected:
fully-annotated — too verbose.)

### 2. `HasVTy`/`HasCTy` is the SPEC; the checker is an algorithm that TARGETS it

Single source of truth: the kernel relation is the truth. The checker is a NEW algorithm whose
**soundness** is the contract — *if `check`/`synth` accepts, the program's lowering is `HasCTy`-derivable*.
We do **not** write a second surface typing relation (that would be two copies of the typing rules — the
SSoT violation ADR-0028's stratification engineers against). The surface `Ty` syntax is a thin sugar over
`VTy`/`CTy`; checking maps to a `HasCTy` claim on the lowered `Comp`.

### 3. Tested superset, NOT verified core (v1)

Per ADR-0028, the checker sits in the **tested** tier. Its agreement with `HasCTy` is **differential-tested**,
not proven in v1:
- **soundness corpus** — well-typed surface programs; assert the lowering is `HasCTy`-derivable (the
  existing `Examples`/`#guard` discipline, extended with a `HasCTy` witness check).
- **rejection corpus** — ill-typed programs the checker must reject (`3 + Left(0)`, applying a non-function, …).
- (later) **property test** — generated terms: `check` accepts ⟹ `HasCTy` holds (Plausible, #80 harness).

A **verified** type-checker (machine-proven sound *and* complete vs `HasCTy`) is the gold standard and a
post-v1 aspiration — a large proof. v1 buys the capability at tested-rung cost, exactly the stratification
move (proof budget on the kernel relation; the algorithm rides differential-testing).

### 4. Grades default to `ω`; grade-checking is a separable refinement

`HasCTy` is graded (QTT = {`zero`,`one`,`omega`}; ADR-0019). `omega` = **unrestricted use**, so a term
typed with every binder at `ω` is `HasCTy`-derivable whenever it is type-correct *modulo* the resource
discipline. v1 therefore checks **type structure + effect rows** and assigns grades `= ω` uniformly;
**grade-checking** (linearity — the `0`/`1` distinctions, "used exactly once", erasure) is its own later
increment. (Rejected: full QTT grade *inference* in v1 — research-level; premature when the immediate
unblock (#24, #5) needs *types*, not linearity. The `ω`-default is sound: it produces valid `HasCTy`
derivations; it just doesn't yet *enforce* the resource discipline.)

### 5. Effect rows ARE inferred — this layer IS #5

`synth`/`check` return the computation's **effect row** (the union of labels its `perform`s touch,
discharged by enclosing handlers). That is precisely **#5 (effect-typed signatures + type display)**:
a function's inferred `CTy` shows its effect row (`Int -> {throws} Int`). So #5 is not a separate feature
— it is the natural output of this checker.

### 6. Surface type syntax (new grammar, staged)

Users write types: `Int`, `Unit`, `A -> B` (function `CTy`), `A + B`, `A * B`, `Thunk C` (the `U`
former), `Cap ℓ`, and effect rows on computations (`{throws} Int`, the #5 surface). Annotations:
`fun (x : T) => e`, `let x : T = e in …`, top-level `e : T`. A type-expression parser (a small Pratt-ish
grammar — note the synergy with #30) produces a surface `Ty` that maps to `VTy`/`CTy`.

## Downstream — what this unblocks (and how they hook in)

- **#5** — *is* this (decision 5): effect rows in inferred types + type display.
- **#24 lawful algebra** — once `synth` exposes `a : Vec`, operator resolution looks up the
  `AddCommGroup Vec` instance by that type. The **typeclass/instance mechanism + law checking** is a
  SEPARATE feature on top; this layer's job is only to *make the type available* at the operator site.
- **#21 scoped capability types** — `Cap ℓ` types surface here; scoping rides the checker.

## Consequences & staging (each gated; de-risk early)

```
① this ADR — architecture locked
② type-expression grammar + parser (Ty syntax + annotations on fun/let/top-level)
③ SPIKE — bidirectional checker for the PURE fragment (int·unit·let·lam·app·pair·sum, no effects/
   grades) over Surf, + 3-5 diff-tests (checker-accepts ⟹ HasCTy on the lowering). De-risks the
   architecture before breadth. ← do this BEFORE committing to the full build.
④ effects — infer/check effect rows (handlers discharge labels) = #5 shipped
⑤ corpora — soundness + rejection corpus as #guards; wire the HasCTy-witness check into the gate
⑥ (later, separable) grades (linearity) · instance resolution (#24) · a VERIFIED checker
```

Surface/tooling only; the kernel `HasCTy` and the verification spine are untouched (the checker is a leaf
consumer, like `Surface.lean`). The first real step after this ADR is the **spike (③)** — a minimal
bidirectional checker for the pure fragment, diff-tested against `HasCTy`, to validate the architecture
cheaply before the full grammar + effects.
