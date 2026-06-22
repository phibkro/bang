# PATH · Tracer bullet — the first product-spine issue

> The thinnest end-to-end slice that makes bang-lang **run a program**. Pulled forward per PRD §7.
> Status: **READY** (scoped 2026-06-22, not started). Grabbable by a fresh session.

## GOAL (verifiable)

A real bang **source string** goes `surface → graded-CBPV Comp → Source.eval → a VALUE`, shown — for
(1) a pure program and (2) an effectful (throws) program. Verifiable as a Lean check:
`Source.eval fuel (lower (parse src)) = Result.done <expected>` is green (the `machine_test.lean`
pattern from ADR-0023). When this is green, "bang-lang runs a program" is **true**.

## WHY (the de-risking, PRD §7)

1. Makes the language *real* (it runs) — before ◊5, not after.
2. **De-risks the surface→kernel lowering** — the biggest product unknown. It is invisible until you
   try to express a real program as graded-CBPV `Comp`. This issue surfaces it cheaply.
3. Gives a concrete artifact to grow, instead of more mid-pipe proofs.

## CONTEXT (facts; don't recompute)

- The kernel TODAY (`Bang/Core.lean`, `Bang/Operational.lean`): graded-CBPV `Comp` (de Bruijn:
  `ret`/`letC`/`force`/`lam`/`app`/`up`/`handle`); `Source.eval : Nat → Comp → Result Val` is a
  fuel-driven **CK machine** with deep handlers (ADR-0023), proven type-safe for the **pure core +
  throws**. **State is deferred (Q12)** — so the first tracer bullet uses pure + throws, NOT `mut`.
- **`Comp` is GRADE-FREE** — grades live only in the typing (`HasCTy`/`GradeVec`). So the lowering
  targets grade-free `Comp`; you do NOT need to produce typing derivations to *run* a program.
  (Type-checking the surface is a later issue.)
- Product decision **B** (PRD §4): lang-bang grows its own surface; v0.1 (TS) is the **syntax
  reference** — mine `examples/hello.bang` and `packages/core/src/{Lexer,Parser}.ts` for the
  `!`-force surface, don't port the TS.

## SCOPE

**Stage 1 — kernel expresses a real program (no parser).** Hand-build the `Comp` AST for one pure
program (e.g. `let x = 3 in x + ...` shape — note: the kernel has no built-in `+`; use what `Comp`
provides, or add a primitive only if needed) and one throws program (`handle (throws ℓ) (… up ℓ
"raise" v …) → ret v`). Run `Source.eval`, assert the value. Proves the kernel can express it.

**Stage 2 — minimal surface (the thin parser).** A small `String → Comp` parser for a SUBSET:
literals, `let`/binding, force (`!`/`$`), lambda/application, and `handle`/`raise`. Lower to `Comp`.
Re-run the Stage-1 programs *from source text*. This is the actual surface spine.

**Out of scope** (explicitly): full surface syntax; type inference / effect-row checking; `mut`/State
(Q12); CalcVM/WasmFX codegen; STM. **Do not edit** the verification spine (`Metatheory.lean`,
`Spec.lean`, `Syntax.lean` typing) beyond reading — this issue is additive (a new surface module +
a demo/test), it must not touch proven theorems.

## DELIVERABLE

- A new surface module (e.g. `Bang/Surface.lean` or a `surface/` area) with the minimal parser +
  lowering, plus a runnable demo/test (`native_decide`/`rfl` battery à la the ADR-0023 journeys)
  showing `source → value` green for ≥1 pure + ≥1 throws program.
- `just verify` stays green (the new module builds; no spine theorem disturbed).
- A short note (in this file or a follow-up) on **what the surface→`Comp` lowering revealed** — the
  de-risking output (e.g. "the kernel lacks primitive arithmetic", "let-binding maps cleanly",
  "throws needs the answer-type to line up"). This finding is the point as much as the green test.

## POINTERS

- PRD: `docs/PRD.md` §5 (eval-stage axis), §6 (v1 scope), §7 (this bullet).
- Kernel: `Bang/Core.lean` (the `Comp` constructors), `Bang/Operational.lean` (`Source.eval`,
  `Source.step`, `handlesOp`, `dispatch`).
- Pattern to copy: the ADR-0023 smoke tests (hand-built `Comp` → `Source.eval` → value via `rfl`) —
  see the commit `d12b436` description / `/tmp/machine_test.lean` shape.
- v0.1 surface reference: `/srv/share/projects/bang-lang/examples/hello.bang`,
  `/srv/share/projects/bang-lang/packages/core/src/Parser.ts`.
- Watch out: `Source.eval`/`Source.step` are well-founded recursions — concrete runs reduce via
  `simp [Source.step]` / `rfl`, NOT bare `rfl` on `Source.step` (it has `termination_by`).
