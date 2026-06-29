# PATH · Tracer bullet — the first product-spine issue

> The thinnest end-to-end slice that makes bang-lang **run a program**. Pulled forward per PRD §7.
> Status: **✓ DONE** (rung 0; 2026-06-23, commit `ff7bb9d`). The language RUNS — surface → graded-CBPV
> `Comp` → `Source.eval` → a VALUE (pure + throws), in `Bang/Frontend/Surface.lean`. Superseded as "next work"
> by rung 1 (✓) then rung 2; kept as the rung-0 record.

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

- The kernel TODAY (`Bang/Core/IR.lean`, `Bang/Core/Semantics.lean`): graded-CBPV `Comp` (de Bruijn:
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

- A new surface module (e.g. `Bang/Frontend/Surface.lean` or a `surface/` area) with the minimal parser +
  lowering, plus a runnable demo/test (`native_decide`/`rfl` battery à la the ADR-0023 journeys)
  showing `source → value` green for ≥1 pure + ≥1 throws program.
- `just verify` stays green (the new module builds; no spine theorem disturbed).
- A short note (in this file or a follow-up) on **what the surface→`Comp` lowering revealed** — the
  de-risking output (e.g. "the kernel lacks primitive arithmetic", "let-binding maps cleanly",
  "throws needs the answer-type to line up"). This finding is the point as much as the green test.

## POINTERS

- PRD: `docs/PRD.md` §5 (eval-stage axis), §6 (v1 scope), §7 (this bullet).
- Kernel: `Bang/Core/IR.lean` (the `Comp` constructors), `Bang/Core/Semantics.lean` (`Source.eval`,
  `Source.step`, `handlesOp`, `dispatch`).
- Pattern to copy: the ADR-0023 smoke tests (hand-built `Comp` → `Source.eval` → value via `rfl`) —
  see the commit `d12b436` description / `/tmp/machine_test.lean` shape.
- v0.1 surface reference: `/srv/share/projects/bang-lang/examples/hello.bang`,
  `/srv/share/projects/bang-lang/packages/core/src/Parser.ts`.
- Watch out: `Source.eval`/`Source.step` are well-founded recursions — concrete runs reduce via
  `simp [Source.step]` / `rfl`, NOT bare `rfl` on `Source.step` (it has `termination_by`).

## Finding (Stage 1+2)

Status: **DONE** (2026-06-22). Module `Bang/Frontend/Surface.lean` (~340 lines), wired into `Bang.lean`.
The full pipeline `source String → Surf → Comp → Source.eval → Result Val` is green in the build.

What the surface→`Comp` lowering REVEALED — the de-risking output:

1. **The kernel has no primitive arithmetic, and that shapes the surface.** There is no `+`; the
   five primitives give let-binding, force, lambda/app, raise/handle. So the canonical "pure"
   demo is `let x = 3 in x` (sequencing + variable lookup), NOT `x + y`. Adding `+` would be a
   *sixth primitive* (K-ADR) — correctly out of scope. The honest tracer-bullet "compute" story is
   binding/forcing, not arithmetic; a real `+` belongs in a library effect or a future numeric ADR.

2. **`let` maps cleanly onto `letC`; the only real work is the name→de-Bruijn pass.** The lowering
   threads an `env : List String` (innermost binder first); a name's index is its position
   (`List.idxOf?`), and each binder conses its name for the body. This single pass is the whole
   surface→kernel bridge for binders — `lam`/`letC` both just cons. A free name is a clean
   `Except String` error. **This is the biggest de-risked unknown: name resolution is ~6 lines.**

3. **The CBPV value/computation split surfaces immediately in lowering.** `lowerC`/`lowerV` are a
   mutual pair: an atom (literal/var) in *computation* position becomes `ret v`; in *value* position
   it stays a `Val`. A computation in value position is a surface error — the user must thunk it
   (`{ … }` → `vthunk`). So the adjunction (`thunk`/`force`) is not hidden plumbing; it is a surface
   obligation the parser must expose. The `!`/`$` force UX (v0.1) maps to `force (vthunk …)`.

4. **`throws` needs no answer-type juggling to RUN.** Because `Comp` is grade- AND type-free,
   `handle (throws ℓ) body` and `up ℓ "raise" v` lower with zero type information. The answer-type
   line-up (ADR-0023's `opArg ℓ "raise" = block result`) is a *typing* concern; running a program
   never touches it. Lowering picks one concrete label (`exnLabel = 0`, since `Label := Nat`) and a
   fixed op name `"raise"` — that is all the machine's `handlesOp`/`dispatch` needs.

5. **`rfl` is the right discharge for kernel eval, the WRONG one for string parsing.** Stage-1/1b
   checks (`Comp` eval, AST lowering) discharge by `by rfl` in milliseconds — the machine is a small
   concrete `Nat`-fuelled recursion. But reducing the *parser over a `String`* in the kernel
   (`rfl`/`decide`) is pathological (`String` ops don't `whnf` cheaply) — a single such `rfl` did not
   finish in 250s. The Stage-2/2b string checks therefore use `#guard` (compiled evaluation):
   millisecond, build-failing-if-false, and NOT a banned tactic (`#guard` ≠ `sorry`/`admit`/
   `native_decide`; touches no spine theorem). Practical rule for future surface tests:
   **`rfl` for kernel terms, `#guard` for anything reducing a `String`.**

6. **The parser must be fuel-driven total, not `partial`, if its results are to appear in checks.**
   A `partial def` is opaque to the kernel, so `parse "…" = …` cannot reduce. The recursive descent
   takes a structural `Nat` fuel (passed decremented at every call, set to token-count at the call
   site) so it is total and its output is inspectable. This is the same fuel discipline the machine
   already uses (`Config.run`).

Green checks (all in `Bang/Frontend/Surface.lean`, all in the build):
- Stage 1 — `example : Source.eval 20 {pure,throws,deep}Comp = .done (.vint {3,7,7})`  · `by rfl`
- Stage 1b — `example : lower <surf> = .ok <comp>` (×3)  · `by rfl`
- Stage 2 — `#guard runYieldsInt 20 <src> {3,7,7}` (×3, from source text)
- Stage 2b — `#guard parsesTo <src> <surf>` (×3, parser pinned independently)

Not done / out of scope (unchanged from above): type-checking the surface (grades/effect rows),
`mut`/State (Q12), richer effect declarations (only one `raise` channel), and any syntax beyond the
documented subset grammar (no operators, no top-level decls, no multi-binding `let`).
