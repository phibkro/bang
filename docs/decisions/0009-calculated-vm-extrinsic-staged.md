# ADR-0009 · The calculated VM is extrinsic and grown one constructor at a time, starting from an arithmetic kernel

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: The calculated VM is extrinsic and grown one constructor at a time, from an arithmetic kernel.

- **Status:** Accepted
- **Date:** 2026-05-31
- **Related:** 0004 (the VM is the *output* of a Bahr–Hutton calculation from `eval`), 0008 (the `eval` it derives from; the free monad collapses to a plain `eval` on the pure fragment), roadmap §3 (the staging) and §8 (the reading canon)

## Context

K2 calculates `(compile, Code, exec)` from `eval` so that `exec ∘ compile ≡ eval`
(ADR-0004, Bahr–Hutton). Two implementation choices shape every later stage and
are each reversible, so they are recorded here:

1. **How the machine is typed in Lean** — extrinsic (a plain instruction list +
   a separate equivalence theorem) vs intrinsic/dependently-typed (`Code` indexed
   by the stack shape, à la Pickard & Hutton 2021, where ill-typed code is
   unrepresentable).
2. **How big the first proven increment is** — settled by the operator decision
   to start with the arithmetic kernel, fully proven.

## Decision

- **Extrinsic first.** `Code` is a plain `List Instr`; `compile : Src → Code → Code`
  and `exec : Code → Stack → Stack` are ordinary total functions; correctness is a
  **separate, proven theorem** `exec (compile e c) s = exec c (eval e :: s)`, with
  corollary `exec (compile e []) [] = [eval e]`.
- **Grow the source one constructor at a time.** The calculation starts from a
  dedicated denotational `Src` for the **arithmetic kernel** (`val`, `add`, `mul`)
  and extends constructor-by-constructor toward the full pinned core, each stage
  extending `Code`/`compile`/`exec` and **re-proving** the theorem. Each stage is
  its own green commit. Order actually taken: **arithmetic → `let`/`var` →** (then)
  `if` → `force`/application → effects. `let`/`var` was taken before `if` because
  it has no value-representation mismatch with the reference — on the pure total
  fragment, `Bang.Eval`'s call-by-name `let` and the machine's strict `let` denote
  the same value, so the machine is *both* proven and differentially testable.
  `if` is deferred until a Bool/value story lands: `Bang.Eval`'s `if` branches on a
  `Bool` ADT, so an Int-conditioned machine `if` could be *proven* but not
  meaningfully *diff-tested* against the reference until ADTs/Bool are in `Src`.
- **Calculate from a denotational `eval`, cross-checked against the operational
  one.** The paper method derives from a denotational `eval` (here `eval : Src →
  Int`). It is kept honest against the operational reference `Bang/Eval.lean`
  (ADR-0008) by the differential **harness**: an `exec` oracle op runs the
  calculated machine and is diff-tested against the `eval` oracle on the same
  programs. So: machine ≡ denotational `eval` (Lean **proof**) ≡ operational
  `eval` (harness). Nothing runs without that loop closed (invariant 1).

## Rationale

- **Legible proofs that grow.** The extrinsic equivalence proof for the
  arithmetic kernel is a three-line induction (`generalizing c s`) with no `sorry`
  — the canonical Hutton result. Adding a constructor adds a case, not a redesign.
  The intrinsic version front-loads stack-shape invariants into the *types* of
  `compile`/`exec`, which is elegant but couples every early proof to machinery we
  do not yet need.
- **The machine still falls out (ADR-0004).** Extrinsic vs intrinsic is *how the
  correctness is stated*, not whether the instructions are designed: `compile`/
  `exec`/`Instr` are still **derived** from the `exec (compile e c) s = …`
  specification by induction, never hand-posited.
- **Arithmetic-first is correctness-by-construction.** It establishes the entire
  calculation skeleton — `Src`, `Code`, `compile`, `exec`, the theorem, and the
  harness wiring — on a fragment whose proof is known-clean, before the hard parts
  (closures, the effect-monad swap) land. Matches small-green-commits.
- **Denotational source is what the method needs.** The free-monad `eval` (ADR-0008)
  is the source for the *effectful* stages (its resumption is what gets
  defunctionalized); on the pure fragment it is a plain function, which is exactly
  the Bahr–Hutton starting point. Keeping a small denotational `Src`/`eval` and
  checking it against the operational reference via the harness avoids contorting
  the proof around the CPS form prematurely.

## Rejected alternatives

| option | why not |
|--------|---------|
| **intrinsic dependently-typed `Code` now** (Pickard–Hutton) | front-loads stack-shape invariants into types before any constructor is calculated; heavier early proofs for a payoff (ill-typed-code-unrepresentable) we can adopt later as a refinement |
| **straight to thunk/force/application** in increment 1 | the distinctive kernel needs closures in the machine; the equivalence proof would ship partly as `sorry`. Deferred to a later increment, on top of the proven skeleton |
| **calculate directly from the operational CPS `eval`** | the paper method is stated over a denotational `eval`; deriving from the CPS form is awkward for the pure stages. Revisit at the effect stage, where the free-monad form *is* the right source |
| **one big `Src = Expr`, partial `compile`** | partial `compile`/`exec` over 14 constructors muddies totality and the proof; grow a total `Src` instead |

## Consequences

- The first artifact is `oracle-lean/Bang/Calc.lean`: `Src`/`Instr`/`Code`/`eval`/
  `compile`/`exec` + the proven `exec_compile` and `compile_correct` (no `sorry`).
- A new `{"op":"exec",…}` oracle op runs the calculated machine; a harness test
  diff-tests it against the `eval` op on arithmetic programs.
- `Src` is, for now, a parallel arithmetic language; as it grows toward the pinned
  core, a semantic embedding `Src ↪ Expr` (agreeing with `Bang.Eval.eval`) becomes
  the tie that makes "the VM is calculated from *the* eval" literal. The harness
  already checks that agreement operationally at each stage.

## Revisit if

- Stack-shape bugs start slipping past the extrinsic proofs (e.g. an `exec`
  underflow case that typechecks but is wrong) → **switch to the intrinsic
  dependently-typed encoding**, where those states are unrepresentable, as a
  refinement of the then-current stage.
- The effect stage makes the denotational `Src`/`eval` and the operational
  free-monad `eval` expensive to keep in sync → calculate that stage **directly
  from the free-monad `eval`** (its resumption defunctionalizes into the machine),
  per the method's monadic form (Bahr–Hutton 2022).
