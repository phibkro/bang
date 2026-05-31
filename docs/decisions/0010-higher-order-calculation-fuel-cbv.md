# ADR-0010 · Higher-order calculation: fuel-indexed CBV with shared source-closures; equivalence proof deferred

- **Status:** Accepted
- **Date:** 2026-05-31
- **Related:** 0009 (the calculation method/staging this extends), 0008 (the fuel-bounded reference; CBV-on-the-total-fragment cross-check), 0004 (the VM is calculated from `eval`)

## Context

K2 increment 3 adds `λ`/application to the calculated machine (`Bang/CalcHO.lean`).
Unlike the first-order increments (arithmetic, `let`/`var` — total, proven by a
short induction in `Bang/Calc.lean`), closures force three decisions, all settled
by the operator and recorded here.

## Decision

1. **Partiality via fuel + `Option`** (not coinduction, not intrinsic typing).
   Untyped `λ` diverges, so `eval` and `exec` are `Nat`-fuel-bounded partial
   functions returning `Option`, structurally recursive on fuel — exactly the
   device the operational reference `Bang.Eval` already uses (ADR-0008).
2. **Call-by-value** (eager arguments). Faithful CBN + thunk/force is a *later*
   increment; CBV is the simpler closure step. On the **pure, total fragment** CBV
   and `Bang.Eval`'s call-by-name denote the same value, so the harness diff-test
   against the `eval` oracle stays sound.
3. **Shared `Value`, source-closures.** A value is `vint Int | vclo Src Env` — the
   closure stores the *source body* + captured env, and the **same** `Value` type
   is used by `eval` and the machine. So correctness is an *equality* of values,
   not a cross-representation logical relation (the usual pain of higher-order
   compiler correctness). The machine's `APP` runs the callee's freshly-compiled
   body as a sub-computation.

`CLOS`/`APP` still **fall out** of the spec `exec (compile e c) env s ≃ exec c env
(eval e :: s)` for the `lam`/`app` cases (derivation sketch in the file) — derived,
not hand-designed (ADR-0004).

## Proof status — honest

The machine is **calculated and differentially tested green** against the `eval`
oracle (closures, capture, higher-order args; goldens + a 500-case fuzz) — the
standing guarantee (invariant 1). The Lean equivalence `compile_correct` (a
**fuel-indexed simulation**) is **shipped as `sorry` with a written proof plan**,
exactly as `unify_sound` ships in `EffectRow.lean`. It is **not** claimed proven.
This increment is therefore *harness-backed, proof-pending* — qualitatively weaker
than the fully-proven `Bang/Calc.lean`, and deliberately kept in a **separate
module** so the proven first-order calculation stays untouched.

Proof plan (the next proof to land): (1) fuel-monotonicity for `exec`/`eval`;
(2) thread the continuation/stack, induct on eval-fuel and `e` — first-order cases
mirror `Calc.exec_compile` under `Option`; (3) the `app`/`lam` cases close via the
callee IH + monotonicity, kept an equality by the shared `vclo`.

## Rejected alternatives

| option | why not |
|--------|---------|
| **intrinsic STLC** (Pickard–Hutton), total `eval`, no fuel | elegant but a heavy dependently-typed rebuild; covers only well-typed terms; BANG's core isn't STLC. Held as a possible refinement (ADR-0009 revisit) |
| **CBN + thunk/force now** | faithful to BANG's kernel but markedly harder; would likely ship more of the proof as `sorry`. Deferred to the next increment, on top of these closures |
| **distinct denot/machine closures + logical relation** | the standard but heavier route; the shared-`Value` source-closure keeps correctness an equality instead |
| **rewrite the proven `Calc.lean` into the `Option`/`Value` form** | would add fuel/`Option` bookkeeping to already-clean proofs and risk un-proving them; keep `Calc` proven, add `CalcHO` alongside |

## Consequences

- `Bang/CalcHO.lean`: `Src` (+`lam`/`app`), `Value`, fuel `eval`, `compile`, fuel
  `exec` (+`CLOS`/`APP`), and `compile_correct` as `sorry`+plan.
- A new `{"op":"execho","fuel":N,…}` oracle op; `harness/test/calc-ho.test.ts`
  diff-tests it vs `eval`. The first-order `exec` op (proven `Calc`) is unchanged.
- Two calculation modules coexist for now (`Calc` proven first-order; `CalcHO`
  frontier). They merge once `compile_correct` lands and `CalcHO` subsumes `Calc`.

## Revisit if

- The fuel-indexed equality proves intractable → adopt **intrinsic typing** for
  the higher-order stage (ADR-0009's revisit), making `eval` total and the
  relation more definitional, accepting the well-typed-only restriction.
- CBV vs CBN starts to matter before thunk/force lands (e.g. a test program where
  an unused argument diverges) → bring the CBN/thunk increment forward.
