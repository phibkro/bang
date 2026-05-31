# ADR-0010 · Higher-order calculation: fuel-indexed CBV with shared source-closures (equivalence now proven)

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

## Proof status — PROVEN (the deferral was resolved in-session)

The machine is calculated, differentially tested green against the `eval` oracle
(closures, capture, higher-order args; goldens + a 500-case fuzz), **and the Lean
equivalence `compile_correct` is now proven — no `sorry`.** The proof shipped in
the same session this ADR was written, so the original "deferred" framing is kept
only as history; the live status is *proven*.

The proof (in `Bang/CalcHO.lean`):
1. **Fuel monotonicity** — `exec_succ` / `exec_mono`: more fuel never changes a
   successful result (induction on fuel; the `APP` case uses the IH on the nested
   callee run).
2. **`sim`** — the forward simulation `eval fe env e = some v → ∀ c s F r,
   exec F c env (v::s) = some r → ∃ F', exec F' (compile e c) env s = some r`.
   Stating the target as a concrete `some r` (not `exec F c …`) is the key move:
   it lets `exec_mono` align the sub-fuels, so the `app` case bumps the callee and
   the continuation to a common fuel. The shared `vclo` keeps `lam`/`app` an
   *equality*, not a logical relation — vindicating the shared-`Value` decision.
3. **`compile_correct`** — corollary: `eval fe env e = some v → ∃ F,
   exec F (compile e []) env [] = some [v]`.

The only `sorry` left in the build is K1's `unify_sound`.

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
