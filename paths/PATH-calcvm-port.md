# PATH · CalcVM port (◊2 → ◊3)

> Collapse the K3 matrix of calculated machines into ONE graded-CBPV calculated machine,
> proven `exec ∘ compile ≡ eval`. Status: **IN PROGRESS** — first green increment landed 2026-06-23.
> Owner: kernel/proof-engineer.

## Progress

### D1 refinement — `evalD` is SUBSTITUTION-based, not env-based (2026-06-23)

The kernel's `Source.step` is **substitution-based with a closed focus** (no env, no closures:
`force(vthunk M)↦M`, `letC`/`app` reduce by `Comp.subst`). So `evalD` mirrors it (option (b) over a
closure/CEK (a)): this makes the `evalD ≡ Source.eval` bridge **nearly mechanical** (subst-vs-subst, it's
literally `Config.run`'s done-condition) — the whole payoff of D1-A — and keeps values as kernel `Val`.
**CBPV shape:** `evalD : Nat → Comp → Option Comp` returns the *terminal computation* (`ret v` OR `lam M`),
not a bare `Val` (a function-typed computation reduces to `lam`). Cost paid: the machine carries residual
`Comp` (CK-style, less flat); **flattening toward a numeric-stack VM is a deferred later calculation step**
(invariant #7). Rejected (a) closures/CEK: forks the value rep + makes the bridge a cross-rep simulation.

### Increments landed

- **✓ Unit 2 — pure spine** (`Bang/CalcVM.lean`, `158f08d`; supersedes the reverted `ae5f1ca` which merged
  red — termination unproven). Substitution `evalD` over `ret`/`letC`/`force`/`lam`/`app`; **termination by
  STRUCTURAL recursion on the fuel** (`Nat` decrements — no `termination_by`, no `partial def`). Calculated
  machine `{RET, LAMI, SUBST, APP, …}` DERIVED from `evalD` (invariant #4); `exec_compile` +
  `compile_correct` **PROVEN** over the subst machine, axioms `[propext]`, gate-guarded. Rides the gate
  (732 jobs); ◊2 gate held (0-axiom).
  - **ADT eliminators (`case`/`split`/`unfold`) DEFERRED** — they break `compile` termination (not cheap);
    revisit when the machine handles them (likely needs the flattening step or a different measure).
- **NEXT: the effect/handler units** (`up`/`handle` — deep handlers, the `Source.step` dispatch as machine
  code) — the real CalcVM payoff. THEN the `evalD ≡ Source.eval` agreement (Unit 1 bridge — cheap by
  construction now), then collapse + archive the K3 matrix (ADR-0017). Flattening (defunctionalize frames
  + compile-away subst) is a later optimization pass, not blocking.

## Target (◊3 gate, ROADMAP)

```
Calc* matrix  ──collapse──►  ONE graded-CBPV calculated machine
(11 K3 files)                (compile, Code, exec) ; exec ∘ compile ≡ eval
                             single unified module, sorry-free ; unified diff-test green
```

The K3 machines (`Bang/Calc*.lean`) calculate `(Instr/Code, compile, exec, exec_compile)` triples
from a **compositional** `eval`, Bahr–Hutton style (`-- derived, not designed`). They cover a matrix
of (convention × effects) over the OLD K2 free-monad `Expr`/`Value`. ◊3 redoes this ONCE over the new
graded-CBPV `Comp`, then archives the matrix (ADR-0017: directory move, not delete — it's the
proven-evidence corpus).

## What the new kernel gives us (the inputs)

- **`Bang.Source.eval`** — graded-CBPV operational semantics: a fuel-driven **CK machine**
  (`Source.step : Config → Option Config`, `Config = EvalCtx × Comp`) with **deep handlers**
  (ADR-0023). Hand-built (the reference small-step), type-safety-proven (preservation/progress/
  type_safety axiom-clean).
- **`Bang.Eval.eval`** — the K2 reference: free-monad **CPS** interpreter, deep handlers as a fold
  (`handleC` re-installs on resume + forwards unhandled ops), fuel-total. The *designed* Bahr–Hutton
  source — but over the OLD `Expr`. The shape ("resumption as a `Value → Comp` function →
  defunctionalize into machine code") is the calculation template.
- **Grades are ERASED at runtime.** `Comp` carries NO grades (they live in `HasCTy`/`GradeVec`, the
  typing). So `Source.eval` is grade-free and the CalcVM is **grade-agnostic** — grades never touch
  Code/exec. Grade-soundness stays a type-level story (`zero_usage_erasable` → ◊4). This is a big
  simplification: ◊3 is "calculate a machine for grade-free CBPV-with-deep-handlers."

## Design decisions (need an ADR — "◊3 port design lock")

### D1 — What do we calculate FROM? · ✓ DECIDED: Option A (2026-06-22)

Calculate from a **denotational graded-CBPV `evalD`** (port `Bang.Eval`'s free-monad CPS to the new
`Comp`); prove `exec∘compile ≡ evalD` AND `evalD ≡ Source.eval`. The agreement proof is the bridge
that lets the calculated machine inherit type safety. The deliberation:

Bahr–Hutton calculates a machine from a **compositional / denotational** `eval` (resumptions as
functions). We have two evals, neither ideal as-is:

| option | source | cost | discipline |
|---|---|---|---|
| **A (recommended)** | write a denotational graded-CBPV `evalD` (port `Bang.Eval`'s free-monad CPS to the new `Comp`), **calculate** `(compile, Code, exec)` from it, prove `exec∘compile ≡ evalD`, AND `evalD ≡ Source.eval` (tie to the type-safety reference) | a 2nd eval + an agreement proof | faithful to invariant #4 (machine is an OUTPUT of calculation) + invariant #1 (rides the reference) |
| **B** | calculate directly from the small-step `Source.eval` (refocusing/Danvy-style) | no 2nd eval, but non-standard derivation | machine still calculated, but from an operational (not denotational) source |
| **C** | bless the hand-built CK machine as the CalcVM + a thin `compile` serialization | cheapest | **violates invariant #4** (machine must be calculated, not hand-designed) — rejected |

**Recommendation: A.** It matches the repo's established K3 pattern (every `Calc*.lean` calculates
from a compositional `eval`), keeps invariant #4 honest, and the `evalD ≡ Source.eval` agreement
proof is exactly the bridge that lets the calculated machine inherit the type-safety guarantees. The
CK machine becomes an oracle/sanity check, not the spec.

### D2 — Machine shape + effects scope

- `Instr`/`Code := List Instr` for CBPV: `PUSH`/`THUNK`/`FORCE`/`LET`/`RET`/`APP`/`OP`/`HANDLE`-ish
  (exact set falls out of the calculation, not designed up front).
- **Deep-handler dispatch** = the hard novelty. Template: `CalcEff`'s handler-stack + `findHandler`
  (THROW jumps to recovery code), generalized from the shallow K2 source to CBPV frames between the
  op and its handler. This is the calculated analog of `Source.step`'s `dispatch`.
- **THROWS only**, matching the kernel's current handler scope. **State** + **multi-shot/non-tail**
  resumption = the reification frontier (`CalcReify`/ADR-0015) — DEFERRED (consistent with Q12/Q6
  state deferral). The effect-shape→mechanism map (ADR-0017 §4) says: throws = nested run + re-throw
  (no flatten); reification is the only thing forcing a flatten. So throws-only stays flatten-free.

### D3 — Collapse, archive, diff-test

- ONE unified module (e.g. `Bang/CalcVM.lean`) over graded-CBPV `Comp`.
- Archive `Bang/Calc*.lean` (the K2 matrix) + `Bang/Eval.lean` (K2 reference) → `archive/` (directory
  move per ADR-0017; the proven-evidence corpus survives).
- **Diff-test infra must be rebuilt Lean-side**: the TS differential harness was DELETED in the merge
  (`CONTEXT.md`). What survives: `selfcheck.mjs` (row unifier only) + per-file `native_decide`/`rfl`
  demonstrators. Plan: a Lean `native_decide` battery (like the ADR-0023 `machine_test` journeys) over
  a generated/curated program set, asserting `exec (compile c) = Source.eval c`. Optionally a small
  generator. (A heavier QuickCheck-style fuzzer is a nice-to-have, not the gate.)

## Risks / open

- **Deep-handler calculation** is the genuine hard part; the K3 reification frontier (`CalcReify`)
  was *paused* at the pivot. Throws-only deep dispatch is more tractable (CalcEff's unwinding lifted
  to CBPV), but the CBPV frames (letC/app) between op and handler are new vs. the flat K2 source.
- **`evalD ≡ Source.eval`** (D1-A) is a non-trivial agreement proof (denotational CPS vs small-step
  CK). The reward: the calculated machine inherits type safety.
- **Scope creep**: resist pulling in state/multi-shot (the reification frontier) — that's ◊3+/ADR-0015.

## Staging (proposed, post-ADR)

```
Unit 0   ADR "◊3 port design lock" — settle D1 (calculation source), D2 (machine shape), archive plan.
Unit 1   denotational graded-CBPV evalD (D1-A) + evalD ≡ Source.eval agreement (the bridge).
Unit 2   calculate (compile, Code, exec) for the PURE CBPV core (thunk/force/let/app/ret) + exec_compile.
Unit 3   add deep handlers (throws) — the dispatch/unwinding, calculated; extend exec_compile.
Unit 4   collapse + archive the K2 matrix; rebuild the Lean diff-test battery; ◊3 gate green.
```

## References

- `docs/decisions/0017-k3-calculated-machine-retrospective.md` — methodology + effect-shape map.
- `docs/notes/k2-calculation-playbook.md` — calculation proof patterns.
- `Bang/Calc.lean` (base), `Bang/CalcEff.lean` (throws-as-unwinding — the handler template),
  `Bang/CalcReify.lean` (reification frontier — the DEFERRED shape).
- `Bang/Eval.lean` — the K2 free-monad CPS reference (D1-A's port source).
- Bahr–Hutton 2022 *Monadic Compiler Calculation*; Hutton–Wright *Compiling Exceptions Correctly*.
