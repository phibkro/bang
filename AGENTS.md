# AGENTS.md — read this first

You are a fresh session. **This repo is your only memory.** Anything not written here did not happen. Read this file, then the roadmap, then the ADRs, before changing anything.

## What BANG is

A small language whose **paradigm and runtime are values, not language features**. The kernel is thunks + effects + STM; everything else (mutability, IO, async, actors, signals) is ordinary library code over it. Programs are **descriptions** until forced with `$` (ADR-0007; `!` is actor-send); a function's **paradigm** is which effects are in its row; a program's **runtime** is a handler installed at the use site.

## Repo map

| you need… | go to |
|-----------|-------|
| what the language *is* | `docs/spec/bang-lang-design.md`, `docs/spec/bang-lang-description-value.md` |
| where the project is going | `docs/roadmap/bang-northstar-roadmap.md` (dense) · `.html` (visual) |
| **why** things are the way they are | `docs/decisions/` (ADRs) — read these before proposing changes |
| the verified reference (K1 unifier) | `effectrow-oracle/oracle-lean/Bang/EffectRow.lean` (Lean 4 + Mathlib) |
| the reference `eval` (K2/K3 source) | `effectrow-oracle/oracle-lean/Bang/Eval.lean` |
| the calculated machines (K2/K3) | `Bang/{Calc, CalcHO, CalcCBN, CalcEff, CalcSt}.lean` — all proven `exec ∘ compile ≡ eval` (see playhead table) |
| **how to prove the next increment** | `docs/notes/k2-calculation-playbook.md` — fuel-alignment, mutual-induction & two-part-sim patterns, gotchas. **Read before proving.** |
| the standing guarantee | `effectrow-oracle/harness/` (differential tests) + `effectrow-oracle/tools/selfcheck.mjs` |
| what to read | reading canon, end of the roadmap `.md` |

## Current playhead

**K0 locked · K1 done · K2 done · K3 in progress.** **Every theorem in the repo is proven — zero `sorry`s.** The verified reference `eval` exists; the VM is **calculated** from it (Bahr–Hutton), and each calculated machine is proven `exec ∘ compile ≡ eval` *and* differentially tested against `eval`.

**The reference:** `oracle-lean/Bang/Eval.lean` — a fuel-bounded, total free-monad interpreter for the pinned core (thunk + `$`force, λ/app, `let`, ADTs+match, one-shot State/Throws handlers as a deep fold). Shape/rationale: **ADR-0008**. Effect labels reuse the K1 `EffectRow` `Finset` model.

**The calculated machines** — each proven `exec ∘ compile ≡ eval` (**no `sorry`**), each with an `{"op":…}` oracle op + a `harness/test/calc-*.test.ts` differential test:

| module | covers | convention | proof shape | ADR |
|--------|--------|-----------|-------------|-----|
| `Calc` | arithmetic, `let`/`var` | total, no fuel | direct equality, structural | 0009 |
| `CalcHO` | + λ/application (closures) | CBV, fuel | fuel-indexed `sim`; shared `vclo` ⇒ equality not a logical relation | 0010 |
| `CalcCBN` | + thunk/`$`force | call-by-name, fuel | **mutual** `eval`/`forceV` `sim`; matches `Bang.Eval` *exactly* | 0010 |
| `CalcEff` | general handlers, **Throws** | total `eval` / fuel machine | **two-part ret/exc `sim`**; handler stack + unwinding (`unwindFind`) | 0011 |
| `CalcSt` | **State** (`get`/`put`/`runState`) | total, no fuel | direct equality; threaded state register | 0011 |

Plus K1's `unify_sound` (proven — it needed a **freshness precondition**: `fresh` not already a row's tail var, else the open/open case binds a cyclic `some fresh`).

**Harness:** `Bang/EvalJson.lean` exposes the ops; `harness/` drives an independent TS candidate (`src/eval-candidate.ts`) on `eval` goldens + a fuzz, and diff-tests **each** machine vs `eval`. **55 tests green** (`make check-lean`).

**Method ↔ papers** (reading canon, roadmap §8): Bahr–Hutton 2022 *Monadic Compiler Calculation* (swap the monad) · Hutton–Wright *Compiling Exceptions Correctly* (the unwinding machine) · Pickard–Hutton 2021 (intrinsic, Lean-shaped). **Honest deltas (named, not hidden):** we use **fuel/`Option`**, not the partiality monad; artifacts are spec-guided definitions + a *post-hoc* `exec∘compile≡eval` proof (the derivation lives in the `-- derived, not designed` comments), not a mechanized step-by-step calculation; `CalcEff`/`CalcSt` exercise one-shot *tail* resumption / unwinding, **not** explicit continuation **reification**.

**Genuinely next** (none of this is done — *read the playbook first*):
- **Compose the fragments** — effects on the closure/CBN core (the real K3: swap the underlying monad on `CalcCBN`; merge `CalcEff`'s handler stack with closures). The biggest open step.
- **Continuation reification** — non-tail / multi-shot handlers (the true general-resumption frontier; Tsuyama 2024). `CalcEff`/`CalcSt` deliberately avoided it (ADR-0011).
- **K4 front end** — parse → typed AST → effect-row inference on the verified unifier → core IR.
- **Deferred & documented** (in `Eval.lean`, never faked): multi-shot handlers, STM, `:`/`=` reactivity, divergence-beyond-fuel, nested deep patterns.

**Build:** `nix develop` gives Lean via elan; `lake exe cache get` pulls Mathlib oleans; `make check-lean` is green. (The persistent-process harness needs the stdout flush in `Main.lean`; three Mathlib-version NUDGE spots were fixed early in the session.)

K0 decisions are locked — see ADRs. Do not relitigate locked decisions; read a decision's **"Revisit if"** clause first.

## Invariants — never break these

1. **Proof rides the reference.** Anything that runs is either `exec` itself or differential-tested against it. Never ship an execution path with no oracle behind it.
2. **Effect rows are sets** — idempotent, union = join. Never ordered, never a multiset. (ADR-0001)
3. **STM is the *only* privileged kernel primitive.** Everything else is effect + handler. (ADR-0003, design doc)
4. **The machine is an *output* of the calculation**, never hand-designed. Calculate, don't verify-after-the-fact. (ADR-0004)
5. **Kernel stays at five primitives:** thunk · force · effect rows · handlers · STM. Adding a sixth is a spec change requiring an ADR.
6. **No implicit capture; reactivity is the operator, not a keyword.** (ADR-0005, ADR-0006)
7. **Performance is second-class.** Optimize only where it touches the user; a slow correct path beats a fast unverified one.
8. **Effect TS is not the target.** The calculated VM is canonical; Effect TS is one optional lowering. (ADR-0004)

## Do NOT

- add a kernel primitive · make rows ordered · reintroduce `sig` · add implicit lexical capture
- make Effect TS (or any borrowed runtime) the canonical target
- hand-design the VM, then justify a compiler against it
- optimize speculatively, or add a feature the spec's Non-Features section forbids
- prove most-generality (MGU) for unification — soundness is the contract; MGU goes to the differential test

## Ubiquitous language (glossary)

| term | meaning |
|------|---------|
| **thunk** | a deferred computation; every value is one until forced |
| **force** `$` | evaluate a thunk to WHNF; the only way to observe a value (ADR-0007). bare `name` = description, `$name` = value. `(e)` *groups* without forcing; `$(e)` groups then forces. `!` is **not** force — it's actor-send |
| **`:` / `=`** | `:` introduces a binding (silent); `=` equates (live sync if RHS is a live description, sampled if `$`-forced). reactivity = equality over thunks (ADR-0005) |
| **effect row** | the set of effects a function may perform, carried in its type after `with`. composes by union |
| **handler** | a value implementing an effect's operations; installed with a `with` block; runtimes are handlers |
| **STM / TVar** | the one privileged primitive; transactional memory with journal/retry. TVars usable only inside `atomically` |
| **oracle** | the verified reference an implementation is checked against — the effect-row unifier *and* the reference `eval` (each calculated machine is diff-tested against `eval` via the harness) |
| **harness** | the differential tester that drives a candidate vs the oracle and reports disagreement |
| **calculated VM** | the `(compile, Code, exec)` triple *derived* from `eval` by Bahr–Hutton equational reasoning |
| **keyframe / rep** | a locked project state (K0–K7) / one delivered increment (rep 1 = the oracle) |
| **lowering** | an optional backend below the VM: C, Wasm, WasmFX, Effect TS |
| **resource trinity** | the framing that computation spends space/time/communication; `name` vs `$name` is the communication axis |

## How to verify (the cheapest orientation)

```
cd effectrow-oracle
nix develop          # ENTER THE DEV SHELL FIRST — bare `make`/`node`/`lake` are NOT on PATH
make selfcheck       # zero-dep algorithm check (Node only) — start here
make check-lean      # selfcheck → lake build → differential harness vs the Lean oracle (55 tests)
```

First `lake` build pulls Mathlib via `lake exe cache get` (network; minutes). Green
means you haven't broken invariant 1 (currently **55 tests green, zero `sorry`s**).
If you can express a new invariant as a runnable check, do that instead of writing it
in prose — checkable beats described.

## When you make a decision

If you make a choice that a future session could reasonably reverse or relitigate, **write an ADR** in `docs/decisions/` (copy the format of an existing one). Record the *rationale* and the *rejected alternatives*, not just the choice. Anti-drift is mostly anti-reversion, and reversion happens when the "why" is missing.
