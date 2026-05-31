# AGENTS.md — read this first

You are a fresh session. **This repo is your only memory.** Anything not written here did not happen. Read this file, then the roadmap, then the ADRs, before changing anything.

## What BANG is

A small language whose **paradigm and runtime are values, not language features**. The kernel is thunks + effects + STM; everything else (mutability, IO, async, actors, signals) is ordinary library code over it. Programs are **descriptions** until forced with `!`; a function's **paradigm** is which effects are in its row; a program's **runtime** is a handler installed at the use site.

## Repo map

| you need… | go to |
|-----------|-------|
| what the language *is* | `docs/spec/bang-lang-design.md`, `docs/spec/bang-lang-description-value.md` |
| where the project is going | `docs/roadmap/bang-northstar-roadmap.md` (dense) · `.html` (visual) |
| **why** things are the way they are | `docs/decisions/` (ADRs) — read these before proposing changes |
| the verified reference | `effectrow-oracle/oracle-lean/Bang/EffectRow.lean` (Lean 4 + Mathlib) |
| the calculated VM (K2) | `effectrow-oracle/oracle-lean/Bang/{Calc,CalcHO}.lean` (proven `exec ∘ compile ≡ eval`) |
| **how to prove the next K2 increment** | `docs/notes/k2-calculation-playbook.md` — fuel-alignment, tactic patterns, gotchas. **Read before proving.** |
| the standing guarantee | `effectrow-oracle/harness/` (differential tests) + `effectrow-oracle/tools/selfcheck.mjs` |
| what to read | reading canon, end of the roadmap `.md` |

## Current playhead

**K1 done** (effect-row oracle: verified unifier + harness). **K2 in progress** — the `eval` reference exists *and the calculation has started*: a stack machine is calculated + **proven** for the arithmetic kernel. The full VM (closures, effects) is not done yet.

- **Reference:** `oracle-lean/Bang/Eval.lean` — a fuel-bounded, total free-monad interpreter for the pinned core (thunk + `$` force, λ/app, `let`, ADTs + match, one-shot State/Throws handlers as a deep fold). Shape & rationale: **ADR-0008**. Effect labels reuse the `EffectRow` `Finset` model.
- **Calculated VM — first-order, PROVEN:** `oracle-lean/Bang/Calc.lean` — K2 increments **1 (arithmetic `val/add/mul`)** + **2 (`let`/`var`, de Bruijn → runtime env + `LOOKUP/BIND/UNBIND`)**. `compile`/`exec`/`Instr` *derived* from `eval`; `exec ∘ compile ≡ eval` **proven, no `sorry`** (`exec_compile`, `compile_correct`). Approach/staging: **ADR-0009**.
- **Calculated VM — higher-order, PROVEN:** `oracle-lean/Bang/CalcHO.lean` — K2 increment **3 (`λ`/application, closures)**. Fuel-bounded, CBV, `Value = vint | vclo Src Env` (source-closures shared with `eval`). `compile_correct` (`exec ∘ compile ≡ eval` for closures) is **proven, no `sorry`** — a fuel-indexed simulation (`sim`) resting on fuel-monotonicity (`exec_succ`/`exec_mono`); the shared `vclo` keeps it an equality, not a logical relation. *Also* diff-tested green vs `eval`. Decisions/proof: **ADR-0010**.
- **Harness:** `Bang/EvalJson.lean` ops — `{"op":"eval"}` (interpreter), `{"op":"exec"}` (proven first-order machine), `{"op":"execho"}` (proven HO machine). `harness/` drives an independent TS candidate (`eval-candidate.ts`) on eval goldens + fuzz, and diff-tests each machine vs `eval` (`test/calc.test.ts`, `test/calc-ho.test.ts`). **31 tests green.**
- **One `sorry` left in the whole build:** `unify_sound` (K1, with a proof plan). Everything else — including the entire K2 calculation so far — builds clean and proven.
- **Deferred (documented in `Eval.lean`, never faked):** multi-shot handlers, STM, `:`/`=` reactivity, divergence-beyond-fuel, nested deep patterns.
- **Next (grow the calculation — read `docs/notes/k2-calculation-playbook.md` first):** thunk/`$`force + call-by-name (BANG's actual kernel — `CalcHO` is CBV; reuse its closure machinery, change the arg convention to thunks) → `if` (after a Bool/value story so it diff-tests vs `Bang.Eval`) → effects (swap in the effect monad; the free-monad `eval`'s resumption defunctionalizes into the machine). Optionally also discharge `unify_sound`. The playbook has the fuel-alignment trick, the tactic patterns, and the gotchas that cost real time.
- **In-sandbox build note:** the Lean oracle compiles and `check-lean` is green (the persistent-process harness needed a stdout flush; three Mathlib-version NUDGE spots were fixed). `nix develop` gives Lean via elan; `lake exe cache get` pulls Mathlib oleans.

K0 decisions are locked — see ADRs. Do not relitigate locked decisions; if you think one is wrong, read its **"Revisit if"** clause first.

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
| **oracle** | the verified reference an implementation is checked against (currently the effect-row unifier; later `eval`/`exec`) |
| **harness** | the differential tester that drives a candidate vs the oracle and reports disagreement |
| **calculated VM** | the `(compile, Code, exec)` triple *derived* from `eval` by Bahr–Hutton equational reasoning |
| **keyframe / rep** | a locked project state (K0–K7) / one delivered increment (rep 1 = the oracle) |
| **lowering** | an optional backend below the VM: C, Wasm, WasmFX, Effect TS |
| **resource trinity** | the framing that computation spends space/time/communication; `name` vs `$name` is the communication axis |

## How to verify (the cheapest orientation)

```
cd effectrow-oracle
make selfcheck     # zero-dep algorithm check (Node only) — start here
make check-lean    # selfcheck → lake build → differential harness vs the Lean oracle
```

Green means you haven't broken invariant 1. If you can express a new invariant as a runnable check, do that instead of writing it in prose — checkable beats described.

## When you make a decision

If you make a choice that a future session could reasonably reverse or relitigate, **write an ADR** in `docs/decisions/` (copy the format of an existing one). Record the *rationale* and the *rejected alternatives*, not just the choice. Anti-drift is mostly anti-reversion, and reversion happens when the "why" is missing.
