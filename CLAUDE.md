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
| the verified reference (K1 unifier) | `Bang/EffectRow.lean` (Lean 4 + Mathlib) |
| the reference `eval` (K2/K3 source) | `Bang/Eval.lean` |
| the wasmfx spec (graded CBPV + LR + WasmFX compiler) | `Bang/Spec.lean`, `Bang/Compat.lean`, `Bang/Audit.lean`, `Bang/Distribution.lean` |
| the calculated machines (K2/K3) | `Bang/{Calc, CalcHO, CalcCBN, CalcEff, CalcSt, CalcCBNEff, CalcCBNSt, CalcCBNEffSt}.lean` — all proven `exec ∘ compile ≡ eval` (see playhead table) · the reification frontier `Bang/CalcReify{,Ref,Sim}.lean` — machine + in-Lean denotational reference + bisimulation (pure core & first firing theorem proven; resuming case open) |
| **how to prove the next increment** | `docs/notes/k2-calculation-playbook.md` — fuel-alignment, mutual-induction & two-part-sim patterns, gotchas; **+ the K3 reification frontier section** (validation ladder, the `fuelOf`/`consK` ideas that unlocked firing handlers, the resuming residual). **Read before proving.** |
| the standing guarantee | `Bang/Audit.lean` + `tools/audit.sh` (axiom-hygiene gate) + `tools/selfcheck.mjs` (Node smoke test for the unifier algorithm). The TS differential harness was retired with the wasmfx merge (2026-06-21); see CONTEXT.md |
| what to read | reading canon, end of the roadmap `.md` |

## Current playhead

> **For the current session-level position, read `CONTEXT.md` first.** The
> K0–K3 playhead below is historical: ADRs 0010–0014 referenced in the K3
> machine table were collapsed into ADR-0017 (retrospective). ADR-0016
> (two-hop architecture) is the architecture in force.

**K0 locked · K1 done · K2 done · K3 in progress.** **Every theorem in the repo is proven — zero `sorry`s** (the repo asserts only what it proves). The verified reference `eval` exists; the VM is **calculated** from it (Bahr–Hutton). The **eight** core machines are each proven `exec ∘ compile ≡ eval` *and* differentially tested. The **ninth**, `CalcReify` (the reification frontier), is a working machine with its core behaviours `rfl`-verified and a real **bisimulation in progress** (`CalcReifySim`, against the in-Lean denotational reference `CalcReifyRef`): the pure core and the **first ∀-quantified firing-handler theorem** (`fire_agree`) are proven sorry-free; the *resuming-clause* case (the full step-indexed `vcont ↔ ek` relation) is the named, scoped residual in ADR-0015 — not faked.

**The reference:** `Bang/Eval.lean` — a fuel-bounded, total free-monad interpreter for the pinned core (thunk + `$`force, λ/app, `let`, ADTs+match, one-shot State/Throws handlers as a deep fold). Shape/rationale: **ADR-0008**. Effect labels reuse the K1 `EffectRow` `Finset` model.

**The calculated machines** — each proven `exec ∘ compile ≡ eval` (**no `sorry`**), each with an `{"op":…}` oracle op + a `harness/test/calc-*.test.ts` differential test:

| module | covers | convention | proof shape | ADR |
|--------|--------|-----------|-------------|-----|
| `Calc` | arithmetic, `let`/`var` | total, no fuel | direct equality, structural | 0009 |
| `CalcHO` | + λ/application (closures) | CBV, fuel | fuel-indexed `sim`; shared `vclo` ⇒ equality not a logical relation | 0017 |
| `CalcCBN` | + thunk/`$`force | call-by-name, fuel | **mutual** `eval`/`forceV` `sim`; matches `Bang.Eval` *exactly* | 0017 |
| `CalcEff` | general handlers, **Throws** | total `eval` / fuel machine | **two-part ret/exc `sim`**; handler stack + unwinding (`unwindFind`) | 0017 |
| `CalcSt` | **State** (`get`/`put`/`runState`) | total, no fuel | direct equality; threaded state register | 0017 |
| `CalcCBNEff` | **Throws over the closure core**: + λ/thunk/`$`force/CBN | fuel; `Option Outcome` | **four-part** mutual sim (`eval`/`forceV` × ret/exc); **forcing can raise**; re-throw `uncaught` at the meta-call boundary | 0017 |
| `CalcCBNSt` | **State over the closure core**: `get`/`put`/`runState` + the CBN core | fuel; `Option (Value × State)` | **two-part** mutual sim; register **threads cleanly** through the nested meta-runs (State resumes ⇒ no re-throw, no flatten) | 0017 |
| `CalcCBNEffSt` | **Throws *and* State together**: handler stack + register at once (the effect-row model) | fuel; `Option (Outcome × State)` | **four-part** mutual sim with state threaded; State **persists through a throw** (register threads through unwinding; rollback is STM's job) | 0017 |
| `CalcReify` | **reification** — multi-shot / non-tail handlers (one op, *flat* generalised-continuation machine) | fuel; `Kont` = list of frames; resumption = captured prefix as a `vcont` | machine + **7 `rfl` demonstrators** + fuel-monotonicity proven + **cross-checked vs an independent TS CPS interpreter (2k+ programs)** + **in-Lean denotational reference** (`CalcReifyRef`) + **bisimulation: pure core + first ∀-quantified firing theorem proven** (`CalcReifySim`: `pure_sim`/`fire_agree`). ⚠ a *resuming* clause proved generally still open (full `vcont↔ek` relation) — see ADR-0015 | 0015 |

Plus K1's `unify_sound` (proven — it needed a **freshness precondition**: `fresh` not already a row's tail var, else the open/open case binds a cyclic `some fresh`).

**Standing guarantee (post-wasmfx-merge):** the TS differential harness was retired (2026-06-21) — the calculated-machine zoo collapses into one graded-CBPV machine at ◊3 (ADR-0017), so the per-machine harness becomes obsolete. The standing gate is now `Bang/Audit.lean` (`#print axioms` ⊆ {propext, Classical.choice, Quot.sound}) + `tools/audit.sh` (static cheats grep + `lake build` clean) + `tools/selfcheck.mjs` (zero-dep Node smoke for the row unifier). Diff-testing returns when there's a graded-CBPV unified machine to test against.

**Method ↔ papers** (reading canon, roadmap §8): Bahr–Hutton 2022 *Monadic Compiler Calculation* (swap the monad) · Hutton–Wright *Compiling Exceptions Correctly* (the unwinding machine) · Pickard–Hutton 2021 (intrinsic, Lean-shaped). **Honest deltas (named, not hidden):** we use **fuel/`Option`**, not the partiality monad; artifacts are spec-guided definitions + a *post-hoc* `exec∘compile≡eval` proof (the derivation lives in the `-- derived, not designed` comments), not a mechanized step-by-step calculation; `CalcEff`/`CalcSt` exercise one-shot *tail* resumption / unwinding, **not** explicit continuation **reification**.

**Effect shape → composition mechanism** (the map that's now established):
- **zero-shot** (Throws) → nested meta-run with empty handler stack, **re-throw** at the boundary (`CalcCBNEff`, ADR-0012, proven; **forcing-can-raise** proven).
- **one-shot tail** (State) → **thread** the register through the nested meta-runs; no re-throw, no flatten (`CalcCBNSt`, ADR-0013, proven). This *answered* ADR-0012's open question: a resumable-in-tail effect does **not** force a machine flatten.
- **non-tail / multi-shot** → **flatten** to a control stack + **reify** the continuation as data (a captured prefix of the generalised continuation). The frontier — and the *only* thing that triggers the flatten. **Machine built + demonstrators verified + cross-checked vs an independent CPS interpreter:** `CalcReify`, ADR-0015 (in-Lean general theorem pending).
- **two effects at once** (Throws + State) → carry **both** apparatus (handler stack *and* register) in one machine; they interact by *persist* (state threads through unwinding; rollback is STM's job). Proven: `CalcCBNEffSt`, ADR-0014 — the effect-row model realized.

**Genuinely next** (none of this is done — *read the playbook + its K3 addendum first*):
- **`CalcReify`'s general theorem** — the machine is empirically validated (TS CPS interpreter, 2k+ programs) and the bisimulation is **underway**: the denotational reference exists in Lean (`CalcReifyRef`, CBPV + free monad, `rfl`-validated) and the **pure core** is proven sorry-free as a genuine machine-vs-reference agreement (`CalcReifySim`: `pure_sim`/`pure_correct`, plus `eval_pure`/`pure_correct_ref` tying `pden` to the real `CalcReifyRef.eval`), including **`handle` over a pure body** (unfired handler is transparent). The bisimulation has now broken into the **firing** cases: **`fire_agree`** proves the first ∀-quantified firing theorem — machine and reference agree on `handle clause (perform e)` for any pure `e` + pure non-resuming `clause` (zero-shot / payload-threading), enabled by an env-independent structural fuel bound (`fuelOf`) and the partial `RelEnv.consK` (opaque `vcont`↔`ek` slot). Plus `Agree` proves machine-vs-reference agreement by `⟨rfl,rfl⟩` on specific multi-shot/non-tail/re-handling programs. **The step-indexed `vcont ↔ ek` relation is now *formalized* in Lean, sorry-free** (`CalcReifySim`'s `Resuming` section): the opaque `consK` stub is replaced by a real `def RelV : Nat → Value → Entry → Prop` (def-not-inductive, structural recursion on the index) carrying the resumption agreement, plus the integration foundation (`relEnvI_lookup`, `bind_mono`, `relEnvI_forget`, `pure_sim_indexed`). The #1 definability risk is retired. **Four ∀-quantified *resuming* firing theorems are now proven** (sorry-free, by direct inside-out construction — the resumption is genuinely *invoked*, generally): `fire_resume_tail` (`handle (resume@1 v) (perform e) ≡ ⟦v⟧`, empty captured continuation), `fire_resume_nontail_body` (`handle (resume@1 v) (add (perform e) rest) ≡ ⟦v⟧+⟦rest⟧`, *non-empty* captured continuation — the 1007 demonstrator, now ∀-general), `fire_multishot` (`handle (add (resume@1 v1) (resume@1 v2)) (perform e) ≡ ⟦v1⟧+⟦v2⟧` — resume invoked **twice**), and **`fire_deep`** (`handle (resume@1 v) (add (perform e1) (perform e2)) ≡ w1+w2` — genuine **deep re-handling**: the resumed continuation itself performs and re-fires the handler; the 14 demonstrator, now ∀-general). Residual splits on a sharper axis (correcting "deep vs shallow"): **(A) fixed skeleton, ∀-general over pure subterms** — *including deep/re-handling* — is **direct-constructible** and now exercised end-to-end (`fire_deep`); the remaining (A) leaves (non-tail clause, multi-shot×non-empty, deeper skeletons) are more of the same. **(B) ∀-general over *all* `Src`** (full `exec ∘ compile ≡ run`) is the **remaining frontier**, needing `RelV`'s agreement (`capture_relates`). **Progress into (B):** `capture_relates_tail`/`capture_relates_add` prove a real PERFORM-captured `vcont` *satisfies* `RelV` for every one-shot capture (empty + non-empty pure) — first proof `RelV` is inhabited by real captures (non-vacuous, contravariance doesn't bite); also fixed a design bug (`RefK` `Int→Comp→Comp` → `Comp→Comp`) and added `pure_sim_back`. The general-simulation **architecture is designed (2nd design pass) and its viability PROVEN**: measure = the `RelV` step index (fuel existential, via `bind_mono`); continuation correspondence = observational `def RelKont` (built by composition, never by decompiling `Code`); predecessor-index headroom (env at `i+1`, conclusion at `i`). Proven sorry-free: `RelKont`/`relKont_nil`, `sim_pure_lift` (pure spine in the general shape), and **`sim_resume_pure_v`** — the `resume` case that genuinely *consumes* `RelV` at a resume node (the viability proof: headroom resolves the off-by-one, `RelKont` discharges `RelV`'s `RelK`, reference aligns). Remaining ladder: (a) `capture_relates_pure_general` + `relKont_pushPure`/`pushHandler` + `sim_structural` → the **shallow** `bisim_forward` (full ∀-`Src` forward bisim minus deep re-handling; all "hard", NO research gate — the guaranteed-reachable deliverable); (b) `perf_outcome_mono` (reference perf-outcome fuel-monotonicity — bisimulation-shaped, the research gate) → `capture_relates_deep` → the full bisim; (c) backward/iff is separate. *Read the playbook's K3 section first* — it has the reusable proof shapes (inside-out machine construction; `resume_empty_splice`; `eval_*` reduction lemmas; `rfl`-`have` to control eval-unfolding) and the contravariance/downward-closure caveat.
- **`runState` × throw** — the deferred sub-decision from the K3 capstone: when a throw escapes a `runState`, does the inner state leak or is the outer cell restored on unwind? (ADR-0014 "Revisit if".)
- **Reification ×** {outer-handler **forwarding** (2nd op), the **closure core**} — the harder reification follow-ups (ADR-0015 "Revisit if"); and a **user-extensible** effect set.
- **K4 front end** — parse → typed AST → effect-row inference on the verified unifier → core IR.
- **Deferred & documented** (in `Eval.lean`, never faked): multi-shot handlers, STM, `:`/`=` reactivity, divergence-beyond-fuel, nested deep patterns.

**Build:** `nix develop` gives Lean via elan; `lake exe cache get` pulls Mathlib oleans; `make verify` runs selfcheck + lake build + `tools/audit.sh` (axiom-hygiene gate). The lakefile lives at project root (`lakefile.toml`); the Lean library is `Bang` at `./Bang/`.

K0 decisions are locked — see ADRs. Do not relitigate locked decisions; read a decision's **"Revisit if"** clause first.

> **Architecture in force (third design revision):** the two-hop architecture
> from **ADR-0016** — graded-CBPV semantics → CalcVM (Bahr-Hutton) → WasmFX
> (Benton-Hur LR). ADRs 0003 and 0004 were deleted, subsumed by 0016. See
> also `ROADMAP.md` (orchestrator map) and `CONTEXT.md` (current position).

## Invariants — never break these

1. **Proof rides the reference.** Anything that runs is either `exec` itself or differential-tested against it. Never ship an execution path with no oracle behind it.
2. **Effect rows are sets** — idempotent, union = join. Never ordered, never a multiset. (ADR-0001)
3. **STM is the *only* privileged kernel primitive.** Everything else is effect + handler. (design doc; preserved by ADR-0016)
4. **The machine is an *output* of the calculation**, never hand-designed. Calculate, don't verify-after-the-fact. (ADR-0016, formerly ADR-0004)
5. **Kernel stays at five primitives:** thunk · force · effect rows · handlers · STM. Adding a sixth is a spec change requiring an ADR.
6. **No implicit capture; reactivity is the operator, not a keyword.** (ADR-0005, ADR-0006)
7. **Performance is second-class.** Optimize only where it touches the user; a slow correct path beats a fast unverified one.
8. **Effect TS is not the target.** The calculated VM is canonical; the WasmFX backend is the verified compiler target. (ADR-0016, formerly ADR-0004; supersedes ADR-0003)

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
nix develop          # ENTER THE DEV SHELL FIRST — bare `make`/`node`/`lake` are NOT on PATH
make verify          # selfcheck (Node) + lake build + tools/audit.sh
# or piecemeal:
make build           # lake exe cache get && lake build  (cold first time: minutes)
make audit           # bash tools/audit.sh  (depends on build; static cheat-grep + clean build)
lake env lean Bang/Audit.lean   # the REAL guarantee — `#print axioms` per headline theorem
```

First `lake` build pulls Mathlib via `lake exe cache get` (network; minutes). Green
means: zero `sorry` outside `Bang/Audit.lean`, no hand-rolled axioms, no `opaque`
surviving in `Bang/Spec.lean`, lake build clean, and every headline theorem's axiom
set ⊆ {`propext`, `Classical.choice`, `Quot.sound`}. If you can express a new
invariant as a runnable check, do that instead of writing it in prose — checkable
beats described.

## When you make a decision

If you make a choice that a future session could reasonably reverse or relitigate, **write an ADR** in `docs/decisions/` (copy the format of an existing one). Record the *rationale* and the *rejected alternatives*, not just the choice. Anti-drift is mostly anti-reversion, and reversion happens when the "why" is missing.
