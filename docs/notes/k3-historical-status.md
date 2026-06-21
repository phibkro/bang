# K3 historical status (pre-ADR-0016 narrative)

> **Historical archive.** This was the K0–K3 playhead before the third
> design revision (ADR-0016, 2026-06-20) pivoted to graded-CBPV + WasmFX.
> Preserved here because the K3 work IS real, proven, and its *insights*
> (especially the effect-shape → composition-mechanism map) carry forward.
>
> For CURRENT direction: read `CLAUDE.md` → `CONTEXT.md` → ADR-0016.
> For the retrospective that captures the durable lessons:
> `docs/decisions/0017-k3-calculated-machine-retrospective.md`.

## The K0–K3 playhead

**K0 locked · K1 done · K2 done · K3 was in progress at the pivot.**
Every theorem in the repo at the time was proven — zero `sorry`s. The
verified reference `eval` exists; the VM is calculated from it
(Bahr–Hutton). Eight core machines proven `exec ∘ compile ≡ eval` plus a
ninth (`CalcReify`) with bisimulation in progress.

## The eight proven calculated machines

| module | covers | convention | proof shape |
|--------|--------|-----------|-------------|
| `Calc` | arithmetic, `let`/`var` | total, no fuel | direct equality, structural |
| `CalcHO` | + λ/application (closures) | CBV, fuel | fuel-indexed `sim`; shared `vclo` ⇒ equality not a logical relation |
| `CalcCBN` | + thunk/`$`force | call-by-name, fuel | mutual `eval`/`forceV` `sim`; matches `Bang.Eval` exactly |
| `CalcEff` | general handlers, **Throws** | total `eval` / fuel machine | two-part ret/exc `sim`; handler stack + unwinding |
| `CalcSt` | **State** (`get`/`put`/`runState`) | total, no fuel | direct equality; threaded state register |
| `CalcCBNEff` | Throws over the closure core | fuel; `Option Outcome` | four-part mutual sim; forcing can raise; re-throw at meta-call boundary |
| `CalcCBNSt` | State over the closure core | fuel; `Option (Value × State)` | two-part mutual sim; register threads cleanly through nested meta-runs |
| `CalcCBNEffSt` | Throws *and* State together | fuel; `Option (Outcome × State)` | four-part mutual sim with state threaded; State persists through a throw |
| `CalcReify` | reification — multi-shot / non-tail handlers | fuel; `Kont` = list of frames | machine + 7 `rfl` demonstrators + cross-checked vs TS CPS interpreter (2k+ programs) + in-Lean denotational reference + bisimulation (pure core + first ∀-quantified firing theorem proven) |

Plus K1's `unify_sound` (proven — needed a freshness precondition).

## The effect-shape → composition-mechanism map (the load-bearing insight)

This is the durable intellectual output of K3 work. Carries forward into
any future calculated-VM work; preserved in ADR-0017.

- **zero-shot** (Throws) → nested meta-run with empty handler stack;
  **re-throw** `uncaught` at the boundary (`CalcCBNEff`)
- **one-shot tail** (State) → **thread** the register through the nested
  meta-runs; no re-throw, no flatten (`CalcCBNSt`). This *answered* the
  open question "does composing State force a CEK-style flatten?" — no,
  it doesn't; only reification does
- **non-tail / multi-shot** → **flatten** to a control stack + **reify**
  the continuation as data (a captured prefix of the generalised
  continuation). The frontier — and the *only* thing that triggers the
  flatten
- **two effects at once** (Throws + State) → carry **both** apparatus
  (handler stack + register) in one machine; they interact by *persist*
  (state threads through unwinding; rollback is STM's job)

## Method ↔ papers

- Bahr–Hutton 2022 *Monadic Compiler Calculation* (swap the monad)
- Hutton–Wright *Compiling Exceptions Correctly* (the unwinding machine)
- Pickard–Hutton 2021 (intrinsic, Lean-shaped)

Honest deltas at the time: fuel/`Option` not partiality monad; artifacts
are spec-guided definitions + post-hoc `exec∘compile≡eval` proof, not a
mechanized step-by-step calculation; `CalcEff`/`CalcSt` exercise one-shot
*tail* resumption / unwinding, NOT explicit continuation reification.

## What was active before the pivot (ADR-0016 paused / superseded)

- **`CalcReify`'s general theorem** — bisimulation was underway; pure
  core + first ∀-quantified firing theorem proven (`fire_agree`,
  `fire_resume_tail`, `fire_resume_nontail_body`, `fire_multishot`,
  `fire_deep`); step-indexed `RelV` formalized; `sim_resume_pure_v`
  proven. The general-simulation architecture (RelKont composition,
  predecessor-index headroom) was designed + viability proven. **Phase
  PAUSED per ADR-0016** — the Benton-Hur logical relation in the
  graded-CBPV spec subsumes the goal.
- **`runState` × throw** — deferred sub-decision from the K3 capstone:
  when a throw escapes a `runState`, does the inner state leak or is
  the outer cell restored on unwind? Documented in OPEN_QUESTIONS.md.
- **Reification × outer-handler forwarding** (2nd op), **the closure
  core** — harder reification follow-ups, also paused.
- **K4 front end** — replaced by the two-hop architecture's surface
  layer (◊5+ in the new ROADMAP.md).
- **Deferred & documented** at the time: multi-shot handlers, STM,
  `:`/`=` reactivity, divergence-beyond-fuel, nested deep patterns.

## How this work informs current Phase A part 2 / Phase B

- The **effect-shape → composition map** above is THE algebraic insight
  to keep. It tells you, for a given handler shape, what runtime
  apparatus is needed. Useful when designing `Bang/Operational.lean`'s
  `Source.step` rules for new handler types.
- The **fuel-bounded totality discipline** carries over: graded-CBPV
  `Source.eval` uses the same `Nat`-fuel pattern.
- The **mutual induction proof shapes** in `Bang/Calc*.lean` (eval/forceV
  two-part sim, ret/exc separation) are reusable patterns for the
  step-indexed LR work in Phase B PROOF_ORDER #1.
- The **calc machines themselves** will collapse into one graded-CBPV
  unified machine at ◊3; their proofs become historical evidence the
  methodology works.
