# ADR-0013 · State composed with the closure/CBN core — `CalcCBNSt` (the register threads cleanly through the nested meta-runs; no flatten needed)

- **Status:** Accepted
- **Date:** 2026-05-31
- **Related:** 0012 (the Throws composition this parallels — and whose "Revisit if"
  this answers), 0011 (State as a register, `CalcSt`), 0010 (the CBN closure machine),
  0008 (the free-monad `eval`), 0009 ("one construct at a time"), roadmap K3

## Context

ADR-0012 composed *zero-shot Throws* with the closure/CBN core (`CalcCBNEff`) and
left an explicit open question (its "Revisit if"): does composing a **resumable**
effect — State — with the same core *clash* with `CalcCBN`'s nested-meta-`exec`
shape, forcing a flatten into a control-stack/CEK machine? This ADR settles it by
calculating State over the closure core.

The two questions the increment answers:

1. **Does the state register thread through the closure machine's nested meta-runs**
   (the `exec f (compile b []) … []` calls that `APP`/`FORCE` use to reduce a
   subterm to a value)?
2. **Does the lazy core interact with state correctly** — forcing a thunk runs a
   computation that may `get`/`put`, and an *unforced* thunk's effect must not
   happen?

## Decision

Calculate **State (`get`/`put`/`runState`) fused into the call-by-name closure/thunk
core** as `Bang/CalcCBNSt.lean` — Bahr–Hutton's "swap to the State monad" applied to
`CalcCBN`: its `Maybe` (the fuel device) composed with State, giving
`eval : Nat → State → Env → Src → Option (Value × State)` and
`forceV : Nat → State → Value → Option (Value × State)` (**forcing threads the
state**). `State = Int`, the single-cell model from `CalcSt` (ADR-0011).

- **The register threads cleanly through the nested meta-runs — no re-throw, no
  flatten.** Because State **resumes** (`get`/`put` continue in tail position), a
  called function / forced thunk simply takes the current state *in* and hands a new
  state *out*; the caller threads it forward. `APP`/`FORCE` run
  `exec f (compile b …) … [] st` and continue with the returned `st'`. This is the
  *opposite* of `CalcCBNEff`'s zero-shot re-throw: tail-resumption needs neither the
  empty-nested+re-throw trick nor a machine flatten.
- **`runState` localises the cell**, exactly as `CalcSt`: `ENTER`/`LEAVE` bracket the
  body, saving the outer state on the value stack (boxed as a `vint`) and restoring
  it on exit. Body runs from `init`; the outer register (the state after evaluating
  `init`) is restored. Composes with closures unchanged — the nested meta-runs inside
  the body just thread whatever the (local) register currently is.
- **`get`/`put`/`runState init` are forcing points** — the register is an `Int`, so
  `put`'s arg and `runState`'s init are forced to a `vint`; `get` pushes the register
  as a `vint`. `put`/`runState` therefore also exercise forcing-threads-state.
- **Arithmetic uses `add` only** (`mul` is a verbatim duplicate; ADR-0009).

## Rationale

- **Faithful to the papers** (ADR-0004): the monad-swap is Bahr–Hutton 2022;
  State-as-register is its State treatment; `ENTER`/`LEAVE` for `runState` come
  straight from `CalcSt`. The instructions are the *union* of `CalcCBN`'s and
  `CalcSt`'s — nothing hand-designed.
- **Provable, and simpler than the Throws composition.** `exec ∘ compile ≡ eval` is
  closed with **no `sorry`** via a **two-part** mutual simulation (eval-sim,
  forceV-sim, by induction on fuel) — `CalcCBN`'s mutual sim with the state register
  threaded and the `get`/`put`/`runState` cases added. No `exc` part (State never
  raises), so it is *one* part lighter than `CalcCBNEff`'s four-part sim. It went
  through **first try** using the playbook's K3 addendum (simp-only-not-`rw` for
  dependent scrutinees, pin `f'` before `omega`, `intro` on its own line).
- **It answers ADR-0012's open question.** Composing a tail-resumable effect with the
  closure core does **not** clash with the nested-meta-`exec` shape. So the flatten
  to a control-stack/CEK machine is **not** triggered by State — only by *non-tail /
  multi-shot* resumption (reification), as ADR-0011/0012 already said.

## The general picture (effect shape → composition mechanism)

| effect shape | composition with the closure core | example |
|--------------|-----------------------------------|---------|
| **zero-shot** (abandons continuation) | nested meta-run with empty handler stack, **re-throw** `uncaught` at the boundary | Throws (`CalcCBNEff`, ADR-0012) |
| **one-shot tail** (resumes in tail position) | **thread** the register through the nested meta-runs; no re-throw | State (`CalcCBNSt`, this ADR) |
| **non-tail / multi-shot** (reifies the continuation) | **flatten** to a control stack + reify the resumption | deferred (Tsuyama 2024; ADR-0011/0012) |

## Rejected alternatives

| option | why not |
|--------|---------|
| **flatten the machine to a control stack now** (anticipating reification) | unnecessary for State — tail-resumption threads through the existing nested-meta-`exec` shape. Flatten when *reification* actually needs it (the table's third row), not before |
| **drop `runState`, do `get`/`put` over a global cell** | `runState` is State's *handler*; without it the composition wouldn't show the scoped effect interacting with closures. `CalcSt` already had `ENTER`/`LEAVE`, so it composed at low extra cost |
| **make the state a `Value` (avoid forcing `put`/`init`)** | the register is a scalar `Int` (matches `CalcSt`/ADR-0011); boxing arbitrary values as state has no use here and complicates `ENTER`/`LEAVE` |

## Consequences

- One new module (`Bang/CalcCBNSt.lean`, proven) + oracle ops
  (`evalcbnst`/`execcbnst`) + a `harness/test/calc-cbn-st.test.ts` differential test
  (goldens for state-through-a-call, forcing-threads-state, laziness-suppresses-an-
  effect, `runState` localisation, plus a 500-run fuzz). 77 tests green.
- **Open / next:** (a) **compose Throws *and* State together** over the closure core
  (two effects + the handler stack + the register at once) — or generalise to a
  user-extensible handler set; (b) **continuation reification** for multi-shot /
  non-tail handlers — the deferred frontier, and the only thing that triggers the
  flatten; (c) STM stays axiomatized (ADR-0003); (d) K4 front end.

## Revisit if

- A **non-tail or multi-shot** handler is needed → reification + the control-stack
  flatten (the table's third row); this is the genuine frontier, unchanged by State.
- Composing **multiple effects at once** makes the per-effect machines (handler stack
  *and* register *and* …) clash → reconsider a single unified effect-monad machine
  over the full core (Bahr–Hutton's "swap the monad" on everything), still calculated.
