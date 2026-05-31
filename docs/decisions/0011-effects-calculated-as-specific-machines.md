# ADR-0011 · Effects are calculated as specific machines (Throws→unwinding, State→register); tail-resumption only, reification deferred

- **Status:** Accepted
- **Date:** 2026-05-31
- **Related:** 0004 (calculate, don't hand-design), 0008 (the free-monad `eval` the effect ops mirror), 0009/0010 (the calculation method/staging this extends), roadmap K3 + §8 reading canon

## Context

K3 adds effects to the calculation. The earlier increments (K2: arithmetic →
closures → CBN) are the *pure* core; effects are the new axis. Two questions had
to be settled, and were (per the operator's choices + the papers):

1. **How are effects modelled in the source and machine** — a *general* algebraic
   handler mechanism, vs each effect *specifically* compiled? And does the machine
   need to **reify continuations** (capture the rest of the computation as data)?
2. **Which monad / divergence story** for the effect stage.

## Decision

- **Calculate each effect into a *specific* machine, surfaced through a general
  `perform`/`handle` (label-dispatched) source.** Following Hutton–Wright and
  Bahr–Hutton 2022 (each effect → its own instructions), not a single generic
  reified-continuation engine:
  - **Throws** (`Bang/CalcEff.lean`): the Hutton–Wright **exception machine,
    generalised to labelled handlers** — a runtime **handler stack** with
    `MARK`/`UNMARK`/`THROW` and **stack unwinding** (`unwindFind`). `raise` is
    **zero-shot** (discards its continuation).
  - **State** (`Bang/CalcSt.lean`): a **threaded state register** (Bahr–Hutton
    "swap to the State monad") — `GET`/`PUT`/`ENTER`/`LEAVE`. `get`/`put` resume
    **in tail position**.
- **Tail-resumption only; no explicit continuation reification.** Throws never
  resumes; State resumes in tail position (the register threads, the machine just
  continues). Neither needs to capture the continuation as data, so **neither
  does**. Multi-shot / non-tail resumption (the true general-handler frontier,
  Tsuyama 2024) is **deferred**.
- **Divergence story per effect.** Both effect sources are **total** (`CalcEff`
  short-circuits on `exc`; `CalcSt` always returns) — so `eval` is total and
  structural. `CalcSt`'s machine is even fuel-free (structural on code); `CalcEff`'s
  machine keeps fuel only because `THROW` jumps to recovery code.

## Rationale

- **Faithful to the papers** (ADR-0004's "calculate"): Hutton–Wright *is* the
  calculated exception machine; State-as-register *is* the monadic-calculation
  treatment of State. The instructions fall out of the `perform`/`handle` cases.
- **Tractable and provable.** Avoiding reification keeps both machines first-order
  and the proofs closed (`exec ∘ compile ≡ eval`, no `sorry`): `CalcEff` via a
  two-part ret/exc `sim` with an unwinding invariant; `CalcSt` via a direct
  structural equality.
- **Honest about the ceiling.** Tail-resumption covers `State`/`Throws` (and most
  of the design doc's library effects) but **not** multi-shot/non-tail handlers —
  named here so a fresh session doesn't mistake "general handlers" for "full
  reification already done."

## Rejected alternatives

| option | why not |
|--------|---------|
| **one generic reified-continuation engine now** (defunctionalize the resumption, à la Tsuyama 2024) | the real frontier; markedly harder, the proof would ship partial. Deferred — adopt when a non-tail/multi-shot effect actually needs it |
| **throw/catch baked in** (specific, not label-dispatched) | less general than `perform`/`handle`; the label-dispatch + forwarding generalises to more effects and to State |
| **partiality monad for the effect stage** (Bahr–Hutton 2022's divergence device) | effect sources here are total — no divergence to model. Fuel stays the device only where a machine jump needs it (`THROW`); consistent with the rest of the project's fuel choice |
| **integrate effects into `CalcCBN` immediately** | effects-on-the-closure-core is the harder *composition* step; calculate each effect over a minimal base first (ADR-0009 "one construct at a time"), compose later |

## Consequences

- Two new modules + oracle ops (`evaleff`/`execeff`, `evalst`/`execst`) + harness
  tests; both proven. No dedicated `Value` ADR needed — `CalcEff` is `Int`-valued
  with an `Outcome`; `CalcSt` is `Int`-valued with a state register.
- **Open / next:** (a) **compose** — effects on the closure/CBN core (swap the
  underlying monad on `CalcCBN`; merge `CalcEff`'s handler stack with closures);
  (b) **continuation reification** for multi-shot/non-tail handlers; (c) STM stays
  axiomatized (ADR-0003), never a handler.

## Revisit if

- A real effect needs **multi-shot or non-tail resumption** → introduce
  continuation **reification** (defunctionalize the resumption into machine data),
  the deferred frontier — as a calculated step, not a hand-designed engine.
- Composing effects with closures makes the *specific-per-effect* machines clash →
  reconsider a unified effect-monad machine (Bahr–Hutton 2022's "swap the monad" on
  the full core), still calculated.
