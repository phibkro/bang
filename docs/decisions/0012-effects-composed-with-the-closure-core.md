# ADR-0012 · Effects composed with the closure/CBN core — Throws fused into `CalcCBNEff` (zero-shot, re-throw at the meta-call boundary)

- **Status:** Accepted
- **Date:** 2026-05-31
- **Related:** 0011 (effects as specific machines — this composes one of them with the
  core), 0010 (the CBN closure machine this fuses into), 0008 (the free-monad `eval`),
  0009 ("one construct at a time"), roadmap K3

## Context

ADR-0011 calculated each effect over a *minimal* base (Throws over arithmetic+`let`;
State over the same). The pure core (K2) — closures, thunks, `$`force, call-by-name —
was calculated *separately* (`CalcCBN`, ADR-0010). The two fragments were disjoint:
the effect machines were `Int`-valued with no closures; the closure machine had no
effects. The "real K3" is **effects *over* the closure/CBN core** — and it is the
biggest open step because composing the two raises a genuinely new question that
neither parent exercised, plus a machine-shape clash.

1. **The new semantic interaction: forcing can raise.** In a lazy language, forcing a
   thunk runs a suspended computation that may itself `perform`/`throw`. So `forceV`
   must thread effects, and every *forcing point* (`$e`, both `add` operands, the
   function position of an application, a `perform` payload) becomes an
   effect-propagation point. This is where any bug hides; the pure fragments never
   tested it.
2. **The machine-shape clash.** `CalcCBN`'s APP/FORCE evaluate a subterm to a value
   via a *nested meta-level* `exec` (run the body, extract the stack top). A `THROW`
   is a *non-local jump* that cannot cross that meta-boundary.

## Decision

Calculate **Throws fused into the full CBN closure core** as a single new module,
`Bang/CalcCBNEff.lean` — Bahr–Hutton's "swap the underlying monad" applied to
`CalcCBN`: its evaluation monad `Maybe` (`Option`, the fuel/divergence device) is
composed with the exception monad `Outcome`, giving
`eval : Nat → Env → Src → Option Outcome` and (the key) `forceV : Nat → Value →
Option Outcome` (**forcing returns an `Outcome` and can raise**).

- **Zero-shot Throws only, this increment.** Scope is the exception effect (ADR-0009,
  one construct at a time). State-over-closures and continuation reification stay
  separate, harder steps (below).
- **Re-throw at the meta-call boundary.** The machine resolves the shape clash — and
  this is clean **only because `raise` is zero-shot** (it abandons its continuation):
  each nested meta-`exec` (APP body, FORCE-of-thunk) runs with a **fresh empty handler
  stack**; if it returns `uncaught ℓ p`, the boundary **re-throws** against the live
  (outer) handler stack via `unwindFind`. Because the nested computation is abandoned
  on a throw anyway, empty-nested + re-throw is provably equivalent to dynamic
  scoping, and keeps each frame's recovery code in the stream that owns it.
- **`add` forces both operands before the int-check.** The machine emits
  `compile x (FORCE :: compile y (FORCE :: ADD :: c))` — both operands are forced
  (each can raise) and the type-check happens *at* `ADD`. So `eval`'s `add` must do
  the same: a non-int operand is stuck (`none`) only *after* the other operand's
  effects have run. (The first cut checked int-ness too eagerly; the differential
  fuzzer caught the divergence — see Consequences.)
- **Arithmetic uses `add` only.** `mul` would be a verbatim duplicate of `add`'s
  effect-threading — proof bulk, no new content (ADR-0009 simplicity).

## Rationale

- **Faithful to the papers** (ADR-0004 "calculate"): the monad-swap is Bahr–Hutton
  2022; the handler stack + unwinding is Hutton–Wright (generalised to labels, as in
  ADR-0011). The instructions are the *union* of `CalcCBN`'s and `CalcEff`'s; nothing
  new is hand-designed — the re-throw falls out of the nested-`exec` boundary.
- **Provable.** `exec ∘ compile ≡ eval` is closed with **no `sorry`** via a **four-part
  mutual simulation** (eval-ret, eval-exc, forceV-ret, forceV-exc, by induction on
  fuel) — the fusion of `CalcCBN`'s mutual `eval`/`forceV` simulation and `CalcEff`'s
  two-part ret/exc simulation. The one new ingredient is the nested-`uncaught` cases
  (a called function / forced thunk whose body raises returns `uncaught` from the
  nested run, which the boundary re-throws).
- **Honest about the ceiling.** Empty-nested + re-throw works for *zero-shot*. It is
  *not* a general resumable-handler machine — named here so a fresh session doesn't
  mistake "effects over closures" for "full algebraic effects done."

## Rejected alternatives

| option | why not |
|--------|---------|
| **flatten the CBN machine into a CEK/control-stack machine** (so `THROW` unwinds uniformly, no boundary re-throw) | a much larger redesign that changes the whole proof technique; deferred (ADR-0011). For zero-shot Throws, nested-`exec` + boundary re-throw is the minimal delta from `CalcCBN` and reuses its proof shape |
| **pass the live `hs` into the nested meta-run** (instead of `[]` + re-throw) | *incorrect*: a frame's recovery code belongs to the outer instruction stream, so running it inside a nested `exec … []` that expects a single return value is ill-formed. Empty-nested + re-throw keeps recovery in the owning stream |
| **fold in State this increment too** | State-over-closures needs register threading through the nested calls — a distinct subtlety; calculate one effect over the composed core first (ADR-0009) |
| **a general reified-continuation engine now** | the real frontier (Tsuyama 2024); markedly harder, would ship partial. Adopt when a non-tail/multi-shot effect actually needs it |

## Consequences

- One new module (`Bang/CalcCBNEff.lean`, proven) + oracle ops
  (`evalcbneff`/`execcbneff`) + a `harness/test/calc-cbn-eff.test.ts` differential test
  (goldens for the new interactions — effect escaping a call, forcing-raises,
  laziness suppressing an effect — plus a 500-run fuzz). 66 tests green.
- **The harness earned its keep.** Built defs-first, the fuzz immediately found the
  eager-int-check divergence in `add` *before* any proof effort was spent — exactly
  the "run the real journey" payoff. Fixed, then proved.
- **Open / next:** (a) **State over the closure core** — thread the register through
  the nested meta-runs; (b) **continuation reification** for multi-shot/non-tail
  handlers (still deferred, ADR-0011); (c) STM stays axiomatized (ADR-0003).

## Revisit if

- **State-over-closures** (or any resumable effect) makes the empty-nested + re-throw
  shape clash with resumption → that is the trigger to **flatten** the machine into a
  control-stack (CEK-style) form, as a calculated step — the rejected alternative
  above becomes the right move once an effect actually resumes across a call boundary.
- A multi-shot/non-tail handler is needed → introduce continuation **reification**
  (ADR-0011's deferred frontier).
