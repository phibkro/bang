# ADR-0022 · Effect operations: the `up` rule, operation signatures, and label-discharging `handle`

- **Status:** Proposed (design lock for the up-rule arc; implementation staged below)
- **Date:** 2026-06-22
- **Layer:** K (kernel — typing rules, the effect-signature interface, the operational/typing tie for handlers)
- **Resolves:** OPEN_QUESTIONS Q5 (`up` typing rule + opArgTy/opResTy); **completes** Q4 (label-removing `handle`, partially landed in ADR-0021); informs Q7 (op names)
- **Builds on:** ADR-0018 (lacks-constrained rows), ADR-0019/0020 (graded de Bruijn context), ADR-0021 (the STD block + the effect-on-judgment discipline this extends)
- **Reference:** algebraic-effect operation typing (Lexa OOPSLA'24 operational shape; Frank/Eff/Koka signature discipline). Torczon's CBPV has only `tick` (no operation alphabet), so this is *additive* to the port, not a port of it.

## Context

The kernel **cannot currently type any effectful program**: `Comp.up ℓ op v` (perform
operation `op` of effect `ℓ`) has no typing rule (Q5), so `HasCTy` derivations never
contain an `up`. Every effect-soundness theorem (`no_accidental_handling`, `effect_sound`)
is therefore **vacuous** — there are no operations to reason about. Closing ◊2's headline
requires operations to be real.

Adding `up` is not a local change — it is a coupled arc, because of three knock-ons that
re-touch the just-proven STD block (ADR-0021):

1. **`up` needs operation signatures.** `up ℓ op v : F q (resultTy)` only typechecks if `v`
   has `op`'s argument type and the rule knows `op`'s result type. The kernel has no
   per-operation signature — `opArgTy`/`opResTy` are unused `Eff → VTy` axioms in `LR.lean`,
   and they are per-*effect*, not per-*operation* (they cannot give `State`'s `get` and `put`
   different types). A real per-`(Label, OpId)` signature is needed.

2. **An unhandled `up` is a stuck normal form.** `up ℓ op v` (no enclosing handler) is a
   closed, `F`-typed computation that neither `step`s nor is a `ret` — exactly the shape that
   broke `progress` for `lam` in ADR-0021 (C2/C4). So `progress`/`type_safety` must be stated
   at effect **`⊥`** (a *fully handled* program), where — given a law that a label's effect is
   never `⊥` — no `up` can be typed, restoring progress.

3. **Reaching `⊥` requires `handle` to discharge its label.** ADR-0021 left `handle` same-φ.
   For a program to be typeable at `⊥` (so progress applies) and for `effect_sound` to hold,
   `handle h M` must *remove* `h`'s handled label from the row. This completes Q4 and makes the
   `handle (throws ℓ) (up ℓ "raise" v) ↦ ret v` reduction (and the `state` ones) type-preserving
   — which the STD-block preservation proof currently discharges as *vacuous* (because `up` is
   untypable) and will have to prove *for real*.

So: signatures + `up` rule + progress-at-`⊥` + label-discharging `handle` + handler typing
must land as **one coherent unit**; the first commit breaks green and it stays red until the
unit closes. Hence this ADR locks the design before any code, and stages the implementation so
the green-breaking work is isolated and bounded.

## Decision

### D1 — Operation signatures as a typeclass `EffSig`

```lean
class EffSig (Eff Mult : Type) [Lattice Eff] [OrderBot Eff] where
  labelEff      : Label → Eff                       -- the singleton effect of a label
  opArg         : Label → OpId → VTy Eff Mult       -- operation argument type
  opRes         : Label → OpId → VTy Eff Mult       -- operation result type
  labelEff_ne_bot : ∀ ℓ, labelEff ℓ ≠ (⊥ : Eff)     -- a label's effect is non-empty
```

Carried in the `variable` block alongside `[Lattice Eff] [OrderBot Eff] [CommSemiring Mult]`,
so it threads into `HasCTy`/`HasVTy` and the theorems via Lean's section-variable mechanism —
existing proofs gain an instance argument but their *bodies* are unchanged. The signature is a
fixed *interface* (the program's effect declarations), parametric so the kernel stays general.
Concrete instance for `EffRow = Finset Label`: `labelEff ℓ = {ℓ}` (so `labelEff_ne_bot` is
`Finset.singleton_ne_empty`); `opArg`/`opRes` from the program's `effect` declarations.

- *Rejected:* per-effect `opArgTy : Eff → VTy` (current axioms) — cannot distinguish two
  operations of the same effect (`get`/`put`). *Rejected:* signature in the typing context —
  heavier, and operation signatures are global, not scoped.

### D2 — The `up` typing rule

```lean
| up : ∀ {γ Γ ℓ op v q},
    EffSig.labelEff ℓ ≤ φ →
    HasVTy γ Γ v (EffSig.opArg ℓ op) →
    HasCTy (q • γ) Γ (Comp.up ℓ op v) φ (CTy.F q (EffSig.opRes ℓ op))
```

`labelEff ℓ ≤ φ` is the lacks-discipline membership ("`ℓ ∈ φ`", ADR-0018) expressed in the
abstract `[Lattice Eff]` algebra. Grade `q • γ` mirrors `ret` (the produced value's budget `q`
scales the argument's grade) — **flagged**: confirm against the `subst`/preservation arithmetic
when implementing; if the operation should consume its argument linearly use `γ` instead.

### D3 — `progress` / `type_safety` restated at effect `⊥`

```lean
theorem progress    : HasCTy [] [] c ⊥ (CTy.F q A) → isReturn c ∨ ∃ c', Source.step c = some c'
theorem type_safety : HasCTy [] [] c ⊥ (CTy.F q A) → ∀ fuel, Source.eval fuel c ≠ Result.stuck
```

At `⊥`, `up` is untypable (`labelEff ℓ ≤ ⊥` ⇒ `labelEff ℓ = ⊥`, contradicting
`labelEff_ne_bot`), so the new `up` normal form never arises and the generalized-terminal
argument from ADR-0021 still collapses to `isReturn ∨ steps`. This is the correct meaning of a
*runnable* program: all effects discharged. (`preservation` stays at general `e` — it must hold
mid-reduction where the row is non-empty.)

### D4 — `handle` discharges its label (completes Q4)

```lean
| handle : ∀ {γ Γ h M ℓ e φ q A},
    HasHandler h ℓ →                                 -- h handles label ℓ
    HasCTy γ Γ M e (CTy.F q A) →                     -- body uses effect e
    e ≤ EffSig.labelEff ℓ ⊔ φ →                       -- e is within ℓ plus residual φ (SUBSUMPTION)
    HasCTy γ Γ (Comp.handle h M) φ (CTy.F q A)        -- ℓ dischargeable from the row
```

**Effect subsumption (`≤`), not equality** — a `ret v` body has effect `⊥`, which cannot
*equal* `labelEff ℓ ⊔ φ`; the body uses *at most* `ℓ` plus residual `φ`. The derivation picks
`φ`; choosing `φ` without `ℓ` discharges `ℓ`, and nesting one handler per label drives a closed
program to `⊥`. This supersedes ADR-0021's same-φ `handle`. (This is the kernel's first effect
*subsumption*; it lives in the `handle` rule, not as a free-standing `T_SubEff`, so it stays
localized.)

### D5 — Handler typing `HasHandler h ℓ`

`h` correctly implements label `ℓ`'s operations *for the simplified (Q6) `Source.step`
semantics* — identity return clauses, zero-shot, no continuation capture. Matching those four
reductions pins the signature shape (these constraints are Q6 artifacts a future CK machine
removes — Q6's revisit):

```lean
inductive HasHandler : Handler → Label → Prop where
  | throws : ∀ {ℓ},
      -- raise returns its payload as the block result ⇒ arg = result type
      EffSig.opArg ℓ "raise" = EffSig.opRes ℓ "raise" →
      HasHandler (Handler.throws ℓ) ℓ
  | state  : ∀ {ℓ s},
      -- State shape: get : Unit→S, put : S→Unit, with S the stored-state type
      EffSig.opRes ℓ "get" = EffSig.opArg ℓ "put" →        -- = S
      EffSig.opArg ℓ "get" = VTy.unit →
      EffSig.opRes ℓ "put" = VTy.unit →
      HasVTy (GradeVec.zeros 0) [] s (EffSig.opRes ℓ "get") →  -- stored state s : S, CLOSED
      HasHandler (Handler.state ℓ s) ℓ
```

The **closedness of `s`** (typed in `[]`, grade `zeros 0`) is load-bearing: the `get` reduction
`handle (state ℓ s)(up ℓ "get" u) ↦ handle (state ℓ s)(ret s)` replaces `up`'s unit-arg `u`
(grade `zeros`) with `s`; preservation's grade matches only because both are `zeros`. (`s` is
weakened to the ambient context as needed via `HasVTy.weaken`, already proven.)

### D5′ — `up`'s closed-handler payload note

`Handler.state`/`throws` carry a `Val` that is *substituted/shifted* like any value
(`Handler.substFrom`/`shiftFrom`, already defined). `HasHandler` types it closed; under
substitution the handler's `s` is unaffected (closed values shift to themselves), so the
existing `HasCTy.weaken`/`subst_gen` handle cases extend without new binder reasoning.

### D6 — STD-block re-proof obligations (the green-breaking work)

- `preservation`: new `up` leaf case (bare `up` doesn't `step` ⇒ `none` ⇒ vacuous *unless under
  handle*); the `handle` head-redex cases (`throws`/`state`×`get`/`put`) become **non-vacuous**
  and must be proven type-preserving via `HasHandler` + the signature. The `handle` search case
  re-proves under the label-discharging rule.
- `progress`: `up` excluded at `⊥` (D3); `handle` case uses D4.
- `type_safety`: fuel induction over the `⊥` `progress` + `preservation`.

## Implementation staging

```
Unit 1 (green, isolated)   EffSig typeclass + Finset instance; replace the opArgTy/opResTy
                           axioms. No up rule yet ⇒ STD block untouched ⇒ stays green.
Unit 2 (breaks green       up rule (D2) + handle→label-discharging (D4) + HasHandler (D5) +
 until it closes)          progress/type_safety→⊥ (D3) + re-prove the STD cases (D6).
Unit 3                     no_accidental_handling + effect_sound now NON-vacuous (operations
                           exist, handlers discharge) — the ◊2 headline.
```

Each unit is a commit; Unit 2 is the one that must land whole. `zero_usage_erasable` stays
deferred to ◊4 (LR-flavored; Torczon proves it semantically).

## Rejected alternatives

| option | why not |
|--------|---------|
| Keep `up` untypable; prove `no_accidental_handling` vacuously | A green theorem that lies — the exact anti-pattern the proof discipline forbids. ◊2's headline must have content. |
| Effect signature baked into `Eff` (operations as part of the row algebra) | Conflates the row lattice with the operation alphabet; breaks the clean `[Lattice Eff]` abstraction and ADR-0001/0018. A separate `EffSig` interface keeps the algebra pure. |
| Keep `progress` at general `e`, treat unhandled `up` as a third terminal | An unhandled operation is *not* a value — calling it "terminal" would make `type_safety` claim a stuck program is safe. `⊥` (fully handled) is the honest runnable-program precondition. |
| Keep `handle` same-φ (ADR-0021 stopgap) | Then no closed program reaches `⊥`, progress is unprovable, and `effect_sound` is false (the row never shrinks). Label-discharge is mandatory, not cosmetic. |

## Revisit if

- Multi-shot / deep-resumption handlers (Q6) are needed: the `Source.step` handler semantics
  move to a CK machine (the `Frame`/`EvalCtx` infra exists); `HasHandler` extends, the typing
  shape here does not revert.
- Operation names go symbolic (Q7): `opArg`/`opRes` re-key from `OpId = String` to an enum;
  `EffSig` is the single place that changes.
- A genuinely linear operation argument is wanted: revisit D2's `q • γ` grade.
