# ADR-0025 · Resumptive state handlers: the CK machine keeps the continuation, and the closed focus dissolves the grade tension

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: Resumptive state handler: `dispatch` keeps the captured continuation + reinstalls a deep `state ℓ s'` frame; the closed focus dissolves the grade tension.
- **Resolves**: Q12
- **Depends-on**: 0023, 0020

- **Status:** Accepted (design lock for the `state` arm of the CK machine; implementation staged below)
- **Date:** 2026-06-22
- **Layer:** K (kernel — operational semantics + the metatheory over it). **Tag: K-ADR** (semantic).
- **Resolves:** OPEN_QUESTIONS **Q12** (graded state handlers — how `state ℓ s` threads grades).
- **Builds on:** ADR-0023 (the CK machine; `state` dispatch was explicitly deferred there with the
  note "the search + split is identical; only the post-dispatch config differs"). ADR-0022 (the `up`
  rule + handler discharge), ADR-0019/0020 (graded de Bruijn context).
- **Reference:** Plotkin–Pretnar / Bauer–Pretnar (algebraic effects + handlers — `get`/`put` as
  operations of a `state` handler that threads a stored value); Hillerström–Lindley (deep handlers
  resume by re-entering the captured continuation under a reinstalled handler).

## Context — `throws` discards, `state` must resume and thread

ADR-0023 made `Source.step` a CK machine over `Config = EvalCtx × Comp` and resolved the **`throws`**
(zero-shot) dispatch: the deep search finds the catching frame, **discards** the captured inner
continuation `Kᵢ`, and aborts to the outer stack `Kₒ` with the payload. `state` (rung 1, the first
*resumptive* paradigm) was deferred to Q12 for one reason: a stateful handler **threads a resource**
— the stored state value — *across* operations, and QTT multiplicity grades track resource usage, so
the two interact. The shallow (pre-CK) `Source.step` exposed two concrete grade mismatches (Q12):

- `get`: `handle (state ℓ s)(up ℓ "get" u) ↦ handle (state ℓ s)(ret s)` — the reduct's grade is
  `q • γ_s` (from `ret s`), the redex's is `q • γ_u` (from the unit arg). Preservation needs
  `γ_s = γ_u`; in the shallow step that only held when both are `zeros` (closed).
- `put`: stores the *program* value `v` (typed in the ambient `γ Γ`, **not** closed) as the new
  handler state, but handler-state typing wanted it closed. Open-term preservation broke.

## Decision

### D1 — Dispatch KEEPS `Kᵢ` and reinstalls a deep `state` frame (one-shot resume)

The deep search (`splitAt`) is shared with `throws`; only the post-split config differs. At the
catching `state ℓ s` frame, split `K = Kᵢ ++ handleF (state ℓ s) :: Kₒ`:

```
get:    ⟨K, up ℓ "get" _⟩  ↦  ⟨Kᵢ ++ handleF (state ℓ s) :: Kₒ,  ret s⟩      -- return stored s, state kept
put w:  ⟨K, up ℓ "put" w⟩  ↦  ⟨Kᵢ ++ handleF (state ℓ w) :: Kₒ,  ret unit⟩   -- store w, return unit
```

`Kᵢ` (the `letF`/`appF` frames between the `up` and the handler) is **kept**, not discarded — that is
the difference from `throws`. The handler frame is **reinstalled** (deep handler) so the *next*
`get`/`put` in the resumed continuation is handled too. This is **one-shot** resume: the continuation
is re-entered exactly once, in place — there is no continuation *value*, no multi-shot reification
(that stays the ADR-0015 frontier). The machine already had the continuation in the frame stack; D1
just plugs it back instead of dropping it.

### D2 — THE GRADE DISCIPLINE (the crux Q12 named): the closed focus dissolves it; **no `ω`-restriction on `S` is required**

Q12 offered, as option 1, "require the state type `S` to be unrestricted (grade `ω`) so threading
doesn't violate linearity." **We reject that as unnecessary.** The CK machine (ADR-0023 D1) keeps the
focus **closed** — binding is substitution-based, so every focus computation is typed at `Γ = []`,
`γ = []`. Both Q12 mismatches are *artifacts of the shallow substitution step* and **vanish** under
the closed focus:

- `get`'s reduct `ret s` is typed at `γ = []` (closed `s`), so its grade is `q' • [] = []` — there is
  no `γ_s = γ_u` obligation to discharge; both are `[]` structurally. Grades never thread across the
  stack (ADR-0023 D4: `HasStack` carries only effects + computation types; grade vectors live inside
  each `letF`'s stored continuation and are discharged by the closed-`v` `subst_value`).
- `put w` stores `w` taken from the **closed** focus (`HasVTy [] [] w S`), so the "open value as
  handler state" problem does not arise — the focus is closed, hence so is `w`.

The state value is duplicated at `get` (returned to `Kᵢ` *and* kept in the reinstalled handler). That
duplication is sound for **any** `S` because a closed value has grade vector `[]`: QTT multiplicity
tracks *variable* usage, and copying a value that uses no variables consumes no budget. So the
linearity discipline is **not** violated by threading a closed state, regardless of `S`'s grade.

**Decision: the state type `S` is required CLOSED at the handler (`HasVTy [] [] s₀ S`); no multiplicity
restriction (`ω` or otherwise) is imposed.** The CK machine's closed-focus invariant is exactly the
structure that makes resumptive state type-preserving — this is Q12 option 2 (the CK route)
*subsuming* option 1, not merely choosing it.

### D3 — Typing: `handleState` discharges `ℓ`; `get`/`put` via the op-partial `EffSig`

`handle (state ℓ s₀) M : F q A` when `s₀ : S` is closed, `M : F q A` at effect `e ≤ labelEff ℓ ⊔ φ`
(label-discharging, ADR-0022 D4), and `ℓ`'s interface is exactly `{get, put}` with
`opArg ℓ "get" = unit`, `opRes ℓ "get" = S`, `opArg ℓ "put" = S`, `opRes ℓ "put" = unit`. The return
clause is the identity (ADR-0023's Q6 simplification — a handled `ret v` returns `v` unchanged). The
`HasStack` stack-typing gains a `stateF` frame mirroring this.

### D4 — Out of scope (deferred, with reasons)

- **A real counter** (`get; put (get+1)`) needs arithmetic `+`, a separate K-ADR (five primitives,
  invariant #5). The **cell** (`put 7; get ⟶ 7`) needs only resumptive state and is the rung-1 demo.
- **Multi-shot / first-class continuations** (the captured `Kᵢ` as a reifiable value) stay the
  ADR-0015 frontier; D1 is deliberately one-shot in-place.
- **In-place vs event-store handler split** (PRD §6) is a *library* choice over this one mechanism,
  not extra kernel work (the event-store handler is `state ℓ (event-log)` whose `get` folds the log).

## Rejected alternatives

| option | why not |
|--------|---------|
| Require `S` unrestricted (grade `ω`) — Q12 option 1 | Unnecessary under the CK machine: the closed focus already makes the stored/threaded state grade-`[]`, so copying it costs no variable budget for any `S`. Imposing `ω` would reject perfectly safe linear-state programs and add a typing side-condition with no soundness payoff. |
| A dedicated graded-state metatheory (coeffectful references) — Q12 option 3 | Over-engineered for one-shot in-place state: that machinery exists to thread grades through *open* continuations / first-class references. The CK machine keeps the focus closed, so there is nothing to thread. Revisit only if multi-shot state lands. |
| Keep `state` dispatch returning `none` (stay deferred) | Rung 1 (the product's first paradigm-as-library) is blocked on it; Q12 was blocked only on the reified continuation, which ADR-0023 now provides. Deferring further is deferring the product spine for no remaining technical reason. |
| Multi-shot resume (reify `Kᵢ` as a `cont` value now) | Strictly more metatheory (a new `Val` constructor, continuation typing) for a capability rung 1 does not need. One-shot in-place is the minimal mechanism that runs a state cell; multi-shot is additive later (ADR-0023 "revisit if"). |

## Implementation staging

```
Unit A (machine)   Operational.lean: splitAt (return the inner prefix Kᵢ), dispatchOn (post-split
                   throws-abort / state-resume), dispatch = splitAt >>= dispatchOn. THROWS behaviour
                   bit-identical to ADR-0023. Smoke-tested by RUNNING the state cell to `done 7`.
Unit B (typing)    Syntax.lean: HasCTy.handleState (D3) + HasStack.stateF. State programs become
                   typable; the cell's HasCTy derivation is the witness.
Unit C (proofs)    Metatheory.lean: re-prove preservation/progress over the splitAt/dispatch refactor
                   (THROWS cases CLOSED, axiom-clean). The STATE-dispatch cases (resumed-stack typing)
                   are the residual proof obligation — see RUNG1-OBLIGATION markers.
```

Units A + the throws-side of C are landed and axiom-clean (`no_accidental_handling` still 0-axiom,
the ◊2 gate). The state-dispatch preservation/progress cases are marked `RUNG1-OBLIGATION` for the
proof-engineer: the hard core is the **resumed-stack typing lemma** (typing
`Kᵢ ++ handleF (state ℓ s') :: Kₒ` from the original `HasStack K`, with the focus re-typed from the
`up`'s result to `ret s`/`ret unit`).

## Revisit if

- Multi-shot / first-class continuations are wanted: `Kᵢ` becomes a `cont` value (a new `Val`
  constructor + an ADR). The stack is already the continuation; this is additive.
- Arithmetic lands (for a real counter): a separate K-ADR; orthogonal to state's resume mechanism.
- The event-store handler is built: confirm it is `state ℓ (event-log)` over THIS mechanism (PRD §6 /
  PATH-rung1-state framing A), i.e. a library, not kernel work.
