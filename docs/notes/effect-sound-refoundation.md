<!-- note-status: active -->
# effect_sound re-foundation — the three trace axioms → defs (Q14, 2026-07-12)

Baseline: `feat-effect-sound-refound` off main @ `412a7f88`. `effect_sound`
(`Bang/Spec.lean:191`) was flagged `[sorryAx, Trace, traceWithin, Source.evalTrace]`
— the last three are **bare `axiom`s** (`Bang/Core/Semantics/Eval.lean:403-407`),
parked on Q1 (a concrete `Eff`). This note is the PHASE-1 design (skeleton landed,
statable, HOLD before the Phase-2 discharge).

## The parking reason EXPIRED — but a second question is the real blocker

The axioms' comment names Q1 (`Eff`-algebra: semiring vs lattice). **Q1 is
RESOLVED** (`[Lattice Eff] [OrderBot Eff]`, ADR-0018) — so the concretization is
unblocked. But the parked axioms masked a SEPARATE open question, **Q14** (`what
does the trace observe?`, `docs/notes/questions/Q14-effect-sound-trace-observation.md`,
still OPEN). Q14 is the load-bearing design fork, and it forces a STATEMENT CHANGE.

## The Q14 tension (why the naive statement is FALSE)

The `perform` typing rule (`Typing.lean:229`) requires `labelEff ℓ ≤ φ` — the
performed label is in the FOCUS effect `φ`. But `handleThrows`/`handleState`
(`Typing.lean:246`+) DISCHARGE `ℓ`: the body runs at `e ≤ labelEff ℓ ⊔ φ`, and the
`handle` block's residual is `φ` (ℓ removed). So a label performed *inside* an
in-program handler is **NOT** `≤` the top-level residual `e`.

Concretely, `handle (throws ℓ) (raise ℓ)` at top-level `e = ⊥`:
- dispatches `ℓ` (the `raise`) during the run — so `ℓ ∈ trace`;
- yet `e = ⊥`, and `labelEff ℓ ≠ ⊥` (`labelEff_ne_bot`).

So the two obvious semantics both fail:

| semantics | `traceWithin` | verdict |
|---|---|---|
| trace = ALL dispatched labels; `t ⊆ e` | `∀ ℓ ∈ t, labelEff ℓ ≤ e` | **FALSE** (internal handling discharges ℓ from e) |
| trace = ESCAPING labels only; `t ⊆ e` | same | **VACUOUS** (an escaping op → `escapedCap`, not `done`, so on a `done` run `t = []`) |

## The chosen design — Q14 option (1) via the RUNTIME BOUND (no preservation, no LR)

Log at each DISPATCH the pair `(label, liveBound K e)`, and check each label against
the bound it was **performed under**, not the discharged top-level `e`. This is Q14's
option (1) ("the most informative"), realized WITHOUT threading a typing fact:

**The live bound is computed config-side.** `liveBound K e := e ⊔ ⨆{labelEff(h.label) |
handleF n h ∈ K}` — the top-level row joined with the labels of the currently-installed
handler frames. Handler frames carry their labels at runtime (`handleF n h`, `h.label` —
dispatch needs them; the glossary's typing-by-label/dispatch-by-identity split guarantees
labels are runtime-present). So the passenger maintains the bound purely from the stack:
entering a `handle` puts its label in the bound (structurally, `handleF` is on `K`),
popping removes it. No preservation, no LR — the theorem becomes "every dispatched op was
performed under a LIVE handler for its label, or its label is in the top-level row `e`",
provable by induction on the machine (a dispatched `ℓ` resolves to a `handleF` frame on
`K` whose label is `ℓ`, so `labelEff ℓ ≤ liveBound K e`).

This is the manager's Phase-2 redirect: the earlier worry ("the performed-at residual is a
TYPING fact") was pessimistic — the runtime bound `e ∪ {live handler labels}` is a SUPERSET
of the true focus residual, and it is exactly what `traceWithin` needs, computed config-side.

### DE-RISKED with runnable witnesses (BEFORE any induction)

`Bang/Witness/EffectTraceWitness.lean` (build-gated, 6 `example`s, all `rfl`/`decide`):

| witness | records | naive `⊆ ∅` | `traceWithin` |
|---|---|---|---|
| `handle(throws 1)(raise 1)` @ ∅ | `(1, {1} ⊔ ∅)` | **FALSE** (refuted) | **TRUE** |
| `handle(throws 1)(handle(throws 2)(raise 1))` @ ∅ | `(1, {2} ⊔ {1} ⊔ ∅)` | FALSE | TRUE (1 ∈ bound) |

The nested case CONFIRMS the runtime bound tracks EVERY live handler (both `throws` frames
join in), not just the discharging one — the shape is genuinely informative. No divergence
from the statement found, so no fork; the runtime-bound shape CLOSES the cheap witnesses.

### The four defs (`Eval.lean` §effect-trace — the OBVIOUS images)

```
abbrev Trace (Eff)           := List (Label × Eff)      -- (dispatched label, runtime live bound)
def liveBound                : EvalCtx → Eff → Eff      -- e ⊔ ⨆{labelEff h.label | handleF h ∈ K}
def Config.runTrace          : Nat → Config → Eff → Trace Eff → Result (Val × Trace Eff)
                                -- = Config.run + a passenger; appends (ℓ, liveBound K e) at DISPATCH
def Source.evalTrace fuel c e := Config.runTrace fuel (0,[],c) e []
def traceWithin t            := ∀ p ∈ t, labelEff p.1 ≤ p.2   -- per-dispatch runtime bound
```

`Trace` = `List Label` would be the naive candidate; it is replaced by
`List (Label × Eff)` precisely because a flat label-list cannot express the
per-dispatch bound Q14 forces. `liveBound` is the new helper — the runtime bound
folded off the stack `K` (config-side, no typing). `Source.eval`/`Config.run` stay
**byte-identical** (verified: the `git diff` on `Eval.lean` removes only the three axiom
lines and adds the sibling; `runTrace` is a separate def, `Config.run` is untouched).

### STATEMENT CHANGE (operator-visible fork)

The frozen `effect_sound` statement changes shape:

```
- Source.evalTrace fuel c   = Result.done (v, t) → traceWithin t e
+ Source.evalTrace fuel c e  = Result.done (v, t) → traceWithin (Mult := Mult) t
```

Two changes, both forced by the design: (a) `evalTrace` gains the whole-program
residual `e` as the initial focus bound; (b) `traceWithin` drops its second `Eff`
argument — the per-focus effect now lives INSIDE each trace entry. `(Mult := Mult)`
is supplied explicitly because `Mult` (needed for the `EffSig` instance) is otherwise
an unconstrained metavariable at the call site.

**This is a frozen-Spec statement change → operator sanction required** (per lane
discipline: STATEMENT_CHANGE_OK). Rejected alternatives (Option A false, Option B
vacuous) are recorded above; this is the ADR-input for the Q14 resolution.

## Statability — CONFIRMED

The skeleton type-checks: `just build` clean (760 jobs), `Spec.lean` error-free
(only the pre-existing `sorry` warnings). The axiom set MOVED as intended:

```
effect_sound  BEFORE: [sorryAx, Trace, traceWithin, Source.evalTrace]
effect_sound  AFTER:  [propext, sorryAx]        -- 3 bare axioms retired
```

The `sorryAx` is the theorem body (Phase 2); the three type/def axioms are gone.

## Phase-2 — DISCHARGED (`runTrace_traceWithin`, axiom-clean)

`effect_sound` is now proven: `[propext, Quot.sound]` (⊆ trusted-3, `sorryAx` dropped). The
discharge is `runTrace_traceWithin` in `Bang/Core/Semantics/Eval.lean`, a machine induction via
`Config.runTrace.induct` — three ~10-line lemmas (`liveBound_splitAtId`,
`labelEff_le_liveBound_of_step`, `traceWithin_append`) + the fuel induction, NO preservation, NO LR,
HARD-RAIL clear of `lr_*`. The `HasCTy` premise is NOT used (the bound is typing-independent); it
stays on the statement for the intended reading. The plan below is the record of how it went.

### What the theorem GUARDS (its refutation content — NOT true-by-construction)

The auditor's fair question: with `HasCTy` unused and the bound computed from the same frames dispatch
walks, is this vacuous? NO. `effect_sound` couples two INDEPENDENTLY-computed things — `runTrace`
records the label the CAPABILITY claims (`perform (vcap n ℓ)`), `liveBound` folds labels off the
HANDLER FRAMES (`h.label`). They agree ONLY because dispatch is fail-loud: `idDispatch` fires iff
`handlesOp h ℓ op`, forcing `h.label = ℓ` (`handlesOp_label`). So the theorem certifies
**dispatch/liveBound coherence: a recorded label is always the label of a live frame that handled it.**

The falsifying bug-shape is machine-witnessed (`EffectTraceWitness.lean` Witness 3, `cMismatch`,
`rfl`-checked): a cap `vcap 0 2` claiming label 2, id-matching a `throws 1` frame (label 1). WITH the
guard it ESCAPES (`escapedCap`, never `done`) — no bad record. WITHOUT the `handlesOp` guard (the
pre-ADR-0054 identity-only silent-wrong dispatch), it would `done`-record `(2, {1})` with `2 ∉ {1}` —
`effect_sound` FALSE. The runtime bound being "computed from the frames dispatch walks" is the point:
the theorem checks that dispatch's identity-match and the frame's label-content agree, a real invariant
that DID break (pre-0054). `HasCTy` is unused because this is an operational property of the fail-loud
dispatcher, not of the static type — a strength, not a vacuity.

### The discharge structure (as landed)

1. **Value-agreement — a THEOREM (not convention).** `Source.eval` stays the oracle, and the tie is
   PROVEN: `runTrace_erase_eq_run (Bang/Core/Semantics/Eval.lean)`:
   `Result.eraseTrace (Config.runTrace n cfg e t) = Config.run n cfg` for all `n, cfg, e, t`
   (`eraseTrace` = project the `done`-value, preserve `oom`/`escapedCap`/`stuck`), with the
   entry corollary `evalTrace_erase_eq_eval : eraseTrace (evalTrace fuel c e) = eval fuel c`. A
   fuel induction via `Config.runTrace.induct` mirroring the copied control flow (~15 lines, `simp`
   per case). This converts value-agreement from convention (copied control flow) to a machine fact —
   no drift between the two evaluators, `runTrace` is not an unoracled execution path (invariant #1).
   The witness file's local `Finset Label` instance additionally checks the TRACE shape by `rfl`.
2. **The discharge.** `traceWithin t` = every recorded `(ℓ, liveBound K e)` has
   `labelEff ℓ ≤ liveBound K e`. The induction invariant: at every DISPATCH-recording
   config, the dispatched capability `vcap n ℓ` resolves (`idDispatch K n ℓ … ≠ none`,
   else the run is `escapedCap` not the recording arm) to a `handleF n h` frame ON `K`
   whose label is `ℓ` (`handlesOp h ℓ op = true ⟹ h.label = ℓ`, the existing
   `Dispatch.lean:50` lemma). Then `labelEff ℓ = labelEff h.label ≤ liveBound K e` by a
   `liveBound`-membership lemma (a `handleF` frame on `K` contributes its label's row to
   the fold — a straightforward `EvalCtx` induction). **NO preservation, NO LR needed**:
   the bound is what dispatch itself witnesses. The one lemma to prove:
   `handleF n h ∈ K → labelEff h.label ≤ liveBound K e` (fold-membership), plus the
   dispatch-finds-a-matching-frame fact (`splitAtId` returns a frame with `handlesOp`,
   already in `Invariants.lean`). Estimate: ~2 lemmas + the fuel induction, well under
   the LR territory. **HARD RAIL respected**: this route never touches `lr_*`.

## Files

- `Bang/Core/Semantics/Eval.lean` §effect-trace (~:399-470) — the four defs (`Trace`,
  `liveBound`, `Config.runTrace`, `Source.evalTrace`, `traceWithin`).
- `Bang/Spec.lean:191` — `effect_sound` restated (`STATEMENT_CHANGE_OK`, this Q14 ruling).
- `Bang/Witness/EffectTraceWitness.lean` — the 6 runnable refutation/confirmation witnesses.
- `docs/notes/questions/Q14-effect-sound-trace-observation.md` — the design fork this resolves.

## ADR obligation (operator condition)

An ADR must record the Q14 ruling: option (1) via the runtime bound, the two refuted
alternatives (naive-false / escaping-vacuous) with their witness references, and the
`evalTrace`/`traceWithin` signature changes. Number next-free at merge time.
