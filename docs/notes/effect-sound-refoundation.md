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

## The chosen design — Q14 option (1), the INFORMATIVE per-focus bound

Log at each DISPATCH the pair `(label, focus-effect)`, and check each label against
the effect it was **performed at**, not the discharged top-level `e`. This is Q14's
option (1) ("the most informative"). It is TRUE (preservation bounds each focus
effect) and non-vacuous (every internal dispatch is a real checked obligation).

### The three defs (`Eval.lean` §effect-trace — the OBVIOUS images)

```
abbrev Trace (Eff)           := List (Label × Eff)           -- (dispatched label, focus residual)
def Config.runTrace          : Nat → Config → Eff → Trace Eff → Result (Val × Trace Eff)
                                -- = Config.run + a passenger accumulator; appends (ℓ,φ) at DISPATCH
def Source.evalTrace fuel c e := Config.runTrace fuel (0,[],c) e []
def traceWithin t            := ∀ p ∈ t, labelEff p.1 ≤ p.2   -- per-focus bound
```

`Trace` = `List Label` would be the naive candidate; it is replaced by
`List (Label × Eff)` precisely because a flat label-list cannot express the
per-focus bound Q14 forces. `Source.eval`/`Config.run` stay **byte-identical**
(verified: the `git diff` on `Eval.lean` removes only the three axiom lines and adds
the sibling; `runTrace` is a separate def, `Config.run` is untouched).

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

## Phase-2 plan (after operator ack of the statement change)

1. **Value-agreement differential guard.** `Source.eval` stays the oracle. The
   guard is a generic lemma (NOT a `#guard` — no concrete `EffSig` instance exists
   in-tree; the kernel is abstract over `Eff`):
   `(Config.runTrace n cfg φ t).map_value = Config.run n cfg` — i.e. the value
   component agrees for all `n, cfg, φ, t`. Structural induction on fuel; the two
   defs share `Source.step` and the same terminal classification (the DISPATCH
   `none → escapedCap` arm matches `Config.run`'s `perform (vcap _) → escapedCap`).
2. **The discharge.** `traceWithin t` = every recorded `(ℓ, φ)` has `labelEff ℓ ≤ φ`.
   Each recording happens at a DISPATCH step of a config typed at focus residual
   `φ`; the `perform` typing rule GIVES `labelEff ℓ ≤ φ` directly. The induction
   threads `HasConfigTy`-preservation (`preservation`, `Spec.lean:119`) to carry the
   focus-typing to each dispatch. Key obligation: the `φ` passed to `runTrace` must
   track the config's residual — the initial `e` is the whole-program residual, and
   the DISPATCH arm records the CURRENT `φ`. **OPEN for Phase 2:** `runTrace` threads
   a SINGLE `φ` (the top-level `e`), but the focus residual SHRINKS as handlers pop.
   Two shapes to resolve at Phase 2 kickoff:
   - (i) record the top-level `e` at every dispatch and prove `labelEff ℓ ≤ e` for
     the *unhandled* labels only — collapses toward Option B (vacuous) unless the
     trace is filtered to escaping labels;
   - (ii) thread the LIVE focus residual through `runTrace` (recompute from the
     config's stack, or preservation-derive it) so each `(ℓ, φ)` carries the ACTUAL
     performed-at effect — the genuinely informative bound. **(ii) is the design
     intent**; it needs `runTrace` to compute/carry the per-config `φ`, which is the
     one non-mechanical Phase-2 question (the perform-in-handler labeling question
     Q14 flagged). Price it BEFORE grinding: if (ii) needs the LR spine it is a
     priced refutation, not a discharge.

## Files

- `Bang/Core/Semantics/Eval.lean` §effect-trace (~:399-449) — the three defs.
- `Bang/Spec.lean:191` — `effect_sound` restated.
- `docs/notes/questions/Q14-effect-sound-trace-observation.md` — the design fork this resolves.
