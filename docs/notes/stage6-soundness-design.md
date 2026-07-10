# Stage 6 (soundness composition) — design map

> #44 / ADR-0085 Stage 6. Lane **s6probe**, 2026-07-10, probe branch `probe-stage6`
> (`2bb5feb`). Probe artifact: `scratch/Stage6CompositionProbe.lean` (census-safe; outside
> the `Bang.+` glob, imported by nothing in `Bang/`, never in `Bang/Audit.lean`). This is a
> MAP, not proofs — the pattern that priced Stages 3 and 5. Point-of-decision truth
> (ADR status, CONTEXT lead) is the manager's; this note is point-of-work truth.

## TL;DR verdict

**The ADR-0085 §Staged-plan Stage-6 HEADLINE obligation is ALREADY DISCHARGED on main.**
The four theorems ADR-0085 names for Stage 6 — `preservation`, `progress`, `type_safety`,
`no_accidental_handling` — are **axiom-clean WITH `Handler.custom` present** (build-gated below).
Their custom proof arms were folded in as Stages 2–5 landed; the census gate ADR-0085 assigns
Stage 6 (`just axioms` — trusted-three census) **passes right now**. So Stage 6 is **not** a new
frozen-statement grind. What genuinely remains is small and additive:

1. **Two instantiation lemmas** (the real Stage-6 content) — make the already-general theorems
   *usable at a custom handler*. Both **PROVEN CLEAN** in the probe (`[propext]` ⊆ trusted-three).
2. **One optional end-to-end corollary** — witnesses `type_safety` composed on a custom program.
   Compiles with a single **mechanical** `HasCTy → HasConfig'` `sorry` (not custom-specific; the
   built-ins need the identical lift).

**One-session verdict: YES** for the two instantiation lemmas + the corollary (a half-session:
the hard content is already on main). The debt-1 residual (`crelK_fund` custom arm, task #16)
does **NOT** block any of this — it feeds only the already-flagged `lr_*` set.

## What ADR-0085 actually names Stage 6

From ADR-0085 §Staged plan (the authoritative staging table):

```
6 SOUNDNESS   preservation/progress/type_safety +        MED-HIGH   just axioms —
              no_accidental_handling custom cases                    trusted-three census
```

And §Soundness ("the frozen statements do NOT change"): `preservation`/`progress`/`type_safety`/
`no_accidental_handling`/`subst_value` are **constructor-agnostic** — `Handler` is quantified,
never destructured in the STATEMENT. The entire #44 ripple is **ADDITIVE proof cases** (every
`cases h` gains one `custom` arm), *not* a re-freeze. So "Stage 6's theorem" is a category error
in the naive reading: there is no new headline statement. Stage 6 = **discharge the custom arms of
the existing headlines + keep the census green**.

## Build-grounded status of the four headline theorems (the gate that IS Stage 6)

`lake env lean Bang/Audit.lean` on `main`@`bbca771`+ (probe base), `#print axioms`:

| headline | axiom set | verdict |
|---|---|---|
| `no_accidental_handling` | **(none)** | clean — custom covered BY CONSTRUCTION |
| `preservation` | `[propext, Classical.choice, Quot.sound]` | clean ⊆ trusted-three |
| `progress` | `[propext, Quot.sound]` | clean ⊆ trusted-three |
| `type_safety` | `[propext, Classical.choice, Quot.sound]` | clean ⊆ trusted-three |
| `subst_value` | `[propext, Classical.choice, Quot.sound]` | clean ⊆ trusted-three |

These are **not vacuous-clean**. The Stage-3 typed rules `HasCTy.handleCustom` +
`HasStack.customF` are real constructors (the stage-1 `concat_custom_absurd`/
`handle_custom_uninhabited` absurdity is RETIRED — a well-typed custom frame CAN sit on a typed
stack). The custom arms are genuinely discharged inside the proofs:

- `handlesOp` has a **real** custom arm (`Dispatch.lean:46`: label-match `&&` clause-list lookup).
- `preservation_proof` / `progress'_proof` carry custom arms throughout: the `handleCustom` typing
  arm, the `customF` stack arm, and the **`perform`-dispatch custom resume** chain —
  `HasStack.concat_custom_resume` (re-type the resumed stack), `HasClauses.mem_typed` (the found
  clause is a typed `ret`-clause), and the resume-focus re-typing at the perform's arbitrary grade
  (`Soundness.lean` §2043+). The ADR-0085 §Soundness "residual-effect threading" risk (a custom
  clause performing effects) is **dissolved by the ret-shape** (ADR-0092 §D4): v1 clause bodies are
  `ret w`, effect-free, so there is no clause effect `φ'` to join — exactly why these arms close
  at the built-ins' cleanliness.

## Candidate Stage-6 theorems (probed — `scratch/Stage6CompositionProbe.lean`)

### Candidate 1 — `custom_handlesWithin` — REAL Stage-6 content, CLOSED clean

The custom analogue of the landed `throws_handlesWithin` (`Soundness.lean:3202`). A
`custom ℓ p cl` handler is scoped to `ℓ`'s row. This is the missing piece that makes
`no_accidental_handling` **instantiable at a custom handler**: the frozen theorem is already
general (proven from `HandlesWithin`, which quantifies over `handlesOp h` for any `h`); it needs
its `HandlesWithin` premise discharged for the custom form.

```lean
theorem custom_handlesWithin (ℓ : EffectRow.Label) (p : Val) (cl : List (OpId × Comp)) :
    HandlesWithin (EffSig.labelEff ℓ) (Handler.custom ℓ p cl)
```
Proof: `handlesOp (custom ℓ …) ℓ' op = true` forces `ℓ' = ℓ` by the label-match `&&` (same shape
as `throws`). **`#print axioms` → `[propext]`.** CLEAN.

### Candidate 1' — `no_accidental_handling_custom` — the "extend to user labels" corollary, CLOSED clean

`no_accidental_handling` INSTANTIATED at the custom form via Candidate 1. This is the concrete
reading of "extending `no_accidental_handling` to custom labels" from the task brief.

```lean
theorem no_accidental_handling_custom
    (hDisj : Disjoint (EffSig.labelEff ℓ) e) :
    ∀ ℓ' op, EffSig.labelEff ℓ' ≤ e → handlesOp (Handler.custom ℓ p cl) ℓ' op = false :=
  no_accidental_handling (custom_handlesWithin ℓ p cl) hDisj
```
**`#print axioms` → `[propext]`.** CLEAN. Rides the already-clean frozen theorem — one line.

### Candidate 2 — `custom_program_safe` — optional e2e corollary, ONE mechanical sorry

Composes Stage-3 typing at a fully-discharged row `⊥` with `type_safety`: a program that installs a
custom handler and handles its label to `⊥` never runs to `.stuck`. Pure corollary of the frozen
`type_safety` (no new arm) — `type_safety` is constructor-agnostic so it already covers the custom
fragment inside `c`.

```lean
theorem custom_program_safe (hc : HasCTy [] [] c ⊥ (CTy.F q A)) :
    ∀ fuel, Source.eval fuel c ≠ Result.stuck := by sorry
```
The `sorry` is the `HasCTy [] [] c ⊥ (F q A) → HasConfig' (0,[],c) ⊥ (F q A)` packaging.
**Mechanical, NOT custom-specific**: `HasConfig' = HasConfigTy ∧ NonEscape'`, the empty stack folds
`HasConfigTy (0,[],c) ⊥ (F q A) ≡ HasCTy [] [] c ⊥ (F q A)` (Spec.lean:121-122), and `NonEscape'`
is the free tautology `nonEscape'_all`. `type_safety'_proof` itself takes `HasConfig'` directly.
The lift is ~3 lines and identical for the built-ins. If a `HasCTy → HasConfig'` initial-config
lemma is wanted as reusable infra, that is the single new lemma this corollary asks for.

## Dependency map onto the landed pieces

```
                         ┌─ Stage-2 dispatch: handlesOp custom arm (Dispatch.lean:46) ─┐
                         │                                                             │
 Candidate 1 ───────────┤   no new deps — proven from handlesOp's custom arm shape     │
 custom_handlesWithin    │   (mirrors throws_handlesWithin)                             │
                         │                                                             ▼
 Candidate 1' ──── no_accidental_handling (FROZEN, already general + clean) ── + Candidate 1
 (extend to user labels)                                                       one-line compose

 Candidate 2 ──── type_safety (FROZEN, constructor-agnostic + clean)  ── + HasCTy→HasConfig'
 custom_program_safe      └─ Stage-3 HasCTy.handleCustom (Typing.lean:317)     packaging (mech.)
```

Nothing here depends on the LR (`lr_*`) frontier. The soundness composition rides the SYNTACTIC
metatheory (preservation/progress/type_safety) + the dispatch semantics — all landed and clean.

## What the debt-1 residual (task #15/#16) blocks vs doesn't

The `crelK_fund` **handleCustom arm** carries ONE `sorry` (`BinaryLR.lean` ~2290) — an *in-block
delegation* blocker (the mutual block's termination inference), NOT a mathematical gap: the content
(`compatK_handleCustom` + `krelS_custom_reinstall` + `custom_clause_resume`) is PROVEN and CLEAN.
Both cheap fixes were probe-refuted (the U-clause routes thunks through `CrelK`; a parameterized
block breaks the frozen Spec wiring) — the fix is a kernel-engineer mutual-block split (task #16).

- **BLOCKS:** only `lr_fundamental` / `lr_sound` / `lr_fundamental_closed` — the **already-flagged**
  set (their state/txn arms are *also* `sorry`). The custom arm rides the EXISTING flagged frontier,
  exactly as ADR-0085 §Soundness predicted ("gated no stricter than the built-ins already achieve").
- **Does NOT block:** any Stage-6 candidate above. The soundness composition is independent of the
  binary LR (it's the ◊4 contextual-equivalence theorem, a separate track — ADR-0016). All three
  candidates compile *with the debt-1 sorry live on main*.

## Out of Stage 6's scope (surfaced, not decided — manager's call)

- **`effect_sound` (Q14):** whole-body `sorry`; `Trace`/`traceWithin`/`Source.evalTrace` are still
  axioms. This is an **orthogonal open design question** (the trace-observation predicate) that
  PREDATES #44 — not a custom-specific gap. It is **OUT** of Stage 6 (Stage 6 owns the trusted-three
  census, not the trace semantics). Recommend it stays Q14/◊-line work, not folded into #44 Stage 6.
- **Multi-shot custom soundness:** scoped OUT of v1 by ADR-0085 D2 (one-shot pin). Not Stage 6.
- **Effectful clause bodies (non-ret-shape):** the D5 / first-class-`k` generalization
  (ADR-0092 §D4 entry gate). Not v1, not Stage 6.

## The walls

There are **no proof walls** in the ADR-named Stage-6 obligation — it is already met. The only
non-trivial item is Candidate 2's `HasCTy → HasConfig'` packaging lemma, and that is mechanical
(the built-ins already rely on it via `type_safety'_proof`). The genuine remaining hard work in
#44 lives EARLIER (the debt-1 mutual-block split, task #16) and LATER (Stage 7 surface), not in
Stage 6.

## Slice plan

Stage 6 is a **single small slice** (est. half-session):

1. Land `custom_handlesWithin` (sibling of `throws_handlesWithin`, `Soundness.lean` §F) — CLEAN.
2. Land `no_accidental_handling_custom` as its corollary (or leave it a `scratch`/witness if the
   general `no_accidental_handling` is deemed sufficient — Candidate 1 is the load-bearing lemma).
3. *(Optional)* Land `custom_program_safe` + the `HasCTy → HasConfig'` initial-config lemma if an
   e2e user-effect soundness statement is wanted as a headline. This is the one place a genuinely
   new (mechanical) lemma is needed.
4. Regate `just axioms` — expected byte-identical census (16 clean / 7 flagged); the new lemmas
   join the clean set.

No frozen-statement change. No new axiom. Census-preserving throughout.

## ADR-INPUTS

- **What Stage 6 IS:** the census-witnessed composition — the trusted-three + `no_accidental_handling`
  already carry their custom arms clean (Stages 2–5 folded them in); Stage 6 adds the small
  **instantiation lemmas** (`custom_handlesWithin` → `no_accidental_handling` at a custom handler)
  and optionally an **e2e corollary** (`custom_program_safe`). It is a *closing ceremony*, not a grind.
- **What Stage 6 DEFERS:** `effect_sound`/Q14 (orthogonal, out); multi-shot (D2, out); effectful
  clause bodies (D5, out); the `crelK_fund` custom arm (task #16, feeds only flagged `lr_*`).
- **The riskiest arm:** there is none of substance. If forced to name one: Candidate 2's
  `HasCTy → HasConfig'` packaging — and it is mechanical, shared with the built-ins. The ADR-0085
  "MED-HIGH" Stage-6 risk estimate is **superseded by the landed reality** (the residual-effect
  threading it feared is dissolved by the ret-shape, ADR-0092 §D4).
- **Recommendation:** collapse Stage 6 into a single closing slice per the plan above; do NOT scope
  `effect_sound` into it. The `just axioms` gate ADR-0085 assigns Stage 6 already passes — landing
  Candidate 1 makes the "no accidental handling at user labels" property *stateable*, which is the
  honest deliverable.
