# ADR-0106 · D5 parameterised handlers (handler memory): opt-in `customUpd`, yield-sniffing rejected

<!-- adr-frontmatter -->

- **Status**: Proposed
- **Summary**: D5 (parameterised handlers / handler memory, the effect-algebra rung-2 face — a custom
  handler whose clause UPDATES its carried param `p` across resumes, Plotkin–Pretnar) enters the kernel
  as a NEW `Handler.customUpd` constructor DISTINCT from the read-only `custom`, NOT as a mode-flag on
  `custom` and NOT inferred from the clause's yield shape. A `customUpd` clause yields `ret (pair w p')`
  (resume-value `w` + updated param `p'`), decoded ONLY in the `customUpd` dispatch arm where it is the
  DECLARED contract; the `custom` constructor, its dispatch arm, its typing rule (`HasClauses`/
  `handleCustom`), and every soundness/LR lemma over it stay BYTE-IDENTICAL. The param-update is the
  `state`-arm `put` swap (`Dispatch.lean:137`, which already reinstalls a CHANGED carried value)
  generalized to the user-effect arm; the proof spine is templated by `krelS_state_reinstall`'s PUT arm
  (`BinaryLR.lean:700`). NO 6th primitive — a 5th `Handler` constructor reusing the CK machinery
  (invariant #5 holds, the same class of change ADR-0025/0030 made adding `state`/`transaction`).
  **Rejected: YIELD-SNIFFING** — decoding a `ret (pair w p')` yielded by a plain `custom` clause as a
  param-update. It silently reinterprets a legal v1 clause that returns a pair AS ITS VALUE (`read(x)
  => ret (pair a b)` typed at `opRes ℓ read = prod A B`), a semantics change to already-shipped
  programs (the silent-wrong class). **Rejected: MODE-FLAG** (`custom : … → ParamMode → …`) — it
  re-patterns all 134 construct-sites AND re-states every theorem mentioning `Handler.custom ℓ p cl`
  (~50 match-sites), so the unmarked path is NOT definitionally unchanged (a red spine, not a
  tested-superset); the new constructor is the only shape where the unmarked path is untouched BY
  CONSTRUCTION. Scope: this ADR fixes the KERNEL rep + the yield-sniffing/mode-flag rejections; the
  SURFACE spelling of the opt-in (a `mut param` marker vs. an explicit `resume(w) with param := p'`
  form) is the Stage-7 lane's call (rides ADR-0095 D5's reserved `resume`), and the answer-grade
  typing (`HasClausesUpd`) + the proven-core re-grade (soundness/LR over `customUpd`) are gated as
  their own increment (S2–S4) after the tested-superset semantics (S0–S1).
- **Resolves**: the ADR-0092 §D5 / ADR-0087 §Open-questions read-only-param deferral (the "param-UPDATE
  (`put`-like clauses)" item ADR-0095 §"What Stage 7 does NOT do" explicitly parked)
- **Depends-on**: 0085 (the coexist `custom` handler + one-shot v1 pin — the arm D5 gives update to),
  0087 (the finite clause rep the param lives in), 0092 (the typed custom-handle rule + the D4 ret-shape
  wall the pair-yield stays inside), 0025 (resumptive `state` — the parameterised-handler precedent + the
  PUT-arm proof template), 0095 (the handler surface — its D5 "resume reservation" is where the opt-in
  spelling lands; NOTE its decision-list "(D5)" is a DIFFERENT D5 = resume spelling, not this rung-2
  param-update)

## Status

Proposed (2026-07-12). Design-first probe (`docs/notes/d5-param-handlers-design.md`, branch
`design-d5-param-handlers` off `main @ 02e406f2`, landed `b16b3927`) with a HOLD, then amended (§0.5)
under team-lead review that caught the yield-sniffing soundness gap. Implementation is the S0–S4 slice
ladder (`d5-param-handlers-design.md` §5); S0–S1 (tested-superset) approved to proceed under the four
conditions below, S2–S4 (proven-core) gated as a dedicated increment.

## Context

The `custom` handler (ADR-0085/0087/0092) is the general user-defined-effect handler: a label `ℓ`, a
carried param `p : Val`, a finite clause list. In v1 the param is READ-ONLY — a clause reads it (bound
at index 1) but the dispatch arm reinstalls it UNCHANGED (`Dispatch.lean:181`). Three lanes this week
worked around the absence of handler-owned mutable state: the Sched demo threaded its seed through the
driver's recursion (`examples/dst-rounds-lcg/main.bang`, the `go n s acc` args), the DST examples
contorted their ret-shape, the Fs sim wanted a growing file→content map behind the effect interface.
All three want the same thing: a USER effect whose handler OWNS evolving state — exactly Plotkin–Pretnar
**parameterised handlers**, the effect-algebra ladder's rung-2 (`docs/notes/effect-algebra-survey.md`
§2). The mechanism already exists for the BUILT-IN `state` effect (its `put` reinstalls a changed cell,
`Dispatch.lean:137`); D5 gives the `custom` (user-effect) arm the same capability.

The design note reached "shape A: the clause yields `ret (pair w p')`, dispatch splits + reinstalls
p'" — but the first draft SNIFFED that shape from a plain `custom` clause's yield. Team-lead review
caught that this silently reinterprets a legal v1 clause returning a pair as its value. The fix — and
this ADR's decision — is to make D5 OPT-IN at the rep.

## Decision

### 1. A new `Handler.customUpd` constructor (opt-in, not a flag, not sniffed)

```
IR.lean:  | custom    : Label → Val → List (OpId × Comp) → Handler    -- UNCHANGED (read-only param)
          | customUpd : Label → Val → List (OpId × Comp) → Handler    -- NEW: parameterised (updatable)
```

`customUpd`'s dispatch arm decodes the clause's `ret (pair w p')` as (resume `w`, reinstall `p'`) —
the `state` PUT shape, confined to this arm. The `custom` arm is byte-identical to today. The
pair-decode NEVER runs on a `custom` handler.

### 2. The clause contract is DECLARED by the constructor, never inferred

A `customUpd` clause is typed (S2, `HasClausesUpd`) to yield `ret (pair w p')` with `w : opRes ℓ op`
and `p' : P` (the same carried-param type). This is the constructor's contract — the dispatch arm
decodes the pair because the handler is `customUpd`, not because it observed a pair. A `custom`
clause yielding a pair (typed at `prod A B` as its result) keeps getting the pair as its VALUE.

### 3. NO 6th primitive; the unmarked path is definitionally unchanged

`customUpd` is a 5th `Handler` constructor reusing the CK machinery (subst/freshness/cap-enumeration
arms are the `custom` arm verbatim — a `customUpd` handler substitutes/enumerates identically). Only
dispatch + typing carry new logic. Invariant #5 holds (the ADR-0025/0030 precedent). Every existing
`custom` theorem STATEMENT and proof is untouched because they destructure `custom`, which did not move.

## Rejected alternatives

- **YIELD-SNIFFING** (the first-draft shape A on `custom`): decode a `ret (pair w p')` yielded by a
  plain `custom` clause as a param-update. REJECTED — it silently reinterprets a legal v1 clause that
  legitimately returns a pair as its value (`read(x) => ret (pair a b)` at `opRes = prod A B` would
  become "resume `a`, set param `b`"). A semantics change to shipped programs; the silent-wrong class
  `CLAUDE.md`'s "make illegal states unrepresentable" forbids. This is the alternative a future session
  WILL re-propose ("why not just look at the yield?") — recorded here so it is closed, not reopened.
- **MODE-FLAG on `custom`** (`custom : Label → Val → ParamMode → List (OpId × Comp) → Handler`): a
  field distinguishing read-only from updatable. REJECTED — a new field re-patterns all 134 construct-
  sites AND forces re-statement of every theorem mentioning `Handler.custom ℓ p cl` (~50 match-sites:
  `custom_handlesWithin`, `no_accidental_handling_custom_proof`, `custom_program_safe_proof`, the LR
  `krelS_custom_reinstall`, …). The unmarked (read-only) path would NOT be definitionally unchanged, so
  a S0 dispatch change could break a `custom` proof arm — a red spine, not a tested-superset. The new
  constructor is the ONLY shape where the unmarked path is untouched by construction.
- **A new `Comp` former `customYield w p'`** (shape B): a bespoke reduction rule. REJECTED — kernel-
  former pressure on invariant #5; the pair encoding subsumes it with no new former (the `pair` is the
  existing ADT).
- **Param as a second clause component** (shape C, a product clause body `(ret w, ret p')`): REJECTED —
  doubles the clause typing (two sub-derivations per clause), no gain over the pair-in-`ret` encoding.

## Conditions on implementation (team-lead review)

1. **OPT-IN at the rep** — `customUpd` is a new constructor; param-update is never sniffed from the
   yield. (This ADR.)
2. **The whole existing corpus byte-identical under a differential run EVERY slice** — non-`customUpd`
   handlers are untouchable (enforced by the `AgreeOutcome`/`Fuzz` harness on the unchanged `custom`
   path).
3. **Headline axioms green EVERY push** — S0's dispatch change is a NEW `customUpd` arm; the `custom`
   arm's equation is definitionally unchanged, so no proof arm referencing the old equation breaks. If a
   `custom` proof broke, the slice would be a red spine — restructure so the marked path is a new arm
   and the unmarked path is definitionally unchanged.
4. **A pair-valued-clause regression witness** pins that a NON-`customUpd` `custom` handler returning
   `pair(w, x)` still gets the pair as its VALUE — the exact regression yield-sniffing would have
   caused, pinned in S0 before it can ever happen.

## Consequences

- Handler memory for USER effects lands as a tested-superset at S0–S1 (semantics + engines, diff-tested
  against `Source.eval`), then the proven core follows at S2–S4 (typing + soundness + LR over
  `customUpd`, porting the `state`/`custom` twins).
- The DST/Sched/Fs-sim lanes gain handler-owned encapsulated state — the ergonomic/encapsulation win
  (`d5-param-handlers-design.md` §3: NOT new computational power; the value set is unchanged, D5 changes
  WHO owns the state).
- The `custom` (read-only) form stays as the cheaper, proof-lighter default; `customUpd` is opt-in for
  the handlers that need mutation. Two constructors, one for each side of the read-only/updatable fork —
  the cost of the soundness guarantee that a pair-returning `custom` clause is never reinterpreted.
