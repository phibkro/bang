# Changelog

Notable **product** changes — the MVP increments that surface the verified kernel. This file is
**generated** from conventional commits (`just changelog`); the commit subject *is* the entry, so
there is no hand-written copy to gate or drift (history lives in git — this is a derivation, the
same as the ADR index / import graph). The pre-MVP verification grind is git + `ROADMAP.md` history,
out of scope here. Squash-merge each increment to `main` → one clean entry per shipped unit.

<!-- BEGIN GENERATED changelog (just changelog) — do not hand-edit -->

## Unreleased

### Features
- **surface** — ADTs end-to-end — Left/Right/match + (a,b)/let-destructure (#1) (`96346ff`)
- **arith** — infix arithmetic, comparisons & if over a verified δ-rule kernel (#4) (`f826dbc`)
- **surface** — do-notation — sequential effectful statements (#27) (`e4fcd2b`)
- **typecheck** — ADR-0066 ③ — bidirectional-checker spike (pure fragment) (`6cef2ba`)
- **surface** — ADR-0066 ②a — type-expression grammar + `(e : T)` ascription (`92114d4`)
- **typecheck** — ADR-0066 ②b — Surf-level checker, lifts the no-annotation limitation (`bb39c34`)
- **typecheck** — ADR-0066 ④ — effect-row inference + handler discharge (= #5) (`ec7638c`)
- **typecheck** — ADR-0066 ④b — type DISPLAY (#5's "type display": effect rows visible) (`2c536c6`)
- **typecheck** — ADR-0066 ④b (writing) — effect signatures `! {ρ}`, enforced (#5 complete) (`858421b`)

### Fixes
- **surface** — A-normalize effect-op arguments — arithmetic composes as put/raise/write args (#26 part-1) (`1e83aad`)
- **surface** — A-normalize ADT intros & eliminator scrutinees — value-restriction generalized (#29) (`e89e9c3`)
- **surface** — A-normalize state initial-value too — #29 value-restriction fully closed (`3f0d81f`)

<!-- END GENERATED changelog -->
