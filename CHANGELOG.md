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
- **surface** — trait/impl declarations parse — Prog = decl prelude + body (#24 piece 1, ADR-0068) (`d724f81`)
- **typecheck** — type-directed operator resolution — the northstar runs (#24 piece 2, ADR-0068) (`63c7fb9`)
- **typecheck** — source laws discharge on the tested rung — the northstar is LAWFUL (#24 piece 3, ADR-0068) (`d9276c0`)
- **surface** — law implication sugar — conditional laws read as written (#39 part 1) (`d74325f`)
- **surface** — data declarations — named ctors/match over sums·products·μ; Vec northstar in its intended spelling (#2, ADR-0069) (`a59cc48`)
- **cli** — compiled path — bang run/eval --compiled runs exec∘compile, differentially gated (#6, closes #6) (`8d40928`)
- **surface** — named capabilities — with H as h in e + h.op, two state cells at once (#3, closes #3, ADR-0070) (`dadafad`)
- **calcvm** — binop δ-rule in the calculated machine — arithmetic on --compiled (#40, closes #40) (`d10f946`)
- **cli** — bang run/eval use the TYPED pipeline — data/traits/named-caps now runnable (`8e46e0f`)
- **reference** — GENERATE the grammar spec from the reified parser rules (#30 stage ③, closes #38) (`e8bb614`)
- **surface** — whitespace-insensitive tokenizer — the dominant dogfood papercut, killed (#30 stage ④, ADR-0071) (`97221cc`)

### Fixes
- **surface** — A-normalize effect-op arguments — arithmetic composes as put/raise/write args (#26 part-1) (`1e83aad`)
- **surface** — A-normalize ADT intros & eliminator scrutinees — value-restriction generalized (#29) (`e89e9c3`)
- **surface** — A-normalize state initial-value too — #29 value-restriction fully closed (`3f0d81f`)
- **hooks** — gate-guard denies bare 'git worktree add' — the actual 2026-07-05 vector (#13, #40b) (`0ab0c87`)
- **worktree** — reflink-copy .lake/packages, not symlink — a lake re-clone can only nuke itself (#40) (`154021a`)
- **build** — cache-get only on main checkout, not via a local-stub precondition (#43, closes #43) (`ae78f22`)

<!-- END GENERATED changelog -->
