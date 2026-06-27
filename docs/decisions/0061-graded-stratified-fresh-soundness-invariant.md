# 0061 — The soundness-diagonal invariant: typeless → graded + stratified-fresh

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: The non-escape soundness diagonal (`Bang/Model.lean`, inc-5) preserves an internal config invariant `WScfg` across `Source.step`; reachability + `WScfg ⟹ FocusResolves` then gives `NonEscape` for the initial config (the sole inc-4 carried obligation). `WScfg` carried TYPELESS liveness (`LWSC`/`LWSK`) + the ids-only freshness `WellCounted` (`StackBelow`), which **discard two facts the preservation needs**, leaving `wsCfg_step` with 3 un-closable sorries. (1) The typed GRADE: `LWSC`'s storage `q` is a free `∃`, so a typed-DEAD capability is NOT forced dormant — the 4 elimination walls (letC/app/case/split) of the ⊥-row return-escape and the REDUCE dead-arg cannot close (spike #48 build-PROVED this: the value-layer B-occ technique works but WALLS at eliminations; `escapeB_app` in `Bang/BoccRegress.lean:145` is the machine-checked falsity that typeless B-occ blinds at the arrow/eliminator). (2) Cap-id FRESHNESS over STORED caps: `StackBelow` bounds only `handleF` FRAME ids `< g`, never the caps stored in `letF`/`appF` frames, so the POP-tail (popping `handleF g'` must leave the tail's caps `≠ g'`) is unprovable though TRUE by global-fresh monotone minting (ADR-0055). DECISION: regrade `WScfg` to carry GRADED liveness `LWSCg`/`LWSKg` (gate `b && decide(q≠0)` tied to the typed binder grade, projecting to the typeless layer by forgetting the grade) PLUS a STRATIFIED capability-freshness conjunct `FreshCfg` = `CapsBelow` (ids + stored caps `< g`) ∧ a focus-cap bound ∧ `StratFresh` (everything below each `handleF n` is `< n`). The grade closes the eliminations (dead intermediate ⇒ gate-dormant ⇒ stack-independent) + the REDUCE dead-arg; `StratFresh` closes the POP-tail; the POP-focus rides B-occ over the grade. Result: `type_safety` reduces to a single sorry on DISPATCH (#35, the resumption-multiplicity grading).
- **Refines**: 0057, 0055
- **Depends-on**: 0060, 0055, 0057, 0054, 0023
- **See-also**: 0016, 0026

This ADR builds directly on **ADR-0060 (grade-driven liveness + the grade-rig commitment)** — the source
of the graded layer it reuses: `LWSVg`/`LWSCg`, the `b∧decide(q≠0)` gate, the q=0 discharge, and the rig
commitment (NoZeroDivisors + ZeroSumFree + Nontrivial). (ADRs 0056–0060 live on the `typed-static-r1` docs
branch; the `inc5-lr-reindex` proof branch has not yet merged `docs/decisions/`, so their files are not
visible from here — branch divergence, resolved on merge.)

## Status

Accepted (design gated by the orchestrator after a STOP-and-SHOW against spike #48's requirements,
2026-06-27). **Phase 1b SKELETON LANDED** on `inc5-lr-reindex`: the new `WScfg` + `CapsBelow`/`StratFresh`/
`FreshCfg` defs + the re-stated `wsCfg_step` (thin dispatcher over two graded obligations + `freshCfg_step`)
+ the named Phase-2 building blocks — all build green with sorries ONLY at the planned obligations.
`#print axioms diagonal` = `[propext, sorryAx, Classical.choice, Quot.sound]` (the sorries shifted but stay
accounted). The Phase-2 proofs (the eliminations + freshness arm + `lwsvg_closed_regrade`, then DISPATCH
#35) are tracked under task #47.

## Decision

Replace `WScfg`'s typeless liveness + ids-only freshness with:

```
def WScfg (Co) (cfg) : Prop :=
  ∃ e C, HasCTy [] [] cfg.2.2 e C ∧ HasStack cfg.2.1 e C ⊥ Co     -- typing (unchanged)
       ∧ LWSCg cfg.2.1 [] true cfg.2.2                            -- GRADED focus (γ = [], closed)
       ∧ LWSKg cfg.2.1 cfg.2.1 [] true                            -- GRADED stack
       ∧ FreshCfg cfg                                             -- stratified cap-freshness
```

with the freshness layer (building-block defs kept SEPARATE from liveness — one construct per problem):

```
def CapsBelow (g) : EvalCtx → Prop      -- handleF ids AND stored letF/appF caps all < g
def StratFresh : EvalCtx → Prop         -- each handleF n dominates everything below it (< n)
def FreshCfg : Config → Prop            -- CapsBelow g K ∧ (focus caps < g) ∧ StratFresh K
```

The three `wsCfg_step` sorries close as:
- **REDUCE** — the substituted value's graded liveness is INVERTED from the carried focus `LWSCg` (NOT
  rebuilt from typing), so the old `capsResolve_reduce` (all-caps-resolve) obligation is ELIMINATED:
  ρ=0 (dead) via `lwscg_to_lwsck` + `lwsck_subst`; ρ≠0 (live) via `lwsvg_closed_regrade` + `lwscg_subst`.
- **POP** — focus `ret v` re-homes past `handleF g'` via `lwscg_returnEscape` (B-occ on the answer type,
  the dead intermediate now gate-dormant); the tail re-homes via `lwskg_pop_fresh` (`CapsBelow g' K'`
  inverted off `StratFresh`).
- **DISPATCH** — stays a single named sorry (`lwsg_step_dispatch`, #35).

## Why this model

1. **The grade is the lever the eliminations need.** Spike #48 PROVED the value-layer B-occ closes every
   value former + ret/force/lam/perform, but WALLS at the eliminators because B-occ constrains only the
   RESULT type, never the consumed intermediate — exactly `escapeB_app`'s arrow-blindness. The typed grade
   gates that dead intermediate dormant, which is stack-independent; nothing else in the typeless world can.
2. **Freshness is a stack-structural fact, distinct from liveness** — global-fresh monotone minting
   (ADR-0055) makes the stack stratified (handleF ids strictly decrease down-stack; a cap named `n` lives
   only inside handler `n`'s body, above frame `n`). Recording it as a SEPARATE predicate (not folded into
   `LWSKg`) keeps the two concerns orthogonal and dodges the MINT `n = g` uninhabitability that folding hits.
3. **Self-contained preservation.** `FreshCfg` bundles the focus-cap bound so `freshCfg_step` is TRUE
   without external hypotheses (MINT injects `vcap g`, advances the counter to `g+1`, re-bounds by
   monotonicity; POP inverts the `StratFresh` head).
4. **The graded engine already exists** (`LWSVg`/`LWSCg`, projection, q=0 discharge, graded subst, the
   forward lift `lwscg_of_typed`) — this is a SWAP + 2 new helpers (`lwsvg_closed_regrade`, `StratFresh`),
   not a from-scratch build. SSoT: one `lwscg_of_typed` lift consumed by the SEED.

## Rejected alternatives

- **Typeless-only (keep `LWSC`/`LWSK`)** — MACHINE-REFUTED. Spike #48's typeless `lwsc_returnEscape` walls
  at all 4 eliminators; `escapeB_app` (`BoccRegress.lean:145`) is the kept witness that the typeless B-occ
  is blind at the arrow. The 3 sorries are not provable typelessly.
- **Global `CapsBelow` without `StratFresh`** — INSUFFICIENT. `CapsBelow g K` bounds the tail by the GLOBAL
  counter `g`, giving tail caps `< g`, not `< g'` (the popped frame's id, which can be ≪ g). The POP-tail
  needs `≠ g'`; only the stratified per-handleF bound delivers it.
- **Fold `n ≠ g` freshness into `LWSKg` (à la `LWSVp`/`LWSCp`)** — collides with the same MINT `n = g`
  uninhabitability already found for the identity layer; and entangles freshness with liveness (two
  problems, one construct). Kept separate.
- **Rebuild value liveness from typing at REDUCE (the old route)** — re-introduces the `capsResolve_reduce`
  all-caps-resolve obligation, which is FALSE for thunk-buried dead caps (`CohSubstRefute::wbad`). The
  invert-from-focus route (with `lwsvg_closed_regrade`) avoids it.

## Revisit if

- `lwsvg_closed_regrade` turns out FALSE under some case (it is expected HARD-not-FALSE: closed ⇒ no
  `vvar` leaves ⇒ grade-blind, flag-weakening via `lwsvg_to_dormant`). The refute-first rule applies — a
  machine-checked `False` from it (kept witness) would force re-shaping the REDUCE arm, NOT this invariant.
- DISPATCH (#35) reveals the resumption grade needs a different freshness shape than `StratFresh` provides.
