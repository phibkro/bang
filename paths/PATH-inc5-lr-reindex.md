# PATH — inc-5: the binary-LR re-index (DEFERRED at the Canonical wall)

> **Resume brief for the ◊4 `lr_sound` seam** — the binary-LR (contextual-equivalence) re-index to
> the identity-dispatch + global-fresh kernel (ADR-0054/0055). The v1 SOUNDNESS payoff is **DONE and
> on main** (`progress`/`type_safety` axiom-clean via the ADR-0063 `escapedCap` reclassification —
> do not relitigate); what this PATH still owns is the FLAGGED cluster `lr_sound` /
> `lr_fundamental(_closed)` / `seq_unit`. Deferred at an **operator-level fork** (below).
> Full derivation history: this file @ `9bcb5ec` and earlier (git); ADRs 0054–0063 are the decisions.

## Feeds the constraint
- **Binding constraint now**: the flagged `lr_sound` cluster (proof-state @ `f826dbc`) blocks the
  full ◊4 close AND #44 Stage 5 (ADR-0085's LR case rides this frontier).
- **How this path feeds it**: closes the binary-LR re-index, un-flagging 4 of the 8 flagged headlines.

## Module map (this PATH's history predates the restructure — old name → current home)

| old (in git history) | current |
|---|---|
| `Bang/LR.lean` | `Bang/Meta/LR.lean` |
| `Bang/Compat.lean` (`crelK_fund`/`KrelS` layer) | `Bang/Meta/BinaryLR.lean` |
| `Bang/Model.lean` (diagonal · carriers) | `Bang/Core/Semantics/{Eval,Invariants}.lean` |
| `Bang/Metatheory.lean` | `Bang/Core/Soundness.lean` |
| `Bang/Operational.lean` (`splitAtId`/`idDispatch`) | `Bang/Core/Semantics{,.Dispatch}.lean` |

## Decisions — build-arbitrated, don't relitigate
- **Machine-shaped KrelS** (observes the canonical config) + **id-renaming invariance** primitives.
- **ADR-0058 route-1**: `CrelK`/`KrelS` carry the real counter `g` internally; `Crel`/Spec frozen-safe.
- **ADR-0063**: cap-escape = DEFINED fail-loud `escapedCap` terminal; dissolved the old diagonal
  soundness path — `progress'`/`type_safety'` closed axiom-clean on pure typing-preservation, #35-free.
- **The soundness payoff is the diagonal, NOT the binary LR** — the LR is contextual equivalence,
  a separate deliverable.

## THE TWO WALLS (why deferred) — distinct obligations, one likely joint fix

**(W1) `lr_sound`'s SOLE residual — the reshape↔raw-focus adequacy bridge (task #72, Q22).**
The authoritative statement is IN the frozen Spec (`Bang/Spec.lean:196-211`): `CrelK`'s biorthogonal
closure observes the RAW focus `(g, C, cᵢ)` but the machine-faithful `converges_plug_iff` observes the
cap-substituted RESHAPE `(handlerCount C, canonStack C cᵢ, capSubstInto C cᵢ)`; build-confirmed
(`scratch/AdequacySpike.lean`) the bridge closes IFF `capSubstInto C cᵢ = cᵢ` — excluding exactly the
effectful case. An ARCHITECTURAL definition-shape fork (CrelK-reshape vs plug-congruence), not a grind.

**(W2) `lr_fundamental` (= `crelK_fund`) state/txn producer arms — the `krelS_append` + ▷-metering
crux, where the Canonical/density wall bites**: `crelK_ret`'s handleF-pop `+1` bridge needs
`Canonical` (dense ids); frozen `CrelK` quantifies over ARBITRARY KrelS stacks, and **KrelS does not
imply Canonical** (sparse gensym ids). Build-confirmed `e909e73` (`scratch/CanonicalWallProbe.lean`):
B-occ⇒density and drop-the-guard BOTH fail.

**The convergence hypothesis (falsifiable, probe before committing):** ONE frozen-statement change —
`CrelK`/`KrelS` observing the CANONICAL RESHAPED config — plausibly dissolves BOTH: the W1 bridge
becomes definitional (observation ≡ what `converges_plug_iff` produces) and W2's density holds
by-construction (`canonStack` is dense). Cost: ADR + STATEMENT_CHANGE_OK + re-threading the
BinaryLR mutual block (multi-session). Alternatives: W1-only plug-congruence route (raw-focus
`converges_plug_iff` form — the "id-agnosticism relational step"); W2-only Canonical-reachability
lemma (hard — `krelS_refl` needs its own Canonical supply). Decision memo: issue #15.

**OPERATOR RULING (2026-07-09, on #15): D now, A later.** Stay deferred (blocks nothing —
v1 soundness clean; #44 Stage 5 gated at the built-ins' frontier). Resume trigger = #44
Stage 5 or the ◊6 paper wanting `lr_fundamental`; then run option A **probe-first** (a
bounded scratch spike of the canonical-reshape `CrelK′` before any frozen re-thread).

## Do-not-retry ledger (each build-refuted; witnesses kept)
- Type-occurrence Γ-premises for non-escape (the `U {ℓ} Int` dormant-cap case refutes them; the
  CARRIER axis is the one that works).
- `liveCapsResolveC_returnEscape` as stated — FALSE: the laundered-re-handle witness
  (`Bang/Witness/ReturnEscapeReach.lean`) is a genuine soundness hole, resolved by ADR-0063, not a proof.
- Lazy-vthunk carrier relaxation (relocates the wall to FORCE, underivable).
- `lwsvg_closed_regrade` (scale-gates couple grade↔liveness even closed; witness `d81515c`).

## Banked assets (axiom-clean, load-bearing for the resume)
- **run_rename keystone** (`Config.run` commutes with injective id-renaming) + `run_plug_reshape`.
- **carrier-subst keystone** `liveCapsResolve{V,C}_subst_gen` + `_weaken` (gated @ `da67c2d`).
- **KrelS `splitAtId` decomp** (Units 1+2; the MISS answer-type-determinism wall DISSOLVED —
  `splitAtId` never tests `handlesOp`). One documented SKIP-relocation residual.
- `seq_unit_proof` residual (cap-subst-commutes, off the critical path) — the `seq_unit` flag.
- **`dispatchOn_rename` custom arm (BANKED HERE 2026-07-09, #44 rung-2):** one doc-commented
  sorry in `Bang/Meta/LR.lean` — `renameH` is identity-on-custom while the RHS renames p+clauses;
  the clean fix is the `.map` clause traversal + its ~15-lemma renameH_shiftFrom/substFrom ripple
  (nested-inductive termination twin of `capsCls`), which is THIS path's re-index shape. Feeds
  only the flagged `lr_sound`; manager-ruled banked at the rung-2 landing (ADR-0087 §Status).
- **binary-LR custom arms ×2 (BANKED HERE 2026-07-09, #44 Stage-3):** two doc-commented sorries in
  `Bang/Meta/BinaryLR.lean` — `crelK_fund`'s `handleCustom` arm + `krelS_refl`'s `customF` arm, the
  exhaustiveness cases forced by ADR-0092 D3's new `HasCTy.handleCustom`/`HasStack.customF`
  constructors. The real proofs are the LR-CUSTOM obligation (contextual equivalence for user
  effects) = #44 STAGE 5's theorem: a `compatK_handleCustom` + `krelS_custom_reinstall`, mirroring
  the `compatK_handleState`/`krelS_state_reinstall` cores. Feed the already-flagged `lr_*` set only
  (no new flagged headline); manager-ruled banked at the Stage-3 kernel landing (ADR-0092 D3/D4).

## Resume protocol
Design-first: an ADR deciding route 1 vs 2 BEFORE any proof work (route 1 touches frozen
statements). Then a fresh proof-engineer grounded on: this brief + ADR-0058/0061/0063 + the
banked branches (`inc5-lr-reindex`, `inc5-comp-grind`, `inc5-opt1-laterLR`, `inc5-opt2-reach`).
Gate per seam: `/gate` on committed content; `lr_sound`/`lr_fundamental` leaving the flagged set
is the finish line.
