# 0043 — ◊4.5b: scoped-seam for nested-wrapping-handler resumption (the `lr_sound` moat scope)

- **Status:** Accepted (build-pinned; the relation-level primitive landed, the sorryAx-zero close scoped to a future kernel session, 2026-06-24)
- **Layer:** C+ (LR metatheory / proof architecture)
- **Depends on / amends:** [0041](0041-cap45-recursive-fragment-needs-later-modality.md) (the `▷` subsystem ◊4.5b lives in), [0039](0039-cap4-non-triangleright-split.md) (the ◊4/◊4.5 split), [0026] (the verified-core / tested-superset descent), [0025] (deep resumptive handlers), [0023] (handler dispatch)

## Context

◊4.5b's resumptive logical relation is one obligation from a fully axiom-clean `lr_sound`:
`krelS_splitAt_decomp`'s **handleF-MISS** case — a handler dispatch whose captured continuation,
up to the catching handler, contains a **non-catching handler** (the "nested-wrapping" / "wrap-MISS"
edge). Everything else is closed: throws/state/txn equivalence at the catching frame, and resumption
through a captured continuation (`krelS_append`, the Biernacki §5.4 Lemma-2 config-append, build-proven).

Two fully-general closes were build-confirmed DEAD before this decision:
- **Pinned-index reshape** (re-index `KrelS` by a determined answer type): `KrelS`-answer-determinism
  is **FALSE** — the `letF` clause existentially quantifies the continuation type `B`, so two
  derivations over the same stacks pick different answers. Recorded as a rabbit-hole in task #10.
- **No-strip / circular**: building the goal `KrelS` at `Dᵢ` directly needs the reinstalled handler's
  own resume conjunct — exactly what is being proven; `krelS_splitAt_decomp` lacks that interface.

## Decision

**The nested-wrapping-handler-resumption edge is excluded by a SCOPED SEAM, not closed.** The
relation-level primitive `NoWrapMiss` is landed; the sorryAx-zero close (which requires a TYPED
`CrelK`) is build-pinned and deferred to a dedicated kernel session.

### What landed (relation level — `2b4479b`, whole-tree green)

`Bang/Operational.lean` gains a standalone predicate:

```
NoWrapMiss : EvalCtx → Label → OpId → Prop
| [],                _, _  => True
| (handleF h :: K),  ℓ, op => handlesOp h ℓ op = true ∨ splitAt K ℓ op = none
| (_ :: K),          ℓ, op => NoWrapMiss K ℓ op
```

`NoWrapMiss K ℓ op` says the dispatch of `(ℓ, op)` reaches its catcher **without passing through a
non-catching handler** (the captured continuation up to the catcher is handler-free). `¬ NoWrapMiss`
is *exactly* the splitAt-wrap-MISS edge. The kernel, `KrelS`, and the whole relation stay **pristine
at `e755afa`** — `NoWrapMiss` touches nothing else.

### Covered / excluded

- **COVERED** (sound + proven): all observation contexts including **legitimate handler stacking** —
  every dispatched op caught by its **nearest** enclosing handler (single-level handling; state-over-
  throws and any focus-installed handler nesting where each op hits its nearest handler; resumption
  through a handler-free captured continuation, via `krelS_append`).
- **EXCLUDED** (the narrow seam): resumption where the captured continuation **up to the catching
  handler contains a non-catching handler** — i.e. a dispatched op is caught by a handler that is
  **not** its nearest enclosing one (it "passes through" a shallower non-catching handler). This is
  the single `krelS_splitAt_decomp` MISS sorry (`Bang/Compat.lean`), the ADR-0026 tested-descent
  boundary: the catching-frame equivalence is fully verified; the pass-through edge is the documented
  descent.

### Why sorryAx-zero needs a TYPED `CrelK` (the deferred close)

To make the MISS obligation vacuous, the biorthogonal closure `CrelK` must range only over stacks
that handle the focus's ops at the nearest handler. **Every simple stack-scope predicate on the
runtime stack `K₁` walls** (build-and-reasoning-confirmed, this session), at one root cause: the
fundamental theorem's handle-arm pushes the focus's **own** handler (`handle h M` runs `M` over
`handleF h :: K₁`), which violates any runtime-stack scope:

- row-indexed `NoWrapMissRow K ε`: walls at `crelK_ret`'s `letF` (row `e → φ` change; no `φ ≤ e`
  without typing);
- row-agnostic "∀ ops `NoWrapMiss`": walls at `crelK_ret`'s `handleF` (passing `handleF h` on a `ret`
  exposes `h`'s masked ops);
- fully-`HandlerFree K₁`: walls at the handle-arm (`HandlerFree K₁ ⊬ HandlerFree (handleF h :: K₁)`).

Distinguishing the focus's **legitimately-pushed** handler from a **context wrap** requires the focus
structure — a `CrelK` re-indexed by typing (`HasCTy`/`HasStack`), threaded through the whole mutual
block and every frozen `Crel` consumer. That is the **pinned-index-reshape order of magnitude** and is
deferred together with it as the **"nested-wrap resumption" kernel project** (see `paths/PATH-cap45-finish.md`).

## Rejected alternatives

- **Pinned-index `KrelS` reshape** — DEAD (answer-determinism FALSE; build-confirmed).
- **`HandlerFree`-restriction ON THE `KrelS` handleF clause** (forbid a handler's tail from holding a
  handler) — OVER-FORBIDS: it bans legitimate handler stacking (state-over-throws is valid + tested;
  the reinstall lemmas build `handleF h :: K` with `K` a handler stack), so it breaks `krelS_refl`.
  The wrap-MISS edge is **narrower** than "no nesting," so it cannot live as a `KrelS` restriction.
- **Scope `lr_sound`'s `ctxApprox` alone** — INSUFFICIENT: the sorry is upstream in `crelK_fund`
  (`= lr_fundamental`), which proves `CrelK` for ALL stacks; its handler/`up` arms carry the obligation
  regardless of how `lr_sound` later instantiates it.
- **Bare `sorry`** — rejected: the seam is STRUCTURAL (`NoWrapMiss` + the documented descent), so the
  limitation is explicit, not papered.

## Consequences

- The kernel and `KrelS` stay pristine (`e755afa`); `NoWrapMiss` is the durable relation-level artifact.
- `lr_sound`/`lr_fundamental` retain the single documented `krelS_splitAt_decomp` MISS sorry — the
  honest moat scope, the verified domain being everything except pass-through resumption.
- The path to sorryAx-zero is fully specified + de-risked-by-isolation: the typed-`CrelK` reshape, a
  dedicated future kernel session (`PATH-cap45-finish.md`).
