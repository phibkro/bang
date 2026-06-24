# 0043 — ◊4.5b: scoped-seam for nested-wrapping-handler resumption (the `lr_sound` moat scope)

- **Status:** Accepted — and the seam is now the **verified-FINAL** answer for this edge: the cheap typed-`CrelK` close (Architecture D) was build-probed and is **NO-GO** (2026-06-24; see "Probe result" below). The only remaining close is the heavy index-everything reshape (rabbit-hole, 4–7 sessions + a frozen-statement break), not worth one tested-descent edge.
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
- ~~The path to sorryAx-zero is fully specified~~ → **PROBED, NO-GO** (see below). The seam is final for this edge.

## Probe result (2026-06-24) — Architecture D (cheap typed-`CrelK`) is NO-GO

A 5-agent design panel recommended **Architecture D** (literature-canonical typed `CrelK` that *proves* the
MISS rather than vacating it; scope as a PREMISE not an index, so the frozen statements survive;
~3–4 sessions): use `HasStack`'s answer-index to recover the junction answer type the MISS sorry says
`KrelS` lacks. A bounded GO/NO-GO **build probe** (branch `typed-crelk-probe` @ `ffac1b0`,
`Bang/Compat.lean` ~1466–1597) split the bet and the build cleanly arbitrated it:

- **Answer-projection half WORKS** — `hasStack_append_handleF_split` is PROVEN, `#print axioms` = `[propext]`.
  `HasStack` *does* carry the **bottom** junction answer `Dᵢ` invariantly down the left stack. The panel was right here.
- **Strip half WALLS (the killer)** — `krelS_strip_handleF` carries `sorryAx`. The genuine structural wall is the
  `letF`/`letF` recursion: the strip's IH demands the recursive `KrelS` at a **returner** hole, but `KrelS.letF`
  yields a tail at an **arbitrary existential intermediate** `B` that `HasStack` typing of the LEFT stack does
  **not** pin onto the `KrelS` index — there is **no `KrelS ⇒ HasStack` bridge** (the logical relation is one-way:
  typing ⇒ related, never the reverse), and even if `B` were pinned it need not be a returner.

So `HasStack` fixes the **answer-projection** (bottom) but the strip's recursion needs the **intermediate**
`KrelS` hole typed — which the one-way LR cannot supply. **Architecture D only RELOCATES the leak** (E's panel
finding "`KrelS.letF` existential `B` leaks" is correct *at the build level* and survives full left-stack typing).

**Consequence:** the only path to sorryAx-zero is typing `KrelS`'s **intermediate** holes — i.e. re-indexing the
whole mutual block (Architecture A / heavy-D), which the panel scored as 4–7 sessions **with** a forced
frozen-statement break. Not worth it for a single tested-descent edge. **The ADR-0026 scoped seam is the
verified-final answer.** Durable evidence: `typed-crelk-probe @ ffac1b0` (both lemmas committed, the wall
documented inline at the `sorry`).
