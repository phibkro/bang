# ADR-0005 · Reactivity is an operator distinction, not a separate kernel form

- **Status:** Accepted
- **Date:** 2026-06-21 (rewritten from earlier glyph-specific version of 2026-05-31)
- **Layer:** K (kernel — semantic decision)
- **Related:** 0007 (no implicit force, the operator-grammar sibling), 0006 (same no-hidden-channels principle), CBPV foundation

## Context

The original design had four binding forms (`let` / `let mut` / `let sig` / `let tvar`) and explicitly flagged that "three mutable forms is one or two too many." Two semantic models were on the table:

1. **Signals as a distinct kernel form** — a `sig` primitive with built-in subscription machinery.
2. **Reactivity as a property of an equation over thunks** — reactivity falls out of equating a name with an unforced description; no separate primitive needed.

This ADR settles which model the kernel commits to. The decision is semantic, not syntactic — the specific operator spellings live at the surface layer (liquid) and may change.

## Decision (semantic — K-layer)

1. **Drop `sig` as a kernel binding form.** Bindings reduce to three: immutable (`let`), mutable scalar (`mut`), transactional cell (`tvar`). Adding a fourth is a spec change requiring a K-ADR.
2. **Reactivity is operator-distinguished from binding.** There is a syntactic distinction between *introducing* a name and *equating* it with a value. Reactivity is what *equation-over-unforced-descriptions* means; it is not a property of the binding site.
3. **Sampling = forcing in equate position.** Severing a reactive link and evaluating-now are the same act; no separate untrack/sample primitive (cf. SolidJS `untrack`, Vue `toRaw`, MobX `untracked`).

## Rationale

- **Equation reads as mathematical equality, not assignment.** `x equates-with y` synchronizing is what equality means over thunks, not a hidden event fired by a write. Reading at scale = reading equations that hold, not tracking which statements fire which events.
- **Force already does kind-shift** (description → value; see ADR-0007). Reusing it in equate position cashes out as sampling at no extra primitive cost: severing-the-link and evaluating-now are unified.
- **Concept reduction.** Four reactive concepts (declare / assign / create-signal / update-signal) collapse to two operators whose distinction *is* the reactive boundary.
- **Smaller kernel = smaller spec to formalize.** Matches the five-primitive invariant (see CLAUDE.md).

## Rejected alternatives

| option | why not |
|--------|---------|
| Keep `sig` as a distinct kernel form | More concepts; the original design doc itself doubted it; violates the five-primitive invariant |
| Make all `mut` reads tracked (subscription always on) | Subscription cost must be opt-in / where asked, not always-on |

## Consequences

- K0 semantics has **3 binding forms**.
- Reactivity is a property of *equations*, not of *binding sites*.
- Force in equate position is sampling — no separate untrack primitive in the kernel.
- **Residue — silent subscription.** The equate site is honest, but the *subscribe site* (a read inside a reactive context) stays implicit. This is the one remaining hidden channel (every other dependency channel in BANG is explicit: arguments, effect rows per ADR-0001, capture per ADR-0006). **Tracked, not resolved.** Mitigations: compiler errors on illegal introduce/equate usage (introduce-twice, equate-before-introduce); LSP rendering of reactive edges to make the subscription graph visible.
- **Load-bearing invariant — thunk NON-memoization** *(surfaced by rung 4, 2026-06-23).* Pull-based reactivity ("each force re-samples the current state") works *because* the kernel thunk is genuinely unmemoized — there is no `Comp` memo cache, so `force` re-evaluates by construction. **Verified**: `Bang.Surface.cell_reflects_latest` (a reactive cell reads the latest write, for arbitrary initial + written value; axioms `[propext]`). This makes thunk non-memoization a **load-bearing semantic invariant of reactivity**, not a free implementation choice. Per invariant #7 (performance is second-class), this is aligned — but it must be stated, not assumed.

## Current surface spelling (liquid — S-layer, not load-bearing)

The current surface chooses `:` to introduce, `=` to equate, with sampling via force-in-equate-position. These glyphs may change as the surface evolves; the K-decision is that the introduce/equate distinction *exists at all*, not which characters spell it. See `ROADMAP.md` for the surface-layer liquidity policy.

## Revisit if

- The introduce/equate semantic distinction (independent of spelling) proves confusing in real programs — e.g. the introduce/equate distinction on re-entry into loop bodies / recursive calls (does each entry re-introduce, and is that an event?). Open semantics question to settle against a real ≥100-line module before final lock.
- The silent-subscription residue bites in practice (a missed/spurious sample causing a wrong subscription that's hard to see) → consider marking the *subscribe site* explicitly at the read position, closing the last hidden channel at an ergonomic cost.
- Per-field reactivity turns out to need an explicit marker after all.
- **Thunk memoization is ever added** (a perf optimization — caching a forced thunk's WHNF). This would SILENTLY BREAK pull-based reactivity (a reactive cell would freeze on its first sample). Before adding any such cache, the non-memoization property must be made an asserted kernel invariant and reactivity re-derived (e.g. a memo-bypass for live cells). `cell_reflects_latest` is the regression test that would catch it.
