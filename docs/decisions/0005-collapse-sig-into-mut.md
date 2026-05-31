# ADR-0005 · Collapse `sig` into `mut` + the `:`/`=` operator distinction

- **Status:** Accepted
- **Date:** 2026-05-31
- **Related:** reconciles the two spec docs (design.md had `sig`; description-value.md removes it); **force notation set by ADR-0007** (`$`, not `!`; parens group without forcing)

## Context

The design doc had four binding forms (`let` / `let mut` / `let sig` / `let tvar`) and flagged "three mutable forms is one or two too many." The two uploaded spec docs disagreed: `bang-lang-design.md` keeps `sig`; the newer `bang-lang-description-value.md` eliminates it, making reactivity a property of the operator.

## Decision

**Eliminate `sig`.** Reactivity is the **`:` vs `=` operator** distinction on a `mut` binding, read through **equality, not assignment**:

- `x: v` — **introduce** x (the binding comes into being; nothing was watching).
- `x = y` — **equate** x with y. x and y *are* the same thing → they stay synchronized. This is not "assign-and-fire-an-event"; it is an equation that holds, and reactivity is simply what equality *means* when the right side is still an unforced description.
- `x = $y` — equate x with the **value** y forces to *here* (force notation per ADR-0007). The description is collapsed to a point, the link is severed, x is a sampled snapshot. Note `x = (y)` merely *groups* y → still live, **not** a sample (parens don't force).
- `x: v` on an already-introduced `x` — error; use `=`.

Binding forms reduce to **`let` (immutable) / `mut` / `tvar`**. A value is reactive iff it is `mut` and equated with a live (unforced) right-hand side.

## Rationale

- **`=` reads as mathematical equality, not assignment.** An equation doesn't hold at an instant, it holds — so `x = y` synchronizing is not a surprising side effect of a write, it is what equality means over thunks. This is the framing that makes the scheme read cleanly at scale: the reader is reading equations (which just hold), not tracking "does this statement fire an event."
- **`$` in binding position pays for its overloading.** Everywhere else force (`$`, ADR-0007) is "description → value"; in `x = $y` that *is* sampling, because severing the link and evaluating-now are the same act. So the snapshot operation falls out of force meaning what it already means — no separate `untrack`/`toRaw`/`untracked` primitive (cf. SolidJS/Vue/MobX). Spec line to preserve: *forcing in binding position is sampling; the severed link is what forcing costs you.*
- Collapses four reactive concepts (declare / assign / create-signal / update-signal) into **two operators whose distinction *is* the reactive boundary**. The programmer chooses reactivity by choosing live-vs-forced on the right.
- Fewer kernel concepts → smaller semantics to formalize at K0.
- Per-field reactivity falls out: a struct literal is a scope of bindings, `mut` is the (syntactic) wrapper, `point.x = liveExpr` keeps `point.x` synchronized; subscribers of `point.x` only.
- The newer spec doc is the more refined position.

## Rejected alternatives

| option | why not |
|--------|---------|
| keep `sig` as a distinct form | more concepts; the design doc itself doubted it |
| unify `mut` and `sig` by making all `mut` reads tracked | subscription-tracking cost must be **opt-in / where asked**, not always-on |

## Consequences

- K0 semantics has **3 binding forms**; live-vs-sampled is the force distinction on the right-hand side (`x = y` live, `x = $y` sampled).
- **Force notation is `$`, set by ADR-0007** (not `!`; `!` is freed for actor-send). Parens group *without* forcing, so `(y)` is a description, not a sample. The equality reading only holds because grouping and forcing are distinct glyphs (0007) — do not reintroduce paren-force.
- **Residue — silent subscription (the last hidden channel).** The equality reading makes the *write/equate* site honest, but the *subscribe* site stays implicit: a bare (live) right-hand side auto-subscribes inside a reactive context, `$`-forced does not, and that difference is a single easily-omitted `$` that is invisible at the read site. Every other dependency channel in BANG is explicit (arguments, effect rows ADR-0001/0004, capture ADR-0006); silent subscription is the one that remains. **Tracked, not resolved.** Mitigations for now: compiler errors on illegal `:`/`=` usage (introduce-twice, equate-before-introduce) give the agent immediate feedback; the LSP renders reactive edges so the subscription graph is visible even though it isn't in the text.

## Revisit if

- Operator-keyed reactivity proves confusing in real programs — e.g. the introduce/equate distinction on **re-entry** into loop bodies / recursive calls (does each entry re-introduce, and is that an event?) — an open semantics question to settle against a real ≥100-line module before final lock.
- The **silent-subscription residue** above bites in practice (a missed/spurious `$` causing a wrong subscription that's hard to see) → consider marking the *subscribe* site explicitly at the read position, closing the last hidden channel at an ergonomic cost.
- Per-field reactivity turns out to need an explicit marker after all.
