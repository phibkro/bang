# 0117 — per-binding effect facts require source provenance

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: Preserve BANG's current strict top-level declaration semantics, but do not publish or
  consume initializer-local effect rows until explicit source binding-occurrence provenance survives
  elaboration. Aggregate checked rows remain authoritative; names, generated prefixes, let-spine
  positions, and separately re-elaborated RHSs are not valid attribution mechanisms.
- **Depends-on**: [0066](0066-surface-type-system.md) (authoritative checked rows),
  [0075](0075-polymorphism-elaborates-to-mono-kernel-bidirectional-decidability.md)
  (monomorphizing elaboration), [0093](0093-module-system-v1-file-modules-elaborate-flat.md)
  (strict flat module lowering)
- **Date**: 2026-07-19
- **Deciders**: operator + Codex, from the per-binding RHS-row falsification probes
- **Ties**: `paths/PATH-per-binding-rhs-row-probe.md`,
  `paths/PATH-top-level-initializer-census.md`,
  `docs/notes/questions/Q34-module-system-tooling-forks.md`

## Context

The module-body work needs to distinguish stable description identity from executable initialization.
An initializer-local effect row would eventually support source-precise diagnostics, per-definition
capability manifests, effect-aware incremental compilation, and safe initialization pruning or
reordering. The checker computes the needed RHS row during final inference, but at that point its input
is an elaborated `Surf` tree rather than a sequence of source declarations.

The completed probe demonstrates that neither obvious mapping is sound. Duplicate source names are
accepted; internal-looking names are user-spellable; aliases can disappear; recursive lowering,
monomorphization, prelude expansion, and ANF introduce source-unowned `let`s. A final-core name or
position therefore does not identify a source binding occurrence. Rechecking each isolated RHS would
create a second elaboration whose environment, specialization sites, and inferred facts can differ
from the authoritative whole-program run.

This is an attribution limitation, not a type-soundness failure. The aggregate final effect row remains
correct, and strict top-level declarations retain their current evaluation semantics.

## Decision

1. **Keep the current language contract.** Ordinary strict top-level declarations, including
   effectful or divergent initializers, remain legal. This ADR does not make libraries inert, make
   `main` the sole executable declaration, or change initialization order.
2. **Keep aggregate rows authoritative.** Existing whole-program and chain-cumulative effect facts keep
   their documented meanings. They must not be relabelled as initializer-local facts.
3. **Require occurrence provenance for attribution.** Any public per-binding row must be tied to a
   stable source binding-occurrence identity that survives elaboration and can be zonked against the
   final inference substitution.
4. **Forbid guessed substitutes.** Binder-name matching, reserved-prefix conventions, outer-let
   position, subtraction of cumulative effect sets, and isolated RHS re-elaboration are not admissible
   implementations of a per-binding fact.
5. **Gate dependent consumers.** Separate compilation, initialization DCE/reordering, per-definition
   capability manifests, or source-precise effect diagnostics must either carry the required provenance
   or use a separately proven semantic mechanism. They may not silently assume attribution exists.

## Why this is deferred infrastructure rather than a cut corner

- No shipped language feature or schema promises initializer-local rows today.
- The current aggregate checker result remains correct; the probe corrected documentation instead of
  weakening the fact to make a feature appear complete.
- Explicit provenance has one hard consumer today—per-binding rows—and one plausible partial consumer,
  file-aware diagnostics. Building a cross-elaborator identity representation before another concrete
  journey needs it would be premature generalization.
- The prohibition on guessed attribution prevents the deferral from accumulating workaround debt.

The balance changes as soon as work crosses the gate below. At that point provenance is prerequisite
work, not optional polish.

## Consequences

- BANG cannot yet truthfully answer “which source declaration contributed this effect?” after
  whole-program elaboration.
- Current execution and acceptance behavior do not change.
- The artifact/link tracer may continue with aggregate body identity, explicit initialization as an
  unresolved link input, import slots, and runtime-label relocation, but it cannot optimize or reorder
  individual initializers using effect guesses.
- A future provenance representation should be introduced by an end-to-end consumer and tested against
  duplicate names, alias erasure, recursive knots, generic specialization, prelude expansion, and ANF.

## Rejected

- **Infer source identity from binder names or generated prefixes** — refuted by duplicate names,
  recursive/plain collisions, and user-spellable internal names.
- **Align source declarations with final let-spine positions** — refuted by disappearing aliases and
  generated monomorphization/ANF bindings.
- **Subtract cumulative rows** — effect rows are sets, so union loses contribution history.
- **Re-elaborate every RHS independently** — produces non-authoritative facts and fails for generic
  declarations that require whole-program specialization sites.
- **Restrict the surface language to avoid provenance** — rejected as an inference from this probe.
  Such a language change needs its own semantic/product justification and migration evidence.
- **Build provenance immediately** — rejected while it has only one hard consumer.

## Revisit if

Reopen before implementing any of the gated consumers above, when a second concrete consumer requires
binding identity, or when independently justified elaborator work can carry occurrence provenance at
low marginal cost. Once one of those triggers fires, continuing to defer becomes technical debt.
