/-
  Bang/Operational.lean — the operational-semantics hub (re-exporting barrel).
  ─────────────────────────────────────────────────────────────────────────
  The former 969-line fan-in-11 hub, split into four deep submodules per the
  4 concerns (core-overview.md §6) — behavior-preserving, no re-proof:

    Bang.Semantics.Subst       de Bruijn substitution + shift (§1.3a/b)
    Bang.Semantics.Dispatch    handlesOp / splitAtId / dispatchOn / idDispatch
    Bang.Semantics.Eval      Source.step / Source.eval / the CK machine
    Bang.Semantics.Invariants  WellCounted / StackBelow freshness (ADR-0055)

  This barrel re-exports all four so `import Bang.Semantics; open Bang` keeps
  resolving the full public surface (Source.step, splitAtId, Comp.subst,
  handlesOp, dispatchOn, idDispatch, plug, NonEscape, HasConfig, CapResolves, …).
  Theorem STATEMENTS (preservation, progress, type_safety, effect_sound,
  zero_usage_erasable) live in Bang/Spec.lean.
-/

module

public import Bang.Semantics.Subst
public import Bang.Semantics.Dispatch
public import Bang.Semantics.Eval
public import Bang.Semantics.Invariants
