# ADR-0018 · Effect-row algebra — lacks-constrained row quantifiers (set discipline)

- **Status:** Accepted
- **Date:** 2026-06-21 (extracted from bang-lang-wasmfx/ADR-effect-row-algebra.md as part of the wasmfx merge)
- **Layer:** K (kernel — extends ADR-0001's effect-row algebra)
- **Related:** 0001 (rows-as-Finset; the base commitment this extends), 0008 (free-monad eval; consumes the row algebra), 0016 (two-hop architecture; this is what enables the spec's `no_accidental_handling`), Biernacki et al. POPL 2018 §5.4

## Context

bang-lang's effect rows are idempotent `Finset Label` (ADR-0001): `+` (choice) is idempotent, commutative, associative, with unit `0`. This was chosen for the effect-grade semiring. ADR-0001 fixed the row *carrier*; what was not yet fixed is the **row-quantification discipline** that prevents a soundness leak that Phase A of the Lean verification could otherwise silently introduce.

The reference point is Biernacki et al. (POPL 2018, *Handle with Care*). Their general model carries `ρ`-maps and a `lift` operator solely to distinguish *duplicate* effects in a row (`⟨l,l⟩ ≠ ⟨l⟩`). Their §5.4 states that with disjoint / unique labels this machinery vanishes and a row is a plain set — at the cost of expressive power (no two handlers for the same label). bang-lang's `Finset` rows are exactly that set fragment.

## Decision

**Adopt the set discipline (Route B), enforced by constrained row-quantification.**

1. **Row variables carry a "lacks" constraint**: `∀(α # L). τ`, where `L` is a set of effect labels `α` may not contain. (Rémy / Links / Hillerström–Lindley style.)
2. **Row instantiation is well-formed only when the instantiating row is disjoint from `L`.** Encoded in `Bang/Spec.lean §0.5` as `rowinst_requires_disjoint`.
3. **No `lift` / `ρ`-map machinery.** `compat_lift` is deliberately omitted from `Bang/Compat.lean`.

### Why the constraint is mandatory, not cosmetic

Without it, instantiating `α` in `∀α. ⟨l | α⟩` with a row containing `l` lets a handler for `l` ACCIDENTALLY capture an operation that arrived through `α`. That is a loss of **abstraction-safety**, not merely of expressiveness. The constraint discipline is precisely the proof obligation that makes the ρ-map-free (set) model SOUND — it is what we pay in exchange for deleting the freeness apparatus. The invariant has a name: `no_accidental_handling` (`Bang/Spec.lean §0.5`).

### If multi-instance capability is later needed

Recover it via **fresh effect labels (instances)** — `⟨State#1, State#2⟩`, still a set — à la Eff / lexically-scoped handlers (Biernacki et al. POPL 2020). NOT via `lift` / `ρ`-maps, which would re-introduce a non-idempotent (multiset) row algebra and break everything below.

## Consequences

### Cost
- Effect-polymorphic functions require lacks-constrained quantifiers; the type-checker must track and discharge disjointness side-conditions.
- No two handlers for the same bare label (acceptable; use instances if needed).

### Benefit — the monotonicity asset (`Bang/Distribution.lean`)

Idempotent `+` makes `(Eff, +, 0)` a **bounded join-semilattice** (provable: `eff_join_semilattice`). This is the algebraic precondition for coordination-free distribution:

- **CALM** (Hellerstein): monotone computations need no coordination.
- **CRDTs** (Shapiro et al.): state-based CRDTs *are* join-semilattices; merge = join.

This places bang-lang's `+` at the monotone end of a single structural spectrum that also governs recovery (the "algebra determines mechanism" framing):

| effect-grade structure | recovery (time) | distribution |
|---|---|---|
| semilattice (idempotent) | — | coordination-free (CALM / CRDT) |
| monoid (sequencing) | sequencing w/ identity | ordered, coordinated |
| group (invertible) | rollback (Frobenius / dagger) | compensation |

The same idempotence that *forces* the constrained-quantifier discipline also *delivers* the coordination-freedom story. The conjecture `rowmonotone_coordination_free` (`Bang/Distribution.lean`) marks the latent result; it is a separate paper, NOT part of the verification spine.

## Related artifacts

- `Bang/Spec.lean §0.5` — well-formedness rule + abstraction-safety invariant
- `Bang/Compat.lean` — `compat_lift` deliberately omitted (comment line 96)
- `Bang/Distribution.lean` — semilattice fact + CALM conjecture
- `references/papers/effects-handlers/biernacki-popl18-handle-with-care.pdf` — §5.4 (set-row fragment); §I (group/Frobenius end of the spectrum)

## Rejected alternatives

| option | why not |
|--------|---------|
| Adopt full Biernacki ρ-map / lift machinery | Buys multi-instance for the same label at the cost of much heavier metatheory; bang-lang doesn't need it (use fresh labels instead). The set fragment is provably the corner of their construction |
| Skip the lacks-constraint and trust unification not to alias | Loses abstraction-safety silently; a handler can capture operations arriving through a polymorphic row variable. The bug is invisible at use sites |
| Modal-row alternative (Tang-Lindley capabilities) | Different design fork; possible but commits to a capability discipline rather than row discipline. Out of scope for this ADR; would replace, not extend, 0001 |

## Revisit if

- Multi-instance capability for the same effect label becomes a recurring user need beyond what fresh-label instances comfortably support → reconsider modal/capability rows (separate ADR).
- The lacks-constraint discharge becomes a type-inference bottleneck in practice → consider partial inference + explicit annotation at boundaries, not weakening the constraint.
- A use case emerges where the semilattice asset (`rowmonotone_coordination_free`) needs to land in the spine rather than as a flagged conjecture.
