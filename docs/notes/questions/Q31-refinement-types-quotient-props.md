---
type: design-question
title: "Refinement types surface / quotient-proposition underlying: `Nat`, decidable checking, and the road to dependent types"
description: "refinement types (surface) over quotient-truncated decidable props (kernel); the road to dependent types"
status: open
area: type-system
ties: ["Q27", "ADR-0027", "ADR-0067", "ADR-0073"]
see-also: ["#47"]
---
**Question**: how does BANG get value-indexed precision — starting with `Nat` (a floor for total
recursion), reaching toward refinement and eventually dependent types — WITHOUT making type-checking
undecidable or the kernel un-verifiable?

**Why it matters** — three threads converge here. (1) `Nat` = the floor that turns measure-recursion
(factorial, countdown) TOTAL — `#47` certifies only STRUCTURAL recursion because unbounded ℤ (ADR-0067)
has no floor, so `($sum)(n-1)` genuinely diverges on negatives and correctly stays `Div`. (2)
Refinement types (`{n : Int // n ≥ 0}`) are the full form of "make illegal states unrepresentable"
(SOUL) — negative-`Nat`, out-of-bounds indices, div-by-zero become unrepresentable BY CONSTRUCTION.
(3) Dependent types NEED a total language (type-level computation must terminate to be decidable) — so
the total fragment (`#47`) is their prerequisite brick.

**The architecture (operator's direction — the load-bearing design):**
```
SURFACE (user-facing)   refinement types   { n : Int // P n }      ergonomic; illegal states
                                                                    unrepresentable; Liquid Haskell / F* / Dafny lineage
UNDERLYING (kernel)     QUOTIENT props     P realized as a         proof-IRRELEVANT (a subsingleton) —
                        (truncation ∥P∥ =  quotient by the total   the checker needs only that a proof
                        the (-1)-trunc)    relation → subsingleton  EXISTS, never to compare witnesses
CHECKING                decidable          discharge P via a        FEASIBLE: no witness-tracking (proof
                                           `Decidable`/decision     irrelevance) + the total fragment (#47)
                                           procedure                ensures the predicate's own evaluation halts
```
Why the quotient layer is the crux: proof-RELEVANT dependent checking is where feasibility dies (you
must compare proof terms, and with non-termination that's undecidable). **Propositional truncation via
QUOTIENT collapses all proofs of `P` to one point** → proof irrelevance → checking a refinement =
DECIDING `P` (a decision procedure), not comparing proofs. **`quotient underlying, refinement
surface`**: the kernel manipulates quotient/truncated propositions (verified, decidable), the user
writes the ergonomic subset type.

**The axiom-clean bonus (bang-specific):** `Quot.sound` is ALREADY one of BANG's trusted-3 axioms
(`{propext, Classical.choice, Quot.sound}`). The quotient foundation is on-hand and adds NOTHING to the
trust base — the underlying mechanism is already in the axiom budget. (And `propext` + proof
irrelevance are the same proof-collapsing move at the `Prop` level.)

**`Nat`, three ways (the concrete near-term instance — see also ADR-0073 §2 / #47):**
```
                     free termination     arithmetic    new machinery         expressiveness
inductive Nat        ✓ (structural — #47  O(n) Peano    none (rides data)     just Nat
  Zero | Succ           certifies it AS-IS: n-1 = the
                        Succ-predecessor subterm)
refinement Nat       ✗ (needs measure +   O(1) Int      quotient props +      Nat, {0≤i<len}, {n>0}, …
  {n:Int // n≥0}         floor reasoning)                a decision procedure  (the general mechanism)
stratified (Lean's)  ✓ structural for proof/type-level ⊕ efficient Int runtime ⊕ verified bridge
                        — verified core + tested superset + explicit seam (the project's signature move)
```
Near-term: **inductive `Nat` is the minimal win** — it rides `data` + the #47 structural checker with
ZERO new type machinery, making factorial-on-`Nat` total for free (measure-recursion collapses into
structural recursion: `n-1` IS `match n { Succ(m) -> m }`). Refinement types are the bigger, later
fork this question is really about.

**Options**: (1) **inductive `Nat` now** (rides #47, no new machinery — the incremental floor). (2)
**refinement types** with quotient-truncated decidable propositions (the operator's direction — the
general "unrepresentable by construction" mechanism; needs a decision procedure + the truncation layer).
(3) **full dependent types** (Π/Σ, `Vec n`) — the far end; rests on (2) + the total fragment. (4) none
(stay simply-typed + inductive data).

**Recommended**: inductive `Nat` opportunistically now (it's free once #47 lands); record refinement-
types-over-quotient-propositions as THE intended path to value-indexed precision (decidable by
construction, axiom-clean via `Quot.sound`), design-first when it's taken up. It sits post-polymorphism
(ADR-0027) — refinements interact with the poly lift (a refined generic type) and with grades (Q27).

**Blocked on**: the total fragment (`#47`, in flight — the termination floor + decidable type-level
evaluation); polymorphism (ADR-0027) for refined generics; a decision-procedure story (how far: syntactic
· `Decidable` instances · SMT). All post-v1.

**Revisit signal**: taking up `Nat` (do it the moment #47 lands — free total factorial); OR array/index
safety, positivity, or div-by-zero pressure (the refinement payoff); OR when the type system's power
axis (Q27 grades, ADR-0027 poly) is next lifted — refinements are the same "richer types" frontier.
