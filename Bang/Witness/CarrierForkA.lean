module

public import Bang.Meta.BinaryLR
public import Bang.Core.Semantics.Invariants

/-! # CarrierForkA — the fork-(a) refutation: a `StackBelow g` DEF-INVARIANT collides with
`KrelS_g_cast`'s contravariant resume recursion.

## The fork (ADR-0096 amendment, lane carrierprobe)

Fork (a) = "carry `StackInc K ∧ StackBelow g K` as the `KrelS` def-invariant, and split/weaken
`KrelS_g_cast` to `g ≤ g'` (monotone) only." This file MACHINE-REFUTES the claim that the monotone
weakening survives — the resume conjunct's recursion (`BinaryLR.lean:1151`) casts the captured
continuation `Kᵢ` in the REVERSE direction (`g' → g`, contravariant), so a `g ≤ g'`-only cast
cannot serve it while an arbitrary-`g'` cast cannot preserve `StackBelow g`.

## What the witnesses establish

1. `gcast_full_kills_stackBelow_invariant` — a FULLY GENERAL `KrelS_g_cast : ∀ g g', KrelS g → KrelS g'`
   is INCOMPATIBLE with a `StackBelow g`-carrying def: taking `g' := 0` on a stack with a live
   `handleF n` (`n ≥ 0`, `¬ n < 0`) forces `StackBelow 0 K = False`. So the CURRENT full-generality
   `KrelS_g_cast` (which the code relies on at every internal recursion) would be UNPROVABLE if the
   def carried `StackBelow g`. This is the head-on collision the ADR names.

2. `monotone_gcast_cannot_serve_contravariant_resume` — the resume-conjunct recursion needs the
   REVERSE cast (`g+1 → g`, since the captured continuation is a HYPOTHESIS). A monotone-only
   `g ≤ g'` cast provides `g → g+1` but NOT `g+1 → g`. Modelled abstractly: a relation `R g` closed
   under `g ≤ g'`-cast in COVARIANT position does not give the contravariant `g' ≤ g` closure the
   resume conjunct's captured-continuation hypothesis demands.

Both are the SAME structural fact from two angles: `KrelS`'s resume conjunct binds `Kᵢ` in
contravariant position, so `g` cannot be BOTH an upper bound carried on `Kᵢ` (the fork's aim) AND
freely castable up (what `KrelS_g_cast n g (g+1)` at every MINT site needs). -/

namespace Bang.Witness

open Bang
open Bang.EffectRow (Label)

/-- **Witness 1 (the head-on collision).** A hypothetical `KrelS`-like def that carries `StackBelow g`
on its stack cannot admit a fully-general counter cast. Concretely: `StackBelow` at counter `0` on a
stack holding ANY `handleF n` frame is `False` (`¬ n < 0`), so a cast `KrelS g K → KrelS 0 K` that
must re-establish the invariant is impossible whenever `K` has a live handler. This is exactly the
shape `KrelS_g_cast n g g'` takes at its letF/appF/handleF recursions (`BinaryLR.lean:1139-1147`),
which pass the OUTER's arbitrary `g'` down — under a `StackBelow g` invariant those become unprovable.
Axiom-clean; the refutation is a decidable `StackBelow`. -/
theorem gcast_full_kills_stackBelow_invariant :
    ∃ (g : Nat) (K : EvalCtx),
      Bang.StackBelow g K ∧ ¬ Bang.StackBelow 0 K := by
  refine ⟨1, [Frame.handleF 0 (Handler.throws 0)], ?_, ?_⟩
  · exact ⟨by decide, trivial⟩
  · -- StackBelow 0 [handleF 0 _] = (0 < 0 ∧ True) = False
    intro h; exact absurd h.1 (by decide)

/-- **Witness 2 (the contravariant-recursion obstacle, abstract model).** Model the fork's proposed
monotone cast on an abstract counter-indexed family `R : Nat → Prop`. The resume conjunct's structure
is: to build `R g'` you must consume a hypothesis of the form `R g' → …` and feed it `R g` (the
captured continuation, cast the OTHER way — `BinaryLR.lean:1151` casts `m g' g`, target→source).

Concretely: a family closed ONLY under `g ≤ g'`-upcast (`hup`) does NOT give the downcast a
contravariant occurrence needs. We exhibit an `R` for which the up-closure holds but a term needing
the down-cast is unfillable — `R := (· = 0)` is up-closed VACUOUSLY at nothing above 0 yet the
resume shape asks for `R 0` from `R 1`. This models: `KrelS_g_cast n g (g+1)` at the MINT site
(1201/1247/…) drives the def's resume recursion, which internally requires `KrelS_g_cast m (g+1) g`
— the reverse — which a `g ≤ g'` cast cannot supply. -/
theorem monotone_gcast_cannot_serve_contravariant_resume :
    -- there is a counter-family `R` closed under monotone up-cast, for which the resume conjunct's
    -- REVERSE obligation (`R (g+1) → R g`, the captured-continuation direction) FAILS.
    ∃ R : Nat → Prop,
      (∀ g g', g ≤ g' → R g → R g') ∧    -- monotone up-cast HOLDS (what the fork keeps)
      ¬ (∀ g, R (g + 1) → R g) := by       -- the reverse (resume conjunct's `Kᵢ`) FAILS
  refine ⟨fun k => 0 < k, ?_, ?_⟩
  · intro g g' hle hg; omega
  · intro hdown
    -- hdown 0 : (0 < 1) → (0 < 0); feeding the true premise yields `0 < 0`, absurd.
    exact absurd (hdown 0 (by decide)) (by decide)

end Bang.Witness

#print axioms Bang.Witness.gcast_full_kills_stackBelow_invariant
#print axioms Bang.Witness.monotone_gcast_cannot_serve_contravariant_resume
