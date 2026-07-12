module

-- Witness examples run `Source.evalTrace` (compiled) at the META phase → `meta import`.
meta import Bang.Core.Semantics.Eval
public import Bang.Core.Semantics.Eval
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Algebra.Order.Ring.Nat

/-! # effect_sound Q14 re-foundation — the runnable refutation witnesses.

The `effect_sound` statement changed shape (Q14): the naive `trace ⊆ e` is FALSE and
"escaping-only" is VACUOUS, so we use the runtime-bound `(ℓ, liveBound K e)` trace with a
per-dispatch `traceWithin`. These `example`s are the machine-checked evidence that:

- the naive alternative is REFUTED (a `done` run records a label NOT `≤` the top-level `e`),
- the chosen `traceWithin` is TRUE on the same runs (each label ≤ its recorded live bound),
- a NESTED handler contributes its label to the live bound (the runtime-bound shape is real).

They pin the ADR ruling: kept as do-not-weaken witnesses. Concrete `Eff = Finset Label` with the
canonical `labelEff ℓ = {ℓ}` (the ADR-0001 instance); the kernel itself stays abstract over `Eff`.

The trace bounds are stated in their DEFINITIONAL fold-shape (`{ℓ} ⊔ (… ⊔ ∅)`, innermost handler
frame first — `liveBound` folds the stack) so the run equalities close by `rfl`; the `Finset`
literal `{1,2}` differs from `{2} ⊔ {1} ⊔ ∅` only in `Quot` representation (`by decide` bridges). -/

@[expose] public section

namespace Bang.EffectTraceWitness
open Bang (Val Comp Handler Frame Result EffSig)
open Bang.EffectRow (Label)

/-- The canonical concrete effect-row signature (ADR-0001): `Eff = Finset Label`,
`labelEff ℓ = {ℓ}`, `Mult = Nat`. Only `labelEff` matters for the trace witnesses; `opArg`/`opRes`
supply the `raise` interface the demo labels use. -/
instance : EffSig (Finset Label) Nat where
  labelEff ℓ := {ℓ}
  opArg _ op := if op = "raise" then some Bang.VTy.unit else none
  opRes _ op := if op = "raise" then some Bang.VTy.unit else none
  labelEff_ne_bot ℓ := Finset.singleton_ne_empty ℓ
  labelEff_sep ℓ ℓ' φ h hne := by
    -- `{ℓ} ⊆ {ℓ'} ∪ φ` with `ℓ ≠ ℓ'` ⟹ `{ℓ} ⊆ φ` (atoms of the powerset lattice).
    simp only [Finset.le_eq_subset, Finset.singleton_subset_iff, Finset.sup_eq_union,
      Finset.mem_union, Finset.mem_singleton] at *
    exact h.resolve_left hne

/-! ## Witness 1 — the Q14 refutation shape

`handle (throws 1) (raise 1)`: the body performs `raise` (label 1) via the handle-bound capability
(`vvar 0`); the `throws` handler aborts, returning the payload as the block result. The program is
well-typed at TOP-LEVEL residual `e = ∅` (the `throws` DISCHARGES label 1 from the row). It runs to
`done`, recording one dispatch `(1, {1} ⊔ ∅)` — the live `throws 1` frame contributes `{1}`. -/

/-- `handle (throws 1) (raise 1)` — the raise aborts to unit. -/
def cThrowRaise : Comp :=
  .handle (Handler.throws 1) (.perform (.vvar 0) "raise" .vunit)

/-- Sanity: the value run agrees with `Source.eval` (the accumulator is inert on the value). -/
example : Source.eval 50 cThrowRaise = Result.done .vunit := rfl

/-- The traced run under top-level `e = ∅`: value `.vunit`, ONE entry `(1, {1} ⊔ ∅)`. -/
example :
    Source.evalTrace (Eff := Finset Label) (Mult := Nat) 50 cThrowRaise ∅
      = Result.done (.vunit, [(1, ({1} ⊔ ∅ : Finset Label))]) := rfl

/-- **REFUTATION of the naive `t ⊆ e`.** The recorded label 1 is NOT `≤ ∅ = e` — the naive bound
`∀ (ℓ,_) ∈ t, labelEff ℓ ≤ e` is FALSE on this `done` run (the `throws` discharged 1 from `e`). -/
example : ¬ (EffSig.labelEff (Eff := Finset Label) (Mult := Nat) 1 ≤ (∅ : Finset Label)) := by
  simp only [EffSig.labelEff]; decide

/-- **The chosen `traceWithin` is TRUE** on the same run: label 1 ≤ its recorded live bound. -/
example :
    Bang.traceWithin (Eff := Finset Label) (Mult := Nat) [(1, ({1} ⊔ ∅ : Finset Label))] := by
  intro p hp; simp only [List.mem_singleton] at hp; subst hp
  simp only [EffSig.labelEff]; decide

/-! ## Witness 2 — a NESTED handler contributes to the live bound

`handle (throws 1) (handle (throws 2) (raise 1))`: the inner body performs `raise` on label 1,
which the INNER `throws 2` does NOT handle (different label) — it aborts PAST it to the OUTER
`throws 1`. When the `raise` fires, BOTH frames are live (`[handleF (throws 2), handleF (throws 1)]`,
innermost first), so the live bound folds `{2} ⊔ ({1} ⊔ ∅)`. Label 1 ≤ that bound; still ⊄ ∅. This
is the shape that makes the runtime bound genuinely INFORMATIVE (option 1) — the bound tracks EVERY
live handler, not just the discharging one. -/

def cNested : Comp :=
  .handle (Handler.throws 1)
    (.handle (Handler.throws 2)
      (.perform (.vvar 1) "raise" .vunit))   -- vvar 1 = the OUTER throws-1 cap (idx shifts under inner handle)

/-- The nested traced run: value `.vunit`, one entry `(1, {2} ⊔ {1} ⊔ ∅)` — both live throws frames
join into the bound. -/
example :
    Source.evalTrace (Eff := Finset Label) (Mult := Nat) 50 cNested ∅
      = Result.done (.vunit, [(1, ({2} ⊔ ({1} ⊔ ∅) : Finset Label))]) := rfl

/-- `traceWithin` TRUE for the nested run: label 1 ≤ `{2} ⊔ {1} ⊔ ∅` (which contains 1). -/
example :
    Bang.traceWithin (Eff := Finset Label) (Mult := Nat)
      [(1, ({2} ⊔ ({1} ⊔ ∅) : Finset Label))] := by
  intro p hp; simp only [List.mem_singleton] at hp; subst hp
  simp only [EffSig.labelEff]; decide

/-! ## Witness 3 — the FALSIFYING bug-shape (why `effect_sound` is NOT true-by-construction)

`effect_sound` couples two independently-computed things: `runTrace` records the label `ℓ` the
CAPABILITY claims (`perform (vcap n ℓ)`); `liveBound` folds labels off the HANDLER FRAMES (`h.label`).
They agree only because dispatch is FAIL-LOUD (`idDispatch` fires iff `handlesOp h ℓ op`, forcing
`h.label = ℓ`). This witness exhibits the machine bug the theorem catches: a cap whose CLAIMED label
differs from the frame it id-matches. -/

/-- `handle (throws 1) (perform (vcap 0 2) "raise")`: the cap claims label 2 but id-matches the
`throws 1` frame (id 0, label 1). The `handlesOp` guard REFUSES (label 2 ≠ frame label 1), so the run
ESCAPES — it never reaches `done`, never records a coherence-violating `(2, {1})`. -/
def cMismatch : Comp :=
  .handle (Handler.throws 1) (.perform (.vcap 0 2) "raise" .vunit)

/-- The mismatch cap ESCAPES (not `done`): with the guard, a cap whose label ≠ its id-matched frame's
label is stuck. So `effect_sound` never sees a bad record. WITHOUT the `handlesOp` guard (identity-only
dispatch, pre-ADR-0054), this same run would `done`-record `(2, {1})` with `2 ∉ {1}` — `effect_sound`
FALSE. That is the theorem's refutation content: it certifies dispatch/liveBound coherence. -/
example : Source.evalTrace (Eff := Finset Label) (Mult := Nat) 50 cMismatch ∅ = Result.escapedCap :=
  rfl

end Bang.EffectTraceWitness

end -- @[expose] public section
