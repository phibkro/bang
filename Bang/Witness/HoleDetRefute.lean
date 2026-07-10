module

public import Bang.Meta.BinaryLR
public import Bang.Core.Semantics.Invariants

/-! # HoleDetRefute — the census4 SKIP wall, made a standalone machine-checked FALSIFIER.

## The question this file decides (ADR-0096, PROPOSED AMENDMENT ③, probe route α)

The census4 SKIP-arm close needs `Cb' = C'`: the strip's re-decomposed outer hole (`Cb'`) must equal
the ORIGINAL outer hole (`C'`) over the SAME shared tail at the SAME answer. That is the statement
**`krelS_hole_det`** — "a `KrelS` hole is determined by (stack pair, answer)":

> `∀ n C₁ C₂ D e g K₁ K₂, KrelS n C₁ D e g K₁ K₂ → KrelS n C₂ D e g K₁ K₂ → C₁ = C₂`.

The ADR text asserts this is FALSE for `letF`/`appF`-headed tails: "the hole `F q A` / `arr q A B`
carries a value-type `A` the frame body does not pin (the `letF` clause existentially binds `A`)".
Per the operator's refute-first discipline, a confident "X is false" is gated EXACTLY like a
confident "X is proven": the evidence is a machine-checked `False` from `krelS_hole_det` taken as a
hypothesis `H`. This file BANKS that falsifier as a do-not-weaken regression witness.

## What the witness establishes

`krelS_hole_det_refuted` — from `krelS_hole_det` (as a hypothesis `H`, so the refutation is
axiom-clean and independent of any in-file `sorry`), derive `False`. The counterexample is the stack
pair `K = [letF (ret v₀), appF vunit]` (a `letF` head over an `appF` tail), self-related:

* the `appF vunit :: []` TAIL relates at a FIXED answer `D = F 0 unit` (the arg constrains only its
  own type `unit`; the nil under it forces the tail answer);
* the `letF (ret v₀)` HEAD gives hole `F q A` for ANY `A`, because at index `n = 0` the `letF` body
  relation (`∀ m < 0, …`) is VACUOUS — nothing pins `A`.

So `K` relates BOTH at hole `F 0 unit` AND at hole `F 0 int` — SAME stacks, SAME answer `D = F 0 unit`
— and `F 0 unit ≠ F 0 int` (structurally, independent of the abstract `Mult`). `krelS_hole_det`
collapses this to `F 0 unit = F 0 int`, absurd.

This CONFIRMS: the census4 wall is a genuinely-FALSE statement (route: the hole needs to be carried
as DATA, not re-derived), NOT merely a hard proof. The refutation does not depend on `0 ≠ 1` in
`Mult` (which can fail in a trivial semiring) — it separates on the value-type `unit` vs `int`. -/

namespace Bang.Witness

open Bang
open Bang.EffectRow (Label)

variable {Eff  : Type} [Lattice Eff] [OrderBot Eff]
variable {Mult : Type} [CommSemiring Mult] [DecidableEq Mult]
variable [EffSig Eff Mult]

/-- The hole-determinacy statement the census4 SKIP close would need. Stated here abstractly so
`krelS_hole_det_refuted` is axiom-clean and self-contained (`H` is a hypothesis, not a `sorry`). -/
abbrev KrelSHoleDet (Eff Mult : Type) [Lattice Eff] [OrderBot Eff]
    [CommSemiring Mult] [DecidableEq Mult] [EffSig Eff Mult] : Prop :=
  ∀ (n : Nat) (C₁ C₂ D : CTy Eff Mult) (e : Eff) (g : Nat) (K₁ K₂ : Stack),
    KrelS n C₁ D e g K₁ K₂ → KrelS n C₂ D e g K₁ K₂ → C₁ = C₂

/-- The `appF vunit :: []` tail relates at answer `D = F 0 unit` (the nil under it forces the tail
hole/answer to `F 0 unit`; the `appF` arg constrains only its own `unit` type). Used as the SHARED
tail whose answer both hole-witnesses agree on. -/
public theorem appF_tail_relates :
    KrelS 0 (CTy.arr (0 : Mult) VTy.unit (CTy.F (0 : Mult) VTy.unit))
      (CTy.F (0 : Mult) VTy.unit) (⊥ : Eff) 0
      [Frame.appF Val.vunit] [Frame.appF Val.vunit] := by
  have hnil : KrelS 0 (CTy.F (0 : Mult) VTy.unit) (CTy.F (0 : Mult) VTy.unit) (⊥ : Eff) 0
      ([] : Stack) [] := by
    rw [krelS_nil]
    refine ⟨rfl, fun q A hC v₁ v₂ _ _ _ => ?_⟩
    exact coApproxC_le_zero _ _
  have hvrel : VrelK (Eff := Eff) (Mult := Mult) 0 VTy.unit Val.vunit Val.vunit := by
    rw [VrelK, BaseRel]; exact ⟨rfl, rfl⟩
  have hcl : Val.Closed Val.vunit := fun k => rfl
  exact krelS_appF_intro (q := 0) hcl hcl hvrel hnil

/-- A `letF (ret v₀)` head over the shared `appF vunit` tail relates at hole `F 0 A` for BOTH
`A = unit` and `A = int`, with the SAME answer `D = F 0 unit` — the `letF` body relation is vacuous
at index `n = 0`, so `A` is completely unconstrained. -/
public theorem letF_relates_at_two_holes :
    KrelS 0 (CTy.F (0 : Mult) VTy.unit) (CTy.F (0 : Mult) VTy.unit) (⊥ : Eff) 0
      [Frame.letF (Comp.ret Val.vunit), Frame.appF Val.vunit]
      [Frame.letF (Comp.ret Val.vunit), Frame.appF Val.vunit]
    ∧
    KrelS 0 (CTy.F (0 : Mult) VTy.int) (CTy.F (0 : Mult) VTy.unit) (⊥ : Eff) 0
      [Frame.letF (Comp.ret Val.vunit), Frame.appF Val.vunit]
      [Frame.letF (Comp.ret Val.vunit), Frame.appF Val.vunit] := by
  have htail := appF_tail_relates (Eff := Eff) (Mult := Mult)
  refine ⟨?_, ?_⟩
  · exact krelS_letF_intro (A := VTy.unit) (q := 0) (φ := ⊥) le_rfl
      (fun m hm => absurd hm (Nat.not_lt_zero m)) htail
  · exact krelS_letF_intro (A := VTy.int) (q := 0) (φ := ⊥) le_rfl
      (fun m hm => absurd hm (Nat.not_lt_zero m)) htail

/-- **The falsifier (do-not-weaken).** `krelS_hole_det` is REFUTED: taken as a hypothesis `H` it
forces `F 0 unit = F 0 int` on the `letF_relates_at_two_holes` witness (same stacks, same answer
`D = F 0 unit`), which is absurd. So the census4 wall is a genuinely-FALSE statement — the outer hole
is NOT determined by `(stack pair, answer)`. This is the machine-checked evidence (axiom-clean,
`sorry`-free) that the SKIP close cannot re-DERIVE the hole; it must be CARRIED as data on the resume
conclusion (probe route α), or the LR re-indexed (β). -/
theorem krelS_hole_det_refuted (H : KrelSHoleDet Eff Mult) : False := by
  obtain ⟨h1, h2⟩ := letF_relates_at_two_holes (Eff := Eff) (Mult := Mult)
  have heq : (CTy.F (0 : Mult) VTy.unit) = (CTy.F (0 : Mult) VTy.int) :=
    H 0 _ _ (CTy.F (0 : Mult) VTy.unit) ⊥ 0
      [Frame.letF (Comp.ret Val.vunit), Frame.appF Val.vunit]
      [Frame.letF (Comp.ret Val.vunit), Frame.appF Val.vunit] h1 h2
  exact absurd heq (by simp)

end Bang.Witness

#print axioms Bang.Witness.appF_tail_relates
#print axioms Bang.Witness.letF_relates_at_two_holes
#print axioms Bang.Witness.krelS_hole_det_refuted
