module

public import Bang.Core.Soundness
public import Bang.Core.Grade

/-! # BinopTyping — the F2 discharge for ADR-0065 stage ④ (task #36, ctr slice 1).

Machine-checked corpus: `Comp.binop`-typed programs BUILD a real kernel `HasCTy` derivation
(no longer `binop_untypable`). This is the F2 falsifier from `docs/notes/ctr-design.md` §4.1:
the binop rule types real programs — arithmetic at `int`, comparisons at `Bool = sum unit unit`,
and the G1-shaped `letC (binop …) (ret …)` compute-then-return body (`CtrF1DependsF2` was the
BEFORE — untypeable; these are the AFTER). All at the concrete `EffRow`/`QTT` instance.

`example : HasCTy …` is the right shape (not `#guard` — `HasCTy` is a `Prop`, not `Decidable`):
a green build IS the proof that the derivation exists. -/

namespace Bang.BinopTyping

open Bang
open Bang.EffectRow (Label EffRow)

-- No global `EffSig EffRow QTT` instance exists (it is supplied per-witness); these ⊥-row binop
-- programs use NO effect signature, but `HasCTy` still needs one in scope to elaborate. Take it as a
-- variable (the `BoccRegress` pattern) — the derivations are independent of its content.
variable [EffSig EffRow QTT]

/-- F2.1 — a CLOSED arithmetic binop types at `F 1 int`, ⊥-row: `3 + 4 : F 1 int`. -/
example : HasCTy (Eff := EffRow) (Mult := QTT) []  []
    (Comp.binop BinOp.add (Val.vint 3) (Val.vint 4)) ⊥ (CTy.F 1 VTy.int) :=
  HasCTy.binop HasVTy.vint HasVTy.vint rfl

/-- F2.2 — a CLOSED comparison types at `F 1 Bool` (= `sum unit unit`), ⊥-row: `3 < 4 : F 1 Bool`. -/
example : HasCTy (Eff := EffRow) (Mult := QTT) []  []
    (Comp.binop BinOp.lt (Val.vint 3) (Val.vint 4)) ⊥ (CTy.F 1 (VTy.sum VTy.unit VTy.unit)) :=
  HasCTy.binop HasVTy.vint HasVTy.vint rfl

/-- F2.3 — the OTHER arithmetic ops all type (mul, sub, div): a closed `div` at `F 1 int`. -/
example : HasCTy (Eff := EffRow) (Mult := QTT) []  []
    (Comp.binop BinOp.div (Val.vint 10) (Val.vint 2)) ⊥ (CTy.F 1 VTy.int) :=
  HasCTy.binop HasVTy.vint HasVTy.vint rfl

/-- F2.4 — the `eq` comparison types at `F 1 Bool`. -/
example : HasCTy (Eff := EffRow) (Mult := QTT) []  []
    (Comp.binop BinOp.eq (Val.vint 7) (Val.vint 7)) ⊥ (CTy.F 1 (VTy.sum VTy.unit VTy.unit)) :=
  HasCTy.binop HasVTy.vint HasVTy.vint rfl

/-- F2.5 — a binop over a BOUND variable: `n + 100 : F 1 int` under `Γ = [int]` (`n = vvar 0`).
The operand grade is the basis vector `[1]`; the closed literal is `[0]`; their sum is `[1]`. -/
example : HasCTy (Eff := EffRow) (Mult := QTT) [1] [VTy.int]
    (Comp.binop BinOp.add (Val.vvar 0) (Val.vint 100)) ⊥ (CTy.F 1 VTy.int) :=
  HasCTy.binop (HasVTy.vvar rfl) HasVTy.vint rfl

/-- F2.6 — THE G1 BODY SHAPE (`docs/notes/ctr-design.md` §2.1, `CtrF1DependsF2`'s formerly-untypeable
goal): the compute-then-return clause body `letC (binop add (vvar 0) (vint 100)) (ret (vvar 0))`
types at `F 1 int` under `Γ = [int]`. This is the exact derivation `g1_body_untypeable_today`
REFUTED before the rule landed — now CONSTRUCTED. It is pillar A cleared for G1. -/
example : ∃ (γ : GradeVec QTT) (q : QTT),
    HasCTy (Eff := EffRow) (Mult := QTT) γ [VTy.int]
      (Comp.letC
        (Comp.binop BinOp.add (Val.vvar 0) (Val.vint 100))
        (Comp.ret (Val.vvar 0)))
      (⊥ ⊔ ⊥) (CTy.F q VTy.int) :=
  ⟨_, _,
    HasCTy.letC (q2 := 1)
      (HasCTy.binop (HasVTy.vvar rfl) HasVTy.vint rfl)
      (HasCTy.ret (HasVTy.vvar rfl) rfl)
      rfl⟩

end Bang.BinopTyping
