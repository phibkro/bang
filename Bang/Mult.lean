/-
  Bang/Mult.lean — QTT multiplicity grade.
  ─────────────────────────────────────────
  The concrete `Bang.QTT` instance of the `Mult` parameter used in
  Bang/Spec.lean (and downstream). QTT = {zero, one, omega} is the
  standard quantitative-type-theory rig (Atkey 2018, McBride 2016).

  All Semiring laws hold by case analysis (3 enum elements → 27
  combinations for 3-arg laws; each closes by `rfl` after `cases`).

  Bang/Core.lean keeps the spec parametric in `[Semiring Mult]`; QTT
  is ONE valid instance — the bang-lang default. Phase B proofs may
  specialize to QTT or stay parametric.

  See ROADMAP.md / docs/notes/spec-handover.md for the multiplicity-
  grade design rationale; ADR-0018 for the row-algebra context.
-/

import Mathlib.Algebra.Order.Ring.Defs

namespace Bang

inductive QTT : Type where
  | zero | one | omega
  deriving DecidableEq, Repr, Inhabited

namespace QTT

/-- Addition table:
      0+0 = 0,  0+1 = 1,  0+ω = ω
      1+0 = 1,  1+1 = ω,  1+ω = ω
      ω+0 = ω,  ω+1 = ω,  ω+ω = ω
-/
def add : QTT → QTT → QTT
  | .zero, m       => m
  | m, .zero       => m
  | .one, .one     => .omega
  | _, _           => .omega

/-- Multiplication table:
      0 * x = 0,   x * 0 = 0
      1 * x = x,   x * 1 = x
      ω * ω = ω
-/
def mul : QTT → QTT → QTT
  | .zero, _       => .zero
  | _, .zero       => .zero
  | .one, m        => m
  | m, .one        => m
  | .omega, .omega => .omega

end QTT

instance : Add QTT := ⟨QTT.add⟩
instance : Mul QTT := ⟨QTT.mul⟩
instance : Zero QTT := ⟨.zero⟩
instance : One QTT := ⟨.one⟩

/-- QTT forms a commutative semiring. All laws by case analysis on the
3-element enum. -/
instance : CommSemiring QTT where
  add_assoc      := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  zero_add       := by intro a;     cases a <;> rfl
  add_zero       := by intro a;     cases a <;> rfl
  add_comm       := by intro a b;   cases a <;> cases b <;> rfl
  nsmul          := nsmulRec
  mul_assoc      := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  one_mul        := by intro a;     cases a <;> rfl
  mul_one        := by intro a;     cases a <;> rfl
  left_distrib   := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  right_distrib  := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  zero_mul       := by intro a;     cases a <;> rfl
  mul_zero       := by intro a;     cases a <;> rfl
  mul_comm       := by intro a b;   cases a <;> cases b <;> rfl

end Bang
