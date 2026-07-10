import Bang.Core.Soundness

/-! # PROBE (task #34, lane ctr): F1 (the ⊥-row grade-freedom) is DOWNSTREAM of F2 (ADR-0065 binop typing).

The design note §4.2 orders slice 1 = F1 (grade-freedom probe), slice 2 = ADR-0065 stage ④.
This probe machine-checks that the order is FORCED the other way for the actual G1 body shape:
a `letC (binop …) (ret …)` body CANNOT be typed today, because `letC`'s bound-computation premise
(`HasCTy γ₁ Γ M φ₁ (F q1 A)`, Typing.lean:148) requires the `binop` sub-term to type — and it does
not (`HasCTy.binop_untypable`). So the F1 grade derivation is UNSTATEABLE until F2 lands.

⟹ SLICE-ORDER CORRECTION: ADR-0065 stage ④ (F2) must precede the F1 grade probe. The design note's
"slice 1 = F1" is only reachable as a PAPER argument (§2.3); the MACHINE-checkable F1 waits on F2.
This is the sharpest slice-order finding — recorded so the grind lane doesn't attempt F1 first and
stall on an unstateable goal. -/

namespace Bang.CtrF1DependsF2

open Bang

variable {Eff  : Type} [Lattice Eff] [OrderBot Eff]
variable {Mult : Type} [CommSemiring Mult] [DecidableEq Mult]
variable [EffSig Eff Mult]

/-- The G1-shaped ⊥-row computing body `letC (binop add arg 100) (ret (vvar 0))` types at NO grade
TODAY, because inverting the `letC` exposes the bound `binop`, which `binop_untypable` refutes. This is
pillar A blocking F1's very STATEMENT — not a grade problem, a "the sub-term is untyped" problem. -/
theorem g1_body_untypeable_today {P opR : VTy Eff Mult} {q : Mult} {φ : Eff} :
    ¬ HasCTy (Eff := Eff) (Mult := Mult) (0 :: 0 :: []) (opR :: P :: [])
        (Comp.letC (Comp.binop BinOp.add (Val.vvar 0) (Val.vint 100)) (Comp.ret (Val.vvar 0)))
        φ (CTy.F q opR) := by
  intro h
  -- invert the letC: the bound M = binop … must type, but HasCTy has NO binop rule (ADR-0065 ④ unlanded).
  -- (`binop_untypable` is private in Soundness; inline its one-liner — `cases` eliminates every ctor.)
  obtain ⟨γ₁, γ₂, φ₁, φ₂, q1, q2, A, _he, _hγ, hM, _hN⟩ := h.letC_inv
  cases hM

#print axioms g1_body_untypeable_today

end Bang.CtrF1DependsF2
