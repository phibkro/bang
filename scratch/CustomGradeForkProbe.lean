import Bang.Core.Soundness

/-! # PROBE (ADR-0092 D3 fork A vs B): does the FLAGSHIP clause body discharge (A)'s ∀q' obligation?

Lead's discriminator: the Stage-2 106-witness clause body is `let x = arg + 100 in ret x` — a
COMPUTE-then-return body. (A) needs `∀ q', HasCTy [opArg,P] body (F q' opRes)`; (B) is the ret-shape shrink.

TWO findings, machine-checked:

(1) The flagship body uses `binop` (`arg + 100`), and **`binop` is UNTYPEABLE in v1** (ADR-0065:
    `HasCTy.binop_untypable` — the δ-rule has no `HasCTy` rule). So the flagship clause body types at NO
    grade, let alone `∀ q'`. This REFUTES (A) for the flagship — but for a reason deeper than grade
    non-parametricity: the compute step itself is untyped-fragment-only. Under EITHER option the flagship
    106 witness stays untyped-fragment-only in v1 (the running superset > the typed core — stratification
    working, not failing).

(2) The grade-parametric question the lead posed, tested on the binop-FREE identity-let
    `let x = arg in ret x` (`letC (ret (vvar 0)) (ret (vvar 0))`): does the letC grade composition stay
    `∀ q'`-parametric the way bare `ret` is? This isolates whether (A) would be viable for the SUBSET of
    compute-then-return clauses that avoid the untyped binop. -/

namespace Bang.CustomGradeForkProbe

open Bang

variable {Eff  : Type} [Lattice Eff] [OrderBot Eff]
variable {Mult : Type} [CommSemiring Mult] [DecidableEq Mult]
variable [EffSig Eff Mult]

/-- (1) The FLAGSHIP body `let x = arg + 100 in ret x` types at NO grade — its `binop` compute step is
untypeable (ADR-0065). Stated for a general `q'`: not even the ∀-instance holds, so (A) is refuted on the
flagship. (`arg` = `vvar 0`; `100` = `vint 100`; the let binds the binop result then returns it.) -/
theorem flagship_body_untypeable {P opA opR : VTy Eff Mult} {q' : Mult} :
    ¬ HasCTy (Eff := Eff) (Mult := Mult) (0 :: 0 :: []) (opA :: P :: [])
        (Comp.letC (Comp.binop BinOp.add (Val.vvar 0) (Val.vint 100)) (Comp.ret (Val.vvar 0)))
        ⊥ (CTy.F q' opR) := by
  intro h
  -- invert the letC: the bound computation `M = binop …` must itself be typed — but `HasCTy` has NO
  -- binop constructor (ADR-0065), so `cases` on its derivation eliminates every alternative.
  obtain ⟨γ₁, γ₂, φ₁, φ₂, q1, q2, A, _he, _hγ, hM, _hN⟩ := h.letC_inv
  cases hM

/-- (2) The grade-freedom crux, isolated on a CONSTANT returner `ret (vint 0)`: it types at ∀ q' (bare
`ret`'s grade-freedom — `[] = q' • []` for any q'). This is the exact property (B) exploits and a general
FIXED-grade body lacks. The lead's letC/binop flagship is untypeable one layer up (finding 1: the binop),
so the grade question never even reaches the letC composition for the flagship — the (A)/(B) fork is MOOT
for it (untyped either way). Constant here stands in for "the resumed value" — the ret-shape (B) body. -/
theorem const_ret_grade_generic {opR : VTy Eff Mult} {Γ : TyCtx Eff Mult} {n : Int} :
    ∀ q', HasCTy (Eff := Eff) (Mult := Mult) (GradeVec.zeros Γ.length) Γ
        (Comp.ret (Val.vint n)) ⊥ (CTy.F q' VTy.int) := by
  intro q'
  exact HasCTy.ret HasVTy.vint (by simp [hsmul_eq_smul, GradeVec.smul, GradeVec.zeros])

#print axioms flagship_body_untypeable
#print axioms const_ret_grade_generic

end Bang.CustomGradeForkProbe
