module

public import Bang.Core.Soundness
public import Bang.Core.Grade

/-! # CtrGradeRefute — the F1 refutation for the compute-then-return (G1) exit gate (task #29).

The KEPT do-not-weaken regression witnesses for `docs/notes/ctr-design.md`'s corrected verdict.
The design note originally predicted a "(γ) GO": a ⊥-row `HasClauses` carve-out admitting COMPUTING
clause bodies into the verified core. **F1 refutes that.** A ⊥-row computing body pins a FIXED
returner grade and CANNOT type at the perform's grade in the kernel — so the carve-out is
UNSTATEABLE at the grade a well-typed surface program actually uses.

The grade-layer mismatch (machine-checked here):

```
                      SURFACE (ω-liberal)          KERNEL (grade-precise)
──────────────────────────────────────────────────────────────────────────────────────
binop returner grade  .F .omega  (TypeCheck:1047)  F 1  (Typing:212, PINNED)
perform returner      .F .omega  (TypeCheck:1201)  F q  (universally free, incl ω)
verdict on a          ACCEPTS + RUNS               CANNOT type at q_perf = ω  (1 ≠ ω)
  computing body       (tested superset)            (verified core stays ret-shape)
```

Consequence: G1's compute-then-return bodies ship as a TESTED-SUPERSET feature (surface-accepted +
differential-tested vs `Source.eval`), NOT covered by `custom_program_safe` — the intended
stratification seam. The `HasClauses` ret-shape STAYS. If any future change makes these refutations
FAIL to compile, the kernel/surface grade contract has shifted and the ctr-design verdict must be
re-derived. -/

namespace Bang.CtrGradeRefute

open Bang
open Bang.EffectRow (Label EffRow)

variable [EffSig EffRow QTT]

/-! ### F1 — the grade-freedom refutation (kernel typing) -/

omit [EffSig EffRow QTT] in
/-- `q_or_1` is never `0` on QTT (the let-coeffect floor). -/
theorem q_or_1_ne_zero (q : QTT) : (1 : QTT) * q_or_1 q ≠ 0 := by
  rw [one_mul]; cases q <;> decide

omit [EffSig EffRow QTT] in
/-- ω ≠ 1 on QTT (the surface's perform grade is NOT the kernel tail grade). -/
theorem omega_ne_one : (QTT.omega : QTT) ≠ 1 := by decide

/-- **F1 REFUTED (bare binop).** A bare `binop` body types ONLY at `F 1 int` — its returner grade
is PINNED to `1` by `HasCTy.binop` (`Typing.lean:212`). For a perform at `q_perf ≠ 1` there is NO
typing derivation. Even the simplest computing body `n + 100` cannot serve as a resume focus at a
general perform grade. The fixed-returner-grade obstruction (pillar B), machine-checked. -/
theorem binop_body_fixed_grade {P : VTy EffRow QTT} {q_perf : QTT} (hq : q_perf ≠ 1) :
    ¬ ∃ γ, HasCTy (Eff := EffRow) (Mult := QTT)
      γ (VTy.int :: P :: [])
      (Comp.binop BinOp.add (Val.vvar 0) (Val.vint 100))
      ⊥ (CTy.F q_perf VTy.int) := by
  rintro ⟨γ, h⟩
  cases h with
  | binop hv hw hγ => exact hq rfl

/-- **The fallback fails at THE surface grade ω.** The surface types every `binopS` and `perform` at
`.F .omega` (`TypeCheck.lean:1047, 1201`). So the kernel resume focus would need to type at
`q_perf = ω`. But the binop returner is pinned to `1`, and `1 ≠ ω`. The §2.5 `∀q'` fallback does
NOT collapse to the ret-shape — it is simply FALSE at the load-bearing grade. -/
theorem binop_body_not_at_omega {P : VTy EffRow QTT} :
    ¬ ∃ γ, HasCTy (Eff := EffRow) (Mult := QTT)
      γ (VTy.int :: P :: [])
      (Comp.binop BinOp.add (Val.vvar 0) (Val.vint 100))
      ⊥ (CTy.F QTT.omega VTy.int) := by
  rintro ⟨γ, h⟩
  -- `cases` sees `F ω int = F 1 (resTy add)` is structurally impossible (ω ≠ 1), closing every arm.
  cases h

/-- **F1 REFUTED (letC-wrapped, at q_perf = 0).** The G1-shaped body `letC (binop …) (ret (vvar 0))`
returning the LET-BOUND result cannot type at `F 0 int`: the `letC` `q_or_1` floor forces the bound
variable's usage grade to `q_or_1 0 = 1`, but `ret`ing it at returner grade `0` demands usage grade
`0 • basis = 0`. `1 ≠ 0`. The floored bound-var breaks grade-freedom at the abort grade. -/
theorem letc_body_not_at_zero {P : VTy EffRow QTT} :
    ¬ ∃ γ, HasCTy (Eff := EffRow) (Mult := QTT)
      γ (VTy.int :: P :: [])
      (Comp.letC (Comp.binop BinOp.add (Val.vvar 0) (Val.vint 100)) (Comp.ret (Val.vvar 0)))
      ⊥ (CTy.F 0 VTy.int) := by
  rintro ⟨γ, h⟩
  obtain ⟨γ₁, γ₂, φ₁, φ₂, q1, q2, A, _he, hγ, hM, hN⟩ := h.letC_inv
  have hq1 : q1 = 1 := by
    generalize hEφ : φ₁ = E at hM
    cases hM with
    | binop _ _ _ => rfl
  subst hq1
  obtain ⟨γ', A0, q0, _heffN, hCeqN, hγN, hvalN⟩ := hN.ret_inv
  obtain ⟨hq0, _hA0⟩ := CTy.F.injEq .. ▸ hCeqN
  subst hq0
  have hhead : (1 : QTT) * q_or_1 q2 = 0 := by
    cases γ' with
    | nil => simp [hsmul_eq_smul, GradeVec.smul] at hγN
    | cons c rest =>
      simp only [hsmul_eq_smul, GradeVec.smul_cons, List.cons.injEq] at hγN
      exact hγN.1
  exact q_or_1_ne_zero q2 hhead

/-- POSITIVE baseline: the SAME letC body DOES type at `F 1 int` (the tail/one-shot grade). So the
obstruction is grade-SPECIFIC (q ≠ 1), confirming the body is well-formed and the wall is purely
about grade adaptation. This is why the tracer `n * 10` RUNS — the RUN never needs a kernel
derivation, and the tested superset admits at ω what the kernel types at 1. -/
theorem letc_body_types_at_one {P : VTy EffRow QTT} :
    ∃ γ, HasCTy (Eff := EffRow) (Mult := QTT)
      γ (VTy.int :: P :: [])
      (Comp.letC (Comp.binop BinOp.add (Val.vvar 0) (Val.vint 100)) (Comp.ret (Val.vvar 0)))
      ⊥ (CTy.F 1 VTy.int) := by
  refine ⟨_, HasCTy.letC (Eff := EffRow) (Mult := QTT) (q1 := 1) (q2 := 1) (A := VTy.int)
    (γ₂ := 0 :: 0 :: [])
    (HasCTy.binop (op := BinOp.add) (v := Val.vvar 0) (w := Val.vint 100)
      (HasVTy.vvar rfl) HasVTy.vint rfl)
    (HasCTy.ret (v := Val.vvar 0)
      (HasVTy.vvar (Γ := VTy.int :: VTy.int :: P :: []) (i := 0) rfl) ?_) rfl⟩
  show ((1 : QTT) * q_or_1 1) :: (0 : QTT) :: 0 :: [] = (1 : QTT) • GradeVec.basis 3 0
  decide

/-! ### The RUN witness — the tested-superset side.

The compute-then-return clause bodies the kernel CANNOT type (F1 above) DO run correctly under the
kernel oracle `Source.eval` — the differential evidence that G1 ships as a tested-superset feature.
Those `#guard`s parse + lower + eval, which needs the interpreter-compiled frontend; they live in
`scratch/CtrTracerRuns.lean` (checked via `lake env lean`, like `CtrWallRecheck.lean`), NOT in this
glob-built library (where `parseProg` has no native impl). See that file + `docs/notes/ctr-design.md`
§"⚠ F1 REFUTATION" for the run evidence: `n*10 ⇒ 30`, `let m=n*2 in m+1 ⇒ 11`. -/

-- Axiom gate: the refutations depend on nothing outside the trusted-3. A green build with these
-- present IS the axiom-cleanliness proof (they error if any theorem picks up `sorryAx`).
#guard_msgs (drop info) in #print axioms binop_body_fixed_grade
#guard_msgs (drop info) in #print axioms binop_body_not_at_omega
#guard_msgs (drop info) in #print axioms letc_body_not_at_zero
#guard_msgs (drop info) in #print axioms letc_body_types_at_one

end Bang.CtrGradeRefute
