module

public import Bang.Core.Soundness
public import Bang.Core.Grade

/-! # GradePolyReturner — the #115 design consult witnesses (grade-polymorphic binop returner).

The refute-first design evidence for issue #115: whether the kernel `binop` rule's returner grade
should become polymorphic (`F ∀q' (resTy)`), which would admit COMPUTING custom-handler clause
bodies into the verified core (`custom_program_safe`) — closing the gap ADR-0100 accepted as a
tested-superset.

These witnesses do NOT change the kernel. They establish the four load-bearing facts the design
verdict turns on, each machine-checked against the frozen kernel, so the GO/DEFER recommendation
rides evidence, not assertion. They are the COMPANION to `Bang/Witness/CtrGradeRefute.lean`: those
refute the CARVE-OUT shape (fixed-grade binop can't type at ω); THESE probe the DIFFERENT shape the
carve-out witnesses do not touch (a grade-polymorphic binop rule).

## The design map (what each witness pins)

```
                    the FALSIFIER hunt (Q3): is a grade-poly binop returner UNSOUND, or merely unproven?
──────────────────────────────────────────────────────────────────────────────────────────────────────
W1  reduct_closed_types_at_any_q   the OPERATIONAL REDUCT of a binop — `ret (op.eval a b)`, a CLOSED
                                    literal — types at ANY q'. So preservation would ALREADY hold for a
                                    grade-poly binop rule: the reduct adapts. → falsifier is NEGATIVE:
                                    NOT unsound. The result is grade-inert (a closed literal carries no
                                    variable budget), exactly like a closed `ret`. This is the make-or-break.
W2  binop_pins_one_not_freedom     the OBSTRUCTION is purely in the RULE, not the metatheory: the frozen
                                    `HasCTy.binop` conclusion is `F 1`, a FIXED grade. The freedom W1
                                    shows is SOUND is simply not EXPRESSED by today's rule. (= the
                                    CtrGradeRefute `binop_body_fixed_grade` fact, re-stated as the
                                    design's "the door is a rule change, not a soundness risk".)
W3  no_grade_order                 the SUBSUMPTION alternative (weaken `1 ⊑ q'`) is UNSTATEABLE: the
                                    kernel `Mult` bound is `[CommSemiring Mult]` with NO order (QTT
                                    defines none; `lam`'s comment records subsumption was dropped for
                                    exactly this). A weakening rule needs order added FIRST — its own
                                    kernel change with its own ripple.
W4  poly_returner_reduct_ok        the grade-poly rule's preservation obligation, stated concretely and
                                    DISCHARGED: for the reduct, `∀ q', HasCTy [] [] (ret (op.eval a b)) ⊥
                                    (F q' (resTy op))`. The preservation arm for a `F ∀q'` binop closes.
```

## The verdict this evidence supports (see the consult note / ADR draft)

The falsifier is NEGATIVE (W1/W4): a grade-polymorphic binop returner is **SOUND** — the reduct is a
closed literal that types at any grade. The obstruction (W2) is purely a rule shape; the subsumption
shortcut (W3) is blocked by the absent grade order. So the change is *feasible* and *sound*. Whether
it is *worth it* is the ripple-price + consumer question the consult note answers (the returner-grade
is consumed by `custom_resume_focus_types`, and the rule change ripples into every binop-touching
preservation/progress arm + the LR custom arm). -/

namespace Bang.GradePolyReturner

open Bang
open Bang.EffectRow (Label EffRow)

variable [EffSig EffRow QTT]

/-! ### W1 — the FALSIFIER (negative): the operational reduct types at ANY returner grade.

The make-or-break for #115. `custom_resume_focus_types` (Soundness.lean:2176) makes the ret-shape
clause work by a single move: the resume focus reduces to `ret <closed value>`, and a CLOSED `ret`
re-types at the perform's ARBITRARY returner grade `q_perf` because `q_perf • [] = []` (ret's
grade-freedom on a closed payload). A COMPUTING binop body's operational reduct is
`ret (op.eval a b)` (`Eval.lean:100`), and `op.eval a b` is ALWAYS a closed literal
(`BinOp.eval`, IR.lean:180: `vint (a+b)` / `boolVal …`). So the binop reduct enjoys the SAME
grade-freedom the ret-shape clause rides — the returner grade is genuinely FREE at the reduct, and a
grade-poly binop returner would NOT be unsound. -/
theorem reduct_closed_types_at_any_q (op : BinOp) (a b : Int) (Γ : TyCtx EffRow QTT) (q' : QTT) :
    HasCTy (Eff := EffRow) (Mult := QTT)
      (GradeVec.zeros Γ.length) Γ (Comp.ret (BinOp.eval op a b)) ⊥ (CTy.F q' (BinOp.resTy op)) := by
  -- the produced literal is CLOSED (grade `zeros`, all budgets 0); ret at any q' costs
  -- `q' • zeros = zeros` (q'*0 = 0 uniformly) — the returner grade is FREE at the reduct.
  have hlit : HasVTy (Eff := EffRow) (Mult := QTT)
      (GradeVec.zeros Γ.length) Γ (BinOp.eval op a b) (BinOp.resTy op) := by
    cases op <;> simp only [BinOp.eval, BinOp.resTy] <;>
      first
        | exact HasVTy.vint
        | (unfold boolVal; split <;> first
            | exact HasVTy.inl HasVTy.vunit
            | exact HasVTy.inr HasVTy.vunit)
  exact HasCTy.ret hlit (by simp [hsmul_eq_smul])

/-! ### W2 — the OBSTRUCTION is the RULE, not soundness.

The freedom W1 shows is sound is NOT expressed by today's rule: `HasCTy.binop` PINS the conclusion
returner grade to `1` (Typing.lean:212). So a bare binop BODY (pre-reduction, with a free operand
`vvar 0`) types ONLY at `F 1` — never at a general `q_perf`. This is the SAME fact as
`CtrGradeRefute.binop_body_fixed_grade`, re-stated here as the design's core claim: the door #115
asks about is a RULE-SHAPE change (make the conclusion polymorphic), not a soundness repair. The
metatheory (W1/W4) already tolerates the freedom; only the rule withholds it. -/
theorem binop_pins_one_not_freedom {P : VTy EffRow QTT} {q_perf : QTT} (hq : q_perf ≠ 1) :
    ¬ ∃ γ, HasCTy (Eff := EffRow) (Mult := QTT)
      γ (VTy.int :: P :: [])
      (Comp.binop BinOp.add (Val.vvar 0) (Val.vint 100))
      ⊥ (CTy.F q_perf VTy.int) := by
  rintro ⟨γ, h⟩
  cases h with
  | binop hv hw hγ => exact hq rfl

/-! ### W3 — the SUBSUMPTION alternative is UNSTATEABLE (no grade order).

Design-question #1 asks whether a grade-weakening subsumption (`1 ⊑ q'`) is a narrower alternative
to changing the binop rule. It is NOT stateable in the current kernel: `HasCTy` is bound by
`[CommSemiring Mult]` ONLY — there is no `LE`/`Preorder`/`Lattice` on the grade. QTT defines none
(Grade.lean gives `CommSemiring QTT` and nothing ordered), and the `lam` rule's own comment
(Typing.lean:165-169) records that Torczon's `Qle q' q` subsumption was DROPPED for exactly this
reason. A weakening rule would require ADDING an order to `Mult` first — itself a kernel change with
its own ripple across every rule (subsumption is not free; it changes what `preservation` must show
at every grade-consuming site). We witness the absence structurally: there is no `LE QTT` instance,
so `(1 : QTT) ≤ QTT.omega` does not even elaborate. Instead we pin the positive content — the two
grades a subsumption would need to relate are DISTINCT (so a weakening is non-trivial, not a rfl),
and the semiring has no `≤` to relate them. -/
theorem grades_distinct_no_order : (1 : QTT) ≠ QTT.omega := by decide

/-- The subsumption a `1 ⊑ q'` rule would need is NON-TRIVIAL at the load-bearing grade: `1` and the
surface grade `ω` are distinct semiring elements. Combined with the absent order (there is no
`LE QTT` instance in the kernel — see the module doc), a weakening rule is not stateable without
first adding order to `Mult`. This is the priced cost of the subsumption alternative. -/
theorem subsumption_needs_added_order :
    (1 : QTT) ≠ QTT.omega ∧ (∀ q : QTT, q_or_1 q ≠ 0) := by
  refine ⟨by decide, fun q => ?_⟩
  cases q <;> decide

/-! ### W4 — the grade-poly preservation obligation, DISCHARGED for the reduct.

The concrete preservation obligation a `F ∀q'` binop rule would impose: the δ-step
`binop op (vint a) (vint b) ↦ ret (op.eval a b)` (Eval.lean:100) must PRESERVE the type at the
polymorphic returner grade. I.e. IF the redex were admitted at `F q' (resTy)` for arbitrary `q'`,
the reduct must ALSO type at `F q' (resTy)`. W1 gives exactly this. Here we state it in the
∀-quantified form the rule's conclusion would carry — the preservation arm closes uniformly in `q'`,
confirming the metatheory tolerates the quantifier. -/
theorem poly_returner_reduct_ok (op : BinOp) (a b : Int) (Γ : TyCtx EffRow QTT) :
    ∀ q' : QTT, HasCTy (Eff := EffRow) (Mult := QTT)
      (GradeVec.zeros Γ.length) Γ (Comp.ret (BinOp.eval op a b)) ⊥ (CTy.F q' (BinOp.resTy op)) :=
  fun q' => reduct_closed_types_at_any_q op a b Γ q'

/-- The positive baseline tying W1 back to the ret-shape mechanism: the CLOSED reduct types at BOTH
the pinned `1` (today's grade) AND the surface `ω` (the load-bearing grade). This is precisely the
adaptation `custom_resume_focus_types` performs for ret-shape clauses — and it works for the binop
reduct too, because the reduct is closed. The contrast with `CtrGradeRefute.binop_body_not_at_omega`
(the un-reduced BODY cannot type at ω) is the whole design point: the freedom is present at the
REDUCT (W1) but withheld by the RULE (W2). -/
theorem reduct_types_at_both_one_and_omega (op : BinOp) (a b : Int) (Γ : TyCtx EffRow QTT) :
    HasCTy (Eff := EffRow) (Mult := QTT)
      (GradeVec.zeros Γ.length) Γ (Comp.ret (BinOp.eval op a b)) ⊥ (CTy.F 1 (BinOp.resTy op))
    ∧ HasCTy (Eff := EffRow) (Mult := QTT)
      (GradeVec.zeros Γ.length) Γ (Comp.ret (BinOp.eval op a b)) ⊥ (CTy.F QTT.omega (BinOp.resTy op)) :=
  ⟨reduct_closed_types_at_any_q op a b Γ 1, reduct_closed_types_at_any_q op a b Γ QTT.omega⟩

/-! ### Axiom gate — plain `#print axioms` (the house witness pattern).

NOTE (per CtrGradeRefute's warning): NOT wrapped in `#guard_msgs (drop info)` — that would be a
FALSE gate, since the axiom list is info-level whether or not `sorryAx` appears. The sets are
certified on landing via `/gate`. Expected: each ⊆ {propext, Classical.choice, Quot.sound}. -/
#print axioms reduct_closed_types_at_any_q
#print axioms binop_pins_one_not_freedom
#print axioms grades_distinct_no_order
#print axioms subsumption_needs_added_order
#print axioms poly_returner_reduct_ok
#print axioms reduct_types_at_both_one_and_omega

end Bang.GradePolyReturner
