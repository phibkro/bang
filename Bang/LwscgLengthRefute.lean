import Bang.Model

/-! REGRESSION WITNESS — keep; do NOT remove the `(hlen_v : γ_v.length = γ.length)`
hypothesis from `lwscg_subst`. Machine-checked proof that WITHOUT a length constraint
relating the substituted value's grade `γ_v` to the body context `γ`, the
`lwscg_subst` statement is FALSE. Sorry-free, axiom-clean (`[propext, Quot.sound]`).
Task #44; ADR-0060. Second don't-weaken guard, on a DIFFERENT axis from
`Bang/CohSubstRefute.lean` (that guards the `∀ γ' b'` reshape of `hvl`; this guards
the length hypothesis).

THE BUG: `GradeVec.add = List.zipWith (·+·)` (Core.lean) TRUNCATES to the shorter
length. When `γ_v` is SHORTER than `γ`, the result grade `γ + ρ • γ_v` silently drops
a LIVE body-variable's grade slot. Most formers (`ret`/`app`/`case`/…) carry an
existential `q`-gate that can collapse to `q = 0` and absorb this, but `force` passes
its flag straight to the value with NO gate — so the dropped-slot becomes a genuinely
uninhabited obligation.

THE COUNTEREXAMPLE (`v = vunit`, so it is PURELY about length, not cap-resolution):
  K=[], ρ=1, γ=[1], γ_v=[], b=true, c = force (vvar 1).
  hc : LWSCg [] [1,1] true (force (vvar 1))        -- var 1 live, grade [1,1][1]=1≠0
  ⊢  : LWSCg [] ([1]+1•[]) true (force (vvar 0))    -- [1]+1•[] = [] (truncated!)
The conclusion forces `LWSVg [] [] true (vvar 0)`, whose gate is `[][0]?.getD 0 ≠ 0` =
`0 ≠ 0` — uninhabited. THE FIX (live in `lwscg_subst`): `hlen_v : γ_v.length = γ.length`
restores the pin the typed template carries for free (subst_value_proof: `HasVTy γ_v Γ`
pins `γ_v.length = Γ.length`, `HasCTy (ρ::γ) (A::Γ)` pins `γ.length = Γ.length`). With
it, `γ_v=[] ⇒ γ=[] ⇒ force (vvar 1)` is ungradeable at `[ρ]`, excluding this case. -/

namespace Bang.Model

variable {Mult : Type} [CommSemiring Mult] [DecidableEq Mult]
  [NoZeroDivisors Mult] [Nontrivial Mult]

/-- The bad source derivation: `force (vvar 1)` is live at grade `[1,1]`. -/
theorem hc_force : LWSCg (Mult := Mult) [] [(1:Mult),(1:Mult)] true (Comp.force (Val.vvar 1)) :=
  LWSCg.force (LWSVg.vvar (fun _ => by simp))

/-- The conclusion grade collapses to `[]` (the truncating `zipWith`). -/
theorem bad_grade : ([(1:Mult)] + (1:Mult) • ([] : GradeVec Mult)) = ([] : GradeVec Mult) := by
  simp [GradeVec.smul, GradeVec.add]

/-- The substituted body: `subst vunit (force (vvar 1)) = force (vvar 0)`. -/
theorem bad_subst : Comp.subst Val.vunit (Comp.force (Val.vvar 1)) = Comp.force (Val.vvar 0) := rfl

/-- The conclusion is UNINHABITED: `force (vvar 0)` at grade `[]`, flag `true`. -/
theorem concl_uninhabited :
    ¬ LWSCg (Mult := Mult) [] ([] : GradeVec Mult) true (Comp.force (Val.vvar 0)) := by
  intro h
  cases h with
  | force hv =>
    cases hv with
    | vvar hgate => exact absurd (hgate rfl) (by simp)

/-- THE REFUTATION: the `lwscg_subst` statement WITHOUT the length hypothesis (with the
∀-form `hvl` and `hcl`, taken as `H` so this is independent of the live lemma's `sorry`)
is inconsistent. -/
theorem lwscg_subst_length_refuted
    (H : ∀ {K : EvalCtx} {ρ : Mult} {γ γ_v : GradeVec Mult} {b : Bool} {v : Val} {c : Comp},
      (∀ (γ' : GradeVec Mult) (b' : Bool), LWSVg K γ' b' v) →
      (∀ j, Val.shiftFrom j v = v) →
      LWSCg K (ρ :: γ) b c →
      LWSCg K (γ + ρ • γ_v) b (Comp.subst v c)) : False := by
  have hout := H (K := []) (ρ := (1:Mult)) (γ := [(1:Mult)]) (γ_v := ([] : GradeVec Mult))
    (b := true) (v := Val.vunit) (c := Comp.force (Val.vvar 1))
    (fun _ _ => LWSVg.vunit) (fun _ => rfl) hc_force
  rw [bad_subst, bad_grade] at hout
  exact concl_uninhabited hout

end Bang.Model
