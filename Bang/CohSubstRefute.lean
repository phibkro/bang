import Bang.Model

/-! REGRESSION WITNESS — why `lwscg_subst` must take `(hvl : ∀ γ' b', LWSVg K γ' b' v)`,
NOT the single-grade `LWSVg K γ_v true v`. `lwscg_subst_refuted` is an AXIOM-CLEAN
(`[propext, Quot.sound]`, no sorryAx) proof that the SINGLE-GRADE shape is FALSE — it takes
that exact type as a hypothesis `H` and derives `False`, so it stands independent of the live
lemma's in-progress proof.

The counterexample: `w = vthunk (ret (vcap n ℓ))` is closed and LWSVg-live at grade `[0]`
(inner cap dormant ⇒ `ret` budget `q=0` ⇒ zeros-headed), yet a well-scoped `c = ret (vvar 0)`
can carry an OFF-DIAGONAL `vvar` grade `[1,1]` (nonzero away from the var it references — because
`LWSVg.vvar`'s grade is only liveness-constrained, unlike `HasVTy.vvar`'s canonical basis). Under
subst that junk must be absorbed by `w`, but `w` is structurally pinned to a zero head ⇒ the forced
conclusion grade `[1]` is unrealizable. The `∀ γ' b'` reshape excludes exactly this: `w` does not
satisfy it (at `(γ'=[1], b'=true)` the cap would have to resolve under `[]`, refuted by
`not_resolves_nil`). DO NOT revert the hypothesis to the single-grade form. (ADR-0060; task #44/#46.) -/

namespace Bang.Model

open Bang.EffectRow (Label)

variable {Mult : Type} [CommSemiring Mult] [DecidableEq Mult]
  [NoZeroDivisors Mult] [Nontrivial Mult]

/-- `head?` of a scaled grade. -/
theorem head?_smul (q : Mult) (δ : GradeVec Mult) :
    (q • δ).head? = δ.head?.map (q * ·) := by
  cases δ <;> simp [GradeVec.smul]

/-- No capability resolves under the empty stack. -/
theorem not_resolves_nil (n : Nat) (ℓ : Label) :
    ¬ ResolvesLabel ([] : EvalCtx) n ℓ := by
  rintro ⟨Kᵢ, h, Kₒ, hsplit, _⟩
  simp [splitAtId] at hsplit

/-- the closed live value: a thunk wrapping a dormant cap. -/
abbrev wbad (n : Nat) (ℓ : Label) : Val := Val.vthunk (Comp.ret (Val.vcap n ℓ))

/-- FACT 1 (sorry-free): `wbad` is LWSVg-live at grade `[0]`. -/
theorem fact1 (n : Nat) (ℓ : Label) :
    LWSVg (Mult := Mult) [] [(0 : Mult)] true (wbad n ℓ) := by
  refine LWSVg.vthunk (LWSCg.ret (q := 0) (γ' := [(0 : Mult)]) ?_ ?_)
  · simp [GradeVec.smul]
  · have hf : (true && decide ((0 : Mult) ≠ 0)) = false := by simp
    rw [hf]; exact LWSVg.vcap_dormant

/-- FACT 2 (sorry-free): `ret (vvar 0)` is LWSCg-live at grade `[1,1]`. -/
theorem fact2 :
    LWSCg (Mult := Mult) [] [(1 : Mult), (1 : Mult)] true (Comp.ret (Val.vvar 0)) := by
  refine LWSCg.ret (q := 1) (γ' := [(1 : Mult), (1 : Mult)]) ?_ ?_
  · simp [GradeVec.smul]
  · refine LWSVg.vvar (fun _ => ?_)
    simpa using (one_ne_zero : (1 : Mult) ≠ 0)

/-- `wbad` is closed. -/
theorem wbad_closed (n : Nat) (ℓ : Label) :
    ∀ j, Val.shiftFrom j (wbad n ℓ) = wbad n ℓ := by
  intro j; rfl

-- inversion helpers: generalize the flag to a variable so dependent elimination
-- on `LWSVg`/`LWSCg` succeeds (a stuck `decide`-flag index breaks bare `cases`).

/-- A `vcap`-value live at flag `true` must resolve its label. -/
theorem lwsvg_vcap_live_resolves {K : EvalCtx} {γf : GradeVec Mult} {f : Bool}
    {n : Nat} {ℓ : Label} (hv : LWSVg K γf f (Val.vcap n ℓ)) (hf : f = true) :
    ResolvesLabel K n ℓ := by
  cases hv with
  | vcap_live hr => exact hr
  | vcap_dormant => exact absurd hf (by simp)

theorem lwsvg_vthunk_inv {K : EvalCtx} {γf : GradeVec Mult} {f : Bool} {c : Comp}
    (hv : LWSVg K γf f (Val.vthunk c)) : LWSCg K γf f c := by
  cases hv with | vthunk hc => exact hc

theorem lwscg_ret_inv {K : EvalCtx} {γf : GradeVec Mult} {f : Bool} {v : Val}
    (h : LWSCg K γf f (Comp.ret v)) :
    ∃ (γ' : GradeVec Mult) (q : Mult), γf = q • γ' ∧ LWSVg K γ' (f && decide (q ≠ 0)) v := by
  cases h with | ret hγ hv => exact ⟨_, _, hγ, hv⟩

/-- FACT 3 (sorry-free): `ret wbad` is NOT LWSCg at grade `[1]`. -/
theorem fact3 (n : Nat) (ℓ : Label) :
    ¬ LWSCg (Mult := Mult) [] [(1 : Mult)] true (Comp.ret (wbad n ℓ)) := by
  intro h
  obtain ⟨γ', q, hγ, hv⟩ := lwscg_ret_inv h
  -- [1] = q • γ' ; via head? get 1 = q * a with γ'.head? = some a
  have hd : ([(1 : Mult)] : GradeVec Mult).head? = (q • γ').head? := by rw [hγ]
  rw [head?_smul] at hd
  obtain ⟨a, ha, hqa⟩ : ∃ a, γ'.head? = some a ∧ (1 : Mult) = q * a := by
    cases hc : γ'.head? with
    | none => rw [hc] at hd; simp at hd
    | some a => rw [hc] at hd; simp at hd; exact ⟨a, rfl, hd⟩
  have hq : q ≠ 0 := by rintro rfl; rw [zero_mul] at hqa; exact one_ne_zero hqa
  have ha0 : a ≠ 0 := by rintro rfl; rw [mul_zero] at hqa; exact one_ne_zero hqa
  -- descend through the thunk and the inner ret
  have hc := lwsvg_vthunk_inv hv
  obtain ⟨γ2', q2, hγ2, hv2⟩ := lwscg_ret_inv hc
  -- γ' = q2 • γ2' ; head? gives a = q2 * b, a ≠ 0 ⇒ q2 ≠ 0
  have hd2 : γ'.head? = (q2 • γ2').head? := by rw [hγ2]
  rw [head?_smul, ha] at hd2
  have hq2 : q2 ≠ 0 := by
    cases hc2 : γ2'.head? with
    | none => rw [hc2] at hd2; simp at hd2
    | some b2 =>
      rw [hc2] at hd2; simp at hd2
      rintro rfl; rw [zero_mul] at hd2; exact ha0 hd2
  -- flag is true ⇒ cap must be live ⇒ ResolvesLabel [] ⇒ contradiction
  have e1 : decide (q ≠ 0) = true := decide_eq_true_eq.mpr hq
  have e2 : decide (q2 ≠ 0) = true := decide_eq_true_eq.mpr hq2
  have hbig : ((true && decide (q ≠ 0)) && decide (q2 ≠ 0)) = true := by rw [e1, e2]; rfl
  exact not_resolves_nil n ℓ (lwsvg_vcap_live_resolves hv2 hbig)

/-- THE REFUTATION: the `lwscg_subst` statement (taken as a hypothesis, so this is
independent of the in-file `sorry`) is inconsistent. -/
theorem lwscg_subst_refuted
    (H : ∀ {K : EvalCtx} {ρ : Mult} {γ γ_v : GradeVec Mult} {b : Bool} {v : Val} {c : Comp},
      LWSVg K γ_v true v → (∀ j, Val.shiftFrom j v = v) → LWSCg K (ρ :: γ) b c →
      LWSCg K (γ + ρ • γ_v) b (Comp.subst v c))
    (n : Nat) (ℓ : Label) : False := by
  have hout := H (ρ := (1 : Mult)) (γ := [(1 : Mult)]) (γ_v := [(0 : Mult)])
    (fact1 n ℓ) (wbad_closed n ℓ) (fact2)
  have hsubst : Comp.subst (wbad n ℓ) (Comp.ret (Val.vvar 0)) = Comp.ret (wbad n ℓ) := rfl
  have hgrade : ([(1 : Mult)] + (1 : Mult) • [(0 : Mult)]) = ([(1 : Mult)] : GradeVec Mult) := by
    simp [GradeVec.smul, GradeVec.add]
  rw [hsubst, hgrade] at hout
  exact fact3 n ℓ hout
