module

public import Bang.Model

/-! REGRESSION WITNESS — keep; do NOT revert `lwscg_subst` to the single-grade hypothesis.
Regression rationale + machine-checked consumability verification for the RESHAPE of
`lwscg_subst` (hyp `∀ γ' b', LWSVg K γ' b' v`). All theorems sorry-free, axiom-clean
(`[propext, Quot.sound]`). Task #44/#46; ADR-0060.

PART A (regression): the OLD statement (`LWSVg K γ_v true v`) was UNSOUND — `wbad =
vthunk (ret (vcap n ℓ))` is gradeable only head-0 (its inner cap is dormant under a
non-resolving K ⇒ ret budget 0), yet pairs with a ρ=1 context to force an impossible
result grade. `lwscg_subst_refuted` derives `False` from the old type (axiom-clean).

PART B (the reshape excludes it): `wbad_not_reshaped` — `wbad` FAILS the ∀-form, so
the reshape precisely drops the unsound case.

PART C (consumability): under a RESOLVING K, the SAME shape satisfies the ∀-form
(`vgood_anyGrade`). The discriminating condition is cap-resolution; closed values have
no free `vvar` (the only grade-sensitive constructor), so well-scoping is grade-free,
gated only by cap-resolution (which is itself grade-insensitive — `vcap_live`'s grade
is unconstrained). Hence no LIVE counterexample to the reshape exists. -/

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

/-! ## PART B — the reshape EXCLUDES the unsound case. -/

/-- `wbad` FAILS the reshaped hypothesis: at `γ'=[1], b'=true` its cap would have to be
live under `[]`, which `not_resolves_nil` forbids. So the reshape drops exactly the
case Part A refutes. -/
theorem wbad_not_reshaped (n : Nat) (ℓ : Label) :
    ¬ (∀ (γ' : GradeVec Mult) (b' : Bool), LWSVg [] γ' b' (wbad n ℓ)) := by
  intro hall
  have hv := hall [(1 : Mult)] true
  have hc := lwsvg_vthunk_inv hv
  obtain ⟨γ', q, hγ, hcap⟩ := lwscg_ret_inv hc
  have hd : ([(1 : Mult)] : GradeVec Mult).head? = (q • γ').head? := by rw [hγ]
  rw [head?_smul] at hd
  obtain ⟨a, ha, hqa⟩ : ∃ a, γ'.head? = some a ∧ (1 : Mult) = q * a := by
    cases hcc : γ'.head? with
    | none => rw [hcc] at hd; simp at hd
    | some a => rw [hcc] at hd; simp at hd; exact ⟨a, rfl, hd⟩
  have hq : q ≠ 0 := by rintro rfl; rw [zero_mul] at hqa; exact one_ne_zero hqa
  have e1 : decide (q ≠ 0) = true := decide_eq_true_eq.mpr hq
  have hbig : (true && decide (q ≠ 0)) = true := by rw [e1]; rfl
  exact not_resolves_nil n ℓ (lwsvg_vcap_live_resolves hcap hbig)

/-! ## PART C — under a RESOLVING K, the same shape IS consumable (∀-form holds). -/

/-- a stack that installs handler `n : ℓ`, so `(n, ℓ)` resolves. -/
abbrev Kres (n : Nat) (ℓ : Label) : EvalCtx := [Frame.handleF n (Handler.throws ℓ)]

theorem resolves_Kres (n : Nat) (ℓ : Label) : ResolvesLabel (Kres n ℓ) n ℓ := by
  refine ⟨[], Handler.throws ℓ, [], ?_, rfl⟩
  simp [splitAtId, Kres]

/-- CONSUMABILITY (sorry-free): the thunk-wrapped cap — the exact shape that FAILS the
∀-form under `[]` — satisfies it under a resolving K, at EVERY grade and flag. -/
theorem vgood_anyGrade (n : Nat) (ℓ : Label) :
    ∀ (γ' : GradeVec Mult) (b' : Bool), LWSVg (Kres n ℓ) γ' b' (wbad n ℓ) := by
  intro γ' b'
  refine LWSVg.vthunk (LWSCg.ret (q := 1) (γ' := γ') ?_ ?_)
  · simp [GradeVec.smul]
  · have e1 : decide ((1 : Mult) ≠ 0) = true := decide_eq_true_eq.mpr one_ne_zero
    cases b' with
    | true =>
      rw [show (true && decide ((1 : Mult) ≠ 0)) = true by rw [e1]; rfl]
      exact LWSVg.vcap_live (resolves_Kres n ℓ)
    | false =>
      rw [show (false && decide ((1 : Mult) ≠ 0)) = false by rfl]
      exact LWSVg.vcap_dormant

/-- CONSUMABILITY, harder shape: a PAIR of resolving caps wrapped in a thunk also meets
the ∀-form — pair's grade split (`γ' = γ' + 0s`) composes at any target grade. -/
theorem vpair_anyGrade (n : Nat) (ℓ : Label) :
    ∀ (γ' : GradeVec Mult) (b' : Bool),
      LWSVg (Kres n ℓ) γ' b' (Val.vthunk (Comp.ret (Val.pair (Val.vcap n ℓ) (Val.vcap n ℓ)))) := by
  intro γ' b'
  refine LWSVg.vthunk (LWSCg.ret (q := 1) (γ' := γ') ?_ ?_)
  · simp [GradeVec.smul]
  · have e1 : decide ((1 : Mult) ≠ 0) = true := decide_eq_true_eq.mpr one_ne_zero
    have hb : (b' && decide ((1 : Mult) ≠ 0)) = b' := by rw [e1, Bool.and_true]
    rw [hb]
    -- pair split: γ' = γ' + zeros|γ'|  (`add_zeros`)
    refine LWSVg.pair (γ_v := γ') (γ_w := GradeVec.zeros γ'.length) ?_ ?_ ?_ ?_
    · show (γ' : GradeVec Mult) = GradeVec.add γ' (GradeVec.zeros γ'.length)
      exact (GradeVec.add_zeros γ').symm
    · simp
    · cases b' with
      | true => exact LWSVg.vcap_live (resolves_Kres n ℓ)
      | false => exact LWSVg.vcap_dormant
    · cases b' with
      | true => exact LWSVg.vcap_live (resolves_Kres n ℓ)
      | false => exact LWSVg.vcap_dormant
