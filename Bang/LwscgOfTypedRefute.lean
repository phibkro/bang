import Bang.Model

/-! REGRESSION WITNESS — keep; the existence-lift `lwscg_of_typed` (Bang/Model.lean) takes
cap-resolution as a SEPARATE hypothesis (`∀ p ∈ capsC c, ResolvesLabel K …`), NOT from `LWSC`.
The THIRD don't-weaken guard (after `CohSubstRefute`, `LwscgLengthRefute`). Sorry-free, axiom-clean
(`[propext, Quot.sound]`). Task #46; ADR-0060.

Shows the once-proposed comp existence-lift FROM `LWSC`
    lwscg_of_typed : HasCTy γ Γ c φ C → LWSC K b c → LWSCg K γ b c
is FALSE as written (WHY the live lift takes caps-resolve directly). The typeless `LWSC`'s storage
gates (`ret`/`app`/… use an
EXISTENTIAL ℕ budget `q'`) can be chosen `q' = 0`, storing a cap DORMANT even when
the type-grade `γ` forces the corresponding `LWSCg` gate LIVE (cap must resolve).
A cap sharing a gated value-slot with a live `vvar` rides the vvar's nonzero grade
into a live `LWSCg` gate, demanding resolution `LWSC` never recorded.

Counterexample (K=[], non-resolving): c = ret (pair (vcap n ℓ) (vvar 0)), Γ=[unit], q=1.
  HasCTy [1] [unit] c ⊥ (F 1 (prod (cap ℓ) unit))   -- grade [1] (the vvar makes it nonzero)
  LWSC  []  true c                                    -- inhabited via ret-gate q'=0 (cap dormant)
  ⊢ LWSCg [] [1] true c                               -- ret gate forced LIVE ⇒ pair ⇒ vcap_live ⇒
                                                       --   ResolvesLabel [] n ℓ — FALSE.
FIX (option A): the lift takes cap-resolution as a SEPARATE hypothesis
(`∀ p ∈ capsC c, ResolvesLabel K p.1 p.2`), NOT from `LWSC`'s lossy gates. -/

namespace Bang.Model

variable {Eff Mult : Type} [Lattice Eff] [OrderBot Eff] [CommSemiring Mult]
  [DecidableEq Mult] [EffSig Eff Mult] [Nontrivial Mult]

open Bang.EffectRow (Label)

/-- No capability resolves under the empty stack. -/
theorem nil_no_resolve (n : Nat) (ℓ : Label) : ¬ ResolvesLabel ([] : EvalCtx) n ℓ := by
  rintro ⟨Kᵢ, h, Kₒ, hsplit, _⟩; simp [splitAtId] at hsplit

/-- The bad value: a cap paired with a live var; typed grade `[1]` (the var forces nonzero). -/
abbrev badVal (n : Nat) (ℓ : Label) : Val := Val.pair (Val.vcap n ℓ) (Val.vvar 0)

/-- Typing: `ret (badVal)` types at grade `[1]` over context `[unit]`, budget `q = 1`. -/
theorem ty_badRet (n : Nat) (ℓ : Label) :
    HasCTy (Eff := Eff) (Mult := Mult) [(1 : Mult)] [VTy.unit]
      (Comp.ret (badVal n ℓ)) ⊥ (CTy.F 1 (VTy.prod (VTy.cap ℓ) VTy.unit)) := by
  refine HasCTy.ret (γ' := [(1 : Mult)]) ?_ (by simp [GradeVec.smul])
  refine HasVTy.pair (A := VTy.cap ℓ) (B := VTy.unit) HasVTy.vcap (HasVTy.vvar ?_) ?_
  · rfl
  · simp [GradeVec.add, GradeVec.zeros, GradeVec.basis]

/-- Typeless: `ret (badVal)` is `LWSC`-OK at flag `true` under `[]` — via the ret-gate `q' = 0`
storing the whole pair (and its cap) DORMANT. No resolution needed. -/
theorem lwsc_badRet (n : Nat) (ℓ : Label) : LWSC [] true (Comp.ret (badVal n ℓ)) := by
  refine LWSC.ret (q := 0) ?_
  rw [show (true && decide ((0 : Nat) ≠ 0)) = false by simp]
  exact LWSV.pair LWSV.vcap_dormant LWSV.vvar

/-- the head of a `•`-scaled grade. -/
theorem head?_smul' (q : Mult) (δ : GradeVec Mult) :
    (q • δ).head? = δ.head?.map (q * ·) := by cases δ <;> simp [GradeVec.smul]

/-- THE REFUTATION: the comp existence-lift from `LWSC` (taken as `H`) is inconsistent. -/
theorem lwscg_of_typed_refuted
    (H : ∀ {γ : GradeVec Mult} {Γ : TyCtx Eff Mult} {K : EvalCtx} {b : Bool}
      {c : Comp} {φ : Eff} {C : CTy Eff Mult},
      HasCTy γ Γ c φ C → LWSC K b c → LWSCg K γ b c)
    (n : Nat) (ℓ : Label) : False := by
  have hg := H (ty_badRet (Eff := Eff) n ℓ) (lwsc_badRet n ℓ)
  cases hg with
  | @ret _ γ' _ _ q_g hγ hv =>
    have hq : q_g ≠ 0 := by
      rintro rfl
      have hd : ([(1 : Mult)] : GradeVec Mult).head? = ((0 : Mult) • γ').head? := by rw [hγ]
      rw [head?_smul'] at hd
      cases hc : γ'.head? with
      | none => rw [hc] at hd; simp at hd
      | some a => rw [hc] at hd; simp at hd
    rw [show (true && decide (q_g ≠ 0)) = true by simp [hq]] at hv
    cases hv with
    | pair _ _ hcap _ =>
      cases hcap with
      | vcap_live hr => exact nil_no_resolve n ℓ hr

end Bang.Model
