/-
Migration type-safety witness (ADR-0053 crux, the operator-requested confirmation).

GOAL: confirm `migrate vFragile` is genuinely WELL-TYPED (HasConfigTy), so that its build-verified
mis-evaluation (`scratch/MigrationSoundnessProbe.lean`: `done(non-int)`) is a real type_safety
counterexample — NOT an ill-typed red herring. This is the FORCED-THUNK migration case, distinct from
`Bang/CapEscapeWitness.lean`'s RETURN-escape `progB` (the known type-directed sorry).

EffSig `sigInt`: label 1 = state with `get : unit → int`, `put : int → unit` (so the read value is an
INT, making a wrong result type-observable); label 2 = throws with `raise : int → int`.
-/
import Bang.Operational
import Bang.Mult

namespace Bang.MigrationTypingProbe

open Bang
open Bang.EffectRow (Label EffRow)

@[reducible] def sigInt : EffSig EffRow QTT where
  labelEff ℓ := {ℓ}
  opArg ℓ op :=
    if ℓ = 1 ∧ op = "get" then some VTy.unit
    else if ℓ = 1 ∧ op = "put" then some VTy.int
    else if ℓ = 2 ∧ op = "raise" then some VTy.int
    else none
  opRes ℓ op :=
    if ℓ = 1 ∧ op = "get" then some VTy.int
    else if ℓ = 1 ∧ op = "put" then some VTy.unit
    else if ℓ = 2 ∧ op = "raise" then some VTy.int
    else none
  labelEff_ne_bot ℓ := Finset.singleton_ne_empty ℓ
  labelEff_sep ℓ ℓ' φ h hne := by
    have hmem : ℓ ∈ ({ℓ'} : EffRow) ∪ φ := h (Finset.mem_singleton_self ℓ)
    apply Finset.singleton_subset_iff.mpr
    rcases Finset.mem_union.1 hmem with hℓ | hφ
    · exact absurd (Finset.mem_singleton.1 hℓ) hne
    · exact hφ

attribute [local instance] sigInt

/-- The thunk's effectful type: `U ⊥ (F 1 int)` — a self-contained get-on-its-own-state, int-returning,
with label 1 discharged inside the thunk (so the carried effect is `⊥`). -/
abbrev UF : VTy EffRow QTT := VTy.U (⊥ : EffRow) (CTy.F 1 VTy.int)

theorem h_iface_state : ∀ op B, EffSig.opArg (Eff := EffRow) (Mult := QTT) 1 op = some B → op = "get" ∨ op = "put" := by
  intro op B hop
  by_cases hg : op = "get"
  · exact Or.inl hg
  by_cases hp : op = "put"
  · exact Or.inr hp
  · simp only [EffSig.opArg, sigInt, hg, hp] at hop
    rw [if_neg (by tauto), if_neg (by tauto), if_neg (by intro h; exact absurd h.1 (by decide))] at hop
    exact absurd hop (by simp)

theorem h_iface_throws : ∀ op B, EffSig.opArg (Eff := EffRow) (Mult := QTT) 2 op = some B → op = "raise" := by
  intro op B hop
  by_cases hr : op = "raise"
  · exact hr
  · simp only [EffSig.opArg, sigInt, hr] at hop
    rw [if_neg (by intro h; exact absurd h.1 (by decide)), if_neg (by intro h; exact absurd h.1 (by decide)),
        if_neg (by tauto)] at hop
    exact absurd hop (by simp)

/-- `perform 0 1 "get" unit : F 1 int` at effect `{1}`, closed. -/
theorem h_perform :
    HasCTy (Eff := EffRow) (Mult := QTT) [] [] (.perform 0 1 "get" .vunit) ({1} : EffRow) (CTy.F 1 VTy.int) :=
  HasCTy.perform (Γ := []) (A := VTy.unit) (B := VTy.int) (le_refl _) rfl rfl (HasVTy.vunit (Γ := []))

/-- The fragile thunk's BODY: `handle (state 1 (vint 7)) (perform 0 1 get) : F 1 int` at `⊥`. -/
theorem h_body :
    HasCTy (Eff := EffRow) (Mult := QTT) [] []
      (.handle (.state 1 (.vint 7)) (.perform 0 1 "get" .vunit)) ⊥ (CTy.F 1 VTy.int) := by
  apply HasCTy.handleState (S := VTy.int) (e := ({1} : EffRow)) rfl rfl rfl rfl h_iface_state
    (HasVTy.vint (Γ := [])) h_perform ?le
  case le => show ({1} : EffRow) ≤ {1} ⊔ ⊥; simp

/-- The lam body: `handle (throws 2) (force (vvar 0)) : F 1 int` at `⊥`, under `[UF]`. -/
theorem h_lambody :
    HasCTy (Eff := EffRow) (Mult := QTT) (GradeVec.basis 1 0) [UF]
      (.handle (.throws 2) (.force (.vvar 0))) ⊥ (CTy.F 1 VTy.int) := by
  apply HasCTy.handleThrows (A := VTy.int) (e := ⊥) rfl h_iface_throws ?body ?le
  case body => exact HasCTy.force (HasVTy.vvar (Γ := [UF]) (i := 0) rfl)
  case le => show (⊥ : EffRow) ≤ {2} ⊔ ⊥; simp

/-- **THE WITNESS.** `migrate vFragile = app (lam (handle (throws 2) (force x))) vFragile` is
WELL-TYPED at `⊥` / `F 1 int`. Combined with its `done(non-int)` evaluation, a type_safety counterexample. -/
theorem migrate_vFragile_well_typed :
    HasCTy (Eff := EffRow) (Mult := QTT) [] []
      (.app (.lam (.handle (.throws 2) (.force (.vvar 0))))
            (.vthunk (.handle (.state 1 (.vint 7)) (.perform 0 1 "get" .vunit)))) ⊥ (CTy.F 1 VTy.int) := by
  have hlam : HasCTy (Eff := EffRow) (Mult := QTT) [] []
      (.lam (.handle (.throws 2) (.force (.vvar 0)))) ⊥ (CTy.arr 1 UF (CTy.F 1 VTy.int)) := by
    have := HasCTy.lam (q := 1) (A := UF) (B := CTy.F 1 VTy.int) (Γ := []) (φ := ⊥) h_lambody
    simpa using this
  have hv : HasVTy (Eff := EffRow) (Mult := QTT) [] [] (.vthunk (.handle (.state 1 (.vint 7)) (.perform 0 1 "get" .vunit))) UF :=
    HasVTy.vthunk h_body
  have h := HasCTy.app (Γ := []) (γ₁ := []) (γ₂ := []) (q := 1) (A := UF) (B := CTy.F 1 VTy.int)
    (φ := ⊥) hlam hv (by rfl)
  exact h

#print axioms migrate_vFragile_well_typed

end Bang.MigrationTypingProbe
