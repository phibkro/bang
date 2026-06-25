/-
  Bang/CapEscapeWitness.lean — ADR-0045 B3a finding artifact (NOT a kernel lemma).
  ─────────────────────────────────────────────────────────────────────────
  THE QUESTION (lead, 2026-06-25): is the capability-ESCAPE program WELL-TYPED?

      progB =  let c = (handle (state ℓ) (ret {get-thunk}))   -- a {get}-capability thunk RETURNED
               in handle (state ℓ) ($c)                        -- ...OUT of its handler, re-handled here

  It runs STUCK under BOTH the static-cap kernel AND the legacy dynamic-label kernel (lead-verified on
  `Source.eval` — NO regression; the cap-shift is observationally faithful to dynamic). The remaining
  question for B3a's scope: is the stuck program WELL-TYPED?

  ANSWER (build-confirmed below, axioms ⊆ {propext, Classical.choice, Quot.sound}):
  **YES — `progB_well_typed` elaborates.** So this is a WELL-TYPED-but-STUCK config = a PRE-EXISTING
  progress gap (the dynamic kernel has it too; the pivot did NOT introduce it). The capability escapes
  its handler via the RESULT TYPE (`U {ℓ} (F _ _)` — the effect is carried as data, re-handled later),
  which the effect-ROW typing permits but the OPERATIONAL semantics cannot serve (the handler that the
  escaped cap names is gone by the time it is forced). The fix is the typed NON-ESCAPE discipline
  (capability scoping in the typed re-index), which fuses B3a with B3b — NOT a kernel-step change.

  This file imports ONLY `Bang.Operational` (which builds), so it is a real build-gated artifact while
  the rest of the tree is mid-flip. It uses a concrete singleton-`Finset` `EffSig` with one state label.
-/
import Bang.Operational
import Bang.Mult

namespace Bang.CapEscapeWitness

open Bang
open Bang.EffectRow (Label EffRow)

/-- A concrete `EffSig`: label `1` is a `state`-label whose ONLY ops are `get`/`put`, both `unit → unit`
(the minimal interface that types a `state` handler). Every other label has an empty interface. The row
is the singleton `Finset` (`labelEff ℓ = {ℓ}`) — sets, idempotent, unchanged (ADR-0001/0018). -/
@[reducible] def sigU : EffSig EffRow QTT where
  labelEff ℓ := {ℓ}
  opArg ℓ op := if ℓ = 1 ∧ (op = "get" ∨ op = "put") then some VTy.unit else none
  opRes ℓ op := if ℓ = 1 ∧ (op = "get" ∨ op = "put") then some VTy.unit else none
  labelEff_ne_bot ℓ := Finset.singleton_ne_empty ℓ
  labelEff_sep ℓ ℓ' φ h hne := by
    have hmem : ℓ ∈ ({ℓ'} : EffRow) ∪ φ := h (Finset.mem_singleton_self ℓ)
    apply Finset.singleton_subset_iff.mpr
    rcases Finset.mem_union.1 hmem with hℓ | hφ
    · exact absurd (Finset.mem_singleton.1 hℓ) hne
    · exact hφ

attribute [local instance] sigU

/-- The escaping value's type: a thunk of the `{get}`-effectful computation `F 1 unit`. -/
abbrev U1 : VTy EffRow QTT := VTy.U ({1} : EffRow) (CTy.F 1 VTy.unit)

/-- Label `1`'s interface is exactly `{get, put}` — the `handleState` interface premise. -/
theorem h_iface : ∀ op B, EffSig.opArg (Eff := EffRow) (Mult := QTT) 1 op = some B → op = "get" ∨ op = "put" := by
  intro op B hop
  by_cases h : op = "get" ∨ op = "put"
  · exact h
  · simp only [EffSig.opArg, sigU] at hop; rw [if_neg (by tauto)] at hop; exact absurd hop (by simp)

/-- The escaping operation: `perform 0 1 "get" unit : F 1 unit` at effect `{1}`, closed. -/
theorem h_perform :
    HasCTy (Eff := EffRow) (Mult := QTT) [] [] (.perform 0 1 "get" .vunit) ({1} : EffRow) (CTy.F 1 VTy.unit) :=
  HasCTy.perform (Γ := []) (A := VTy.unit) (B := VTy.unit) (le_refl _) rfl rfl (HasVTy.vunit (Γ := []))

/-- `ret {get-thunk} : F 1 U1` at `⊥` — the capability packaged as a returnable value. -/
theorem h_ret :
    HasCTy (Eff := EffRow) (Mult := QTT) [] [] (.ret (.vthunk (.perform 0 1 "get" .vunit))) ⊥ (CTy.F 1 U1) :=
  HasCTy.ret (Γ := []) (HasVTy.vthunk h_perform) rfl

/-- **M — the ESCAPE.** `handle (state 1 unit) (ret {get-thunk}) : F 1 U1` at `⊥`. The `{get}`
capability thunk is RETURNED OUT of its `state` handler; the handler discharges `{1}` from the BODY
effect (`⊥`, a `ret`), while the thunk keeps `{1}` in its TYPE `U1` — a typed capability escape. -/
theorem h_M :
    HasCTy (Eff := EffRow) (Mult := QTT) [] []
      (.handle (.state 1 .vunit) (.ret (.vthunk (.perform 0 1 "get" .vunit)))) ⊥ (CTy.F 1 U1) := by
  apply HasCTy.handleState (S := VTy.unit) (e := ⊥) rfl rfl rfl rfl h_iface (HasVTy.vunit (Γ := [])) h_ret ?le
  case le => show (⊥ : EffRow) ≤ {1} ⊔ ⊥; simp

/-- **N — the RE-HANDLER.** Under `c : U1`, `handle (state 1 unit) (force c) : F 1 unit` at `⊥`. The
escaped capability is forced and RE-HANDLED by a fresh `state` handler. -/
theorem h_N :
    HasCTy (Eff := EffRow) (Mult := QTT) (GradeVec.basis 1 0) [U1]
      (.handle (.state 1 .vunit) (.force (.vvar 0))) ⊥ (CTy.F 1 VTy.unit) := by
  apply HasCTy.handleState (S := VTy.unit) (e := ({1} : EffRow)) rfl rfl rfl rfl h_iface
    (HasVTy.vunit (Γ := [])) ?body ?le
  case body => exact HasCTy.force (HasVTy.vvar (Γ := [U1]) (i := 0) rfl)
  case le => show ({1} : EffRow) ≤ {1} ⊔ ⊥; simp

/-- **THE FINDING (build-confirmed).** The full capability-escape program `progB = letC M N` IS
WELL-TYPED at `⊥` / `F 1 unit`. Combined with its build-confirmed STUCK behaviour on `Source.eval`
(in BOTH kernels), this is a WELL-TYPED-but-stuck config — a PRE-EXISTING progress gap, fixed by the
typed non-escape discipline (B3b), not by any change to `Source.step`. -/
theorem progB_well_typed :
    HasCTy (Eff := EffRow) (Mult := QTT) [] []
      (.letC (.handle (.state 1 .vunit) (.ret (.vthunk (.perform 0 1 "get" .vunit))))
             (.handle (.state 1 .vunit) (.force (.vvar 0)))) ⊥ (CTy.F 1 VTy.unit) := by
  have hN' : HasCTy (Eff := EffRow) (Mult := QTT) ((1 * q_or_1 (1 : QTT)) :: []) [U1]
      (.handle (.state 1 .vunit) (.force (.vvar 0))) ⊥ (CTy.F 1 VTy.unit) := by
    rw [show (1 * q_or_1 (1 : QTT)) = 1 from by decide]; exact h_N
  have hγ : (GradeVec.zeros 0 : GradeVec QTT) = q_or_1 (1 : QTT) • ([] : GradeVec QTT) + [] := by rfl
  have h := HasCTy.letC (Γ := []) (γ₁ := []) (γ₂ := []) (q1 := 1) (q2 := 1)
    (A := U1) (B := CTy.F 1 VTy.unit) (φ₁ := ⊥) (φ₂ := ⊥) h_M hN' hγ
  rw [show (⊥ : EffRow) ⊔ ⊥ = ⊥ from by simp] at h
  exact h

/-- The escape program runs STUCK (build-confirmed; matches the dynamic kernel — no regression). The
`#guard` is the behavioural artifact: it pins the operational outcome so the "well-typed but stuck"
finding is grounded in a run, not reasoning. -/
private def progB : Comp :=
  .letC (.handle (.state 1 .vunit) (.ret (.vthunk (.perform 0 1 "get" .vunit))))
        (.handle (.state 1 .vunit) (.force (.vvar 0)))
private def progB_stuck : Bool := match Source.eval 300 progB with | .stuck => true | _ => false
#guard progB_stuck

end Bang.CapEscapeWitness
