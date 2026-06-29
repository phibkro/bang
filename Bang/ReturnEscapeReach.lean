module

-- `#guard Source.eval …` runs compiled Operational code at the META phase. Operational
-- is only a transitive dep (via Metatheory), so `meta import` it directly for the #guard.
meta import Bang.Semantics
public import Bang.Soundness
public import Bang.Grade

/-! # ReturnEscapeReach — the TYPEABILITY SEAL for the laundered re-handle escape (#54).

Settles whether `liveCapsResolveC_returnEscape`'s refuted witness (ReturnEscapeRefute) is REACHABLE
from a WELL-TYPED source. The escape returns a thunk that RE-HANDLES the captured cap's label INSIDE,
laundering the label out of the thunk's external type — so the outer handler's answer-type B-occ
(ADR-0057) passes.

KEY DISCRIMINATION (build-found): the OUTER handler must be `state`, NOT `throws`. `handleThrows` pins
its answer `A = opArg ℓ "raise"` (= the raise payload), which CANNOT be the thunk type ⇒ the THROWS
form is UNTYPEABLE (the type system excludes it). `handleState`'s answer `A` is FREE ⇒ it admits the
laundered thunk. So the seal uses STATE throughout (as `progB`/`escapeB` do).

- `progComp_typeable` : the source TYPECHECKS at a label-1-FREE row `⊥ ⊔ (⊥ ⊔ ⊥)`, result `F 1 unit`.
- `#guard Source.eval progComp = .escapedCap` : it FAILS LOUD into the DEFINED capability-escape terminal
  (ADR-0063; was `.stuck` before the reclassification — the inner re-handler mints a fresh id; the
  escaped `vcap 0` finds no `handleF 0` ⇒ `idDispatch = none`).
This typeable program reaching the defined escape (not `.done`) is exactly the `NonEscape`/progress content
the inc-5 diagonal cannot establish from typing — the witness ADR-0063 reclassifies as defined behavior. -/

namespace Bang.ReturnEscapeReach

open Bang
open Bang.EffectRow (Label EffRow)

/-- A `state`-style `EffSig`: label `1`'s ops are `{get, put}`, both `unit → unit` (= `sigU`). -/
@[reducible] def sigS : EffSig EffRow QTT where
  labelEff l := {l}
  opArg l op := if l = 1 ∧ (op = "get" ∨ op = "put") then some VTy.unit else none
  opRes l op := if l = 1 ∧ (op = "get" ∨ op = "put") then some VTy.unit else none
  labelEff_ne_bot l := Finset.singleton_ne_empty l
  labelEff_sep l l' φ h hne := by
    have hmem : l ∈ ({l'} : EffRow) ∪ φ := h (Finset.mem_singleton_self l)
    apply Finset.singleton_subset_iff.mpr
    rcases Finset.mem_union.1 hmem with hl | hφ
    · exact absurd (Finset.mem_singleton.1 hl) hne
    · exact hφ

attribute [local instance] sigS

/-- The captured-cap thunk body (in `[cap 1]`, `vvar 0` = outer cap): re-handle `state 1`, perform the
escaped (let-bound) outer cap with `get`. -/
def Mcomp : Comp :=
  Comp.letC (Comp.ret (Val.vvar 0))
    (Comp.handle (Handler.state 1 Val.vunit) (Comp.perform (Val.vvar 1) "get" Val.vunit))

/-- The full VcapFree source program: outer `state 1` binds the cap, returns the laundered thunk; the
outer `letC` forces it AFTER the handler pops. -/
def progComp : Comp :=
  Comp.letC (Comp.handle (Handler.state 1 Val.vunit) (Comp.ret (Val.vthunk Mcomp)))
            (Comp.force (Val.vvar 0))

-- BEHAVIORAL: the escape FAILS LOUD into the DEFINED `.escapedCap` terminal (ADR-0063) under
-- global-fresh minting (was `.stuck` before the reclassification).
#guard (match Source.eval 300 progComp with | .escapedCap => true | _ => false)

/-- **THE SEAL.** `progComp` TYPECHECKS — at a label-1-FREE row, result `F 1 unit`. The outer
`state 1` handler's answer-type B-occ `¬ LabelOccurs 1 (U (⊥⊔⊥) (F 1 unit))` PASSES (the inner
re-handle laundered label 1 out of the thunk's external type). With the `#guard` above, a TYPEABLE
program reaches the DEFINED capability-escape (`.escapedCap`, ADR-0063) — the progress content the
inc-5 diagonal cannot establish from typing, hence reclassified as defined v1 behavior. -/
theorem progComp_typeable :
    HasCTy (Eff := EffRow) (Mult := QTT) [] [] progComp (⊥ ⊔ (⊥ ⊔ ⊥)) (CTy.F 1 VTy.unit) := by
  have hint : ∀ op B, EffSig.opArg (Eff := EffRow) (Mult := QTT) 1 op = some B → op = "get" ∨ op = "put" := by
    intro op B hop; by_contra hne; push_neg at hne
    simp [sigS, EffSig.opArg, hne.1, hne.2] at hop
  -- inner perform body `perform (vvar 1) "get" unit` in `[cap 1, cap 1, cap 1]`.
  have hbodyN : HasCTy (Eff := EffRow) (Mult := QTT) [0, 1, 0]
      [VTy.cap 1, VTy.cap 1, VTy.cap 1] (Comp.perform (Val.vvar 1) "get" Val.vunit) ({1} : EffRow)
      (CTy.F 1 VTy.unit) := by
    refine HasCTy.perform (Eff := EffRow) (Mult := QTT) (ℓ := 1) (q := 1) (A := VTy.unit)
      (B := VTy.unit) (HasVTy.vvar (Γ := [VTy.cap 1, VTy.cap 1, VTy.cap 1]) (i := 1) rfl) ?hle rfl rfl
      (HasVTy.vunit (Γ := [VTy.cap 1, VTy.cap 1, VTy.cap 1]))
    show EffSig.labelEff (Eff := EffRow) (Mult := QTT) 1 ≤ ({1} : EffRow)
    simp [EffSig.labelEff]
  -- N = inner `handle (state 1)` — re-handles 1, row ⊥, result `F 1 unit`.
  have hN : HasCTy (Eff := EffRow) (Mult := QTT) [1, 0] [VTy.cap 1, VTy.cap 1]
      (Comp.handle (Handler.state 1 Val.vunit) (Comp.perform (Val.vvar 1) "get" Val.vunit)) ⊥
      (CTy.F 1 VTy.unit) :=
    HasCTy.handleState (ℓ := 1) (s₀ := Val.vunit) (S := VTy.unit) (A := VTy.unit) (φ := ⊥)
      rfl rfl rfl rfl hint (HasVTy.vunit (Γ := ([] : TyCtx EffRow QTT))) hbodyN le_sup_left not_false
  -- M' = `ret (vvar 0)` (returns the captured outer cap), budget 1.
  have hM' : HasCTy (Eff := EffRow) (Mult := QTT) [1] [VTy.cap 1] (Comp.ret (Val.vvar 0)) ⊥
      (CTy.F 1 (VTy.cap 1)) :=
    HasCTy.ret (γ' := [1]) (HasVTy.vvar (Γ := [VTy.cap 1]) (i := 0) rfl) (by simp [GradeVec.smul])
  -- M = the laundered thunk body, in `[cap 1]`, row `⊥⊔⊥`, result `F 1 unit`.
  have hM : HasCTy (Eff := EffRow) (Mult := QTT) [1] [VTy.cap 1] Mcomp (⊥ ⊔ ⊥) (CTy.F 1 VTy.unit) :=
    HasCTy.letC (q1 := 1) (q2 := 1) hM' hN (by simp [GradeVec.smul, GradeVec.add, q_or_1])
  -- `ret (vthunk M)` — the laundered thunk has type `U (⊥⊔⊥) (F 1 unit)`, label-1-FREE.
  have hRetThunk : HasCTy (Eff := EffRow) (Mult := QTT) [1] [VTy.cap 1]
      (Comp.ret (Val.vthunk Mcomp)) ⊥ (CTy.F 1 (VTy.U (⊥ ⊔ ⊥) (CTy.F 1 VTy.unit))) :=
    HasCTy.ret (γ' := [1]) (HasVTy.vthunk hM) (by simp [GradeVec.smul])
  -- M1 = the OUTER `handle (state 1)` binding the cap — its answer-type B-occ PASSES (THE CRUX).
  have hM1 : HasCTy (Eff := EffRow) (Mult := QTT) [] []
      (Comp.handle (Handler.state 1 Val.vunit) (Comp.ret (Val.vthunk Mcomp))) ⊥
      (CTy.F 1 (VTy.U (⊥ ⊔ ⊥) (CTy.F 1 VTy.unit))) := by
    refine HasCTy.handleState (ℓ := 1) (s₀ := Val.vunit) (S := VTy.unit)
      (A := VTy.U (⊥ ⊔ ⊥) (CTy.F 1 VTy.unit)) (φ := ⊥) rfl rfl rfl rfl hint (HasVTy.vunit (Γ := ([] : TyCtx EffRow QTT))) hRetThunk
      bot_le ?hbo
    show ¬ VTy.labelOccurs (Eff := EffRow) (Mult := QTT) 1 (VTy.U (⊥ ⊔ ⊥) (CTy.F 1 VTy.unit))
    intro hocc
    simp only [VTy.labelOccurs, CTy.labelOccurs] at hocc
    rcases hocc with h | h
    · exact EffSig.labelEff_ne_bot (Eff := EffRow) (Mult := QTT) 1 (le_bot_iff.mp (by simpa using h))
    · exact h
  -- `force (vvar 0)` — forces the escaped thunk, row `⊥⊔⊥`, result `F 1 unit`.
  have hForce : HasCTy (Eff := EffRow) (Mult := QTT) [1] [VTy.U (⊥ ⊔ ⊥) (CTy.F 1 VTy.unit)]
      (Comp.force (Val.vvar 0)) (⊥ ⊔ ⊥) (CTy.F 1 VTy.unit) :=
    HasCTy.force (HasVTy.vvar (Γ := [VTy.U (⊥ ⊔ ⊥) (CTy.F 1 VTy.unit)]) (i := 0) rfl)
  -- prog = the outer `letC` — types at the label-1-FREE row `⊥ ⊔ (⊥ ⊔ ⊥)`.
  exact HasCTy.letC (q1 := 1) (q2 := 1) hM1 hForce (by simp [GradeVec.smul, GradeVec.add, q_or_1])

end Bang.ReturnEscapeReach
