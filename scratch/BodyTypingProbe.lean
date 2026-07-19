/-
`PATH-independent-body-typing-probe` kill shot.

The canonical `Comp` plus its ROOT type does not determine the local typing choices erased by
lowering. `ambiguousHead` ignores an internally bound identity thunk; the same bytes and root
judgment admit that thunk at every value type `A`. An independent validator can still check a
proof-relevant certificate carrying the choice, but a root-type-only bidirectional pass cannot
recover a unique local interface.
-/
import Bang.Core.Typing
import Bang.Core.Grade

namespace Bang.BodyTypingProbe

open Bang.EffectRow (EffRow)

@[reducible] def emptySig : EffSig EffRow QTT where
  labelEff ℓ := {ℓ}
  opArg _ _ := none
  opRes _ _ := none
  labelEff_ne_bot ℓ := Finset.singleton_ne_empty ℓ
  labelEff_sep ℓ ℓ' φ h hne := by
    have hmem : ℓ ∈ ({ℓ'} : EffRow) ∪ φ := h (Finset.mem_singleton_self ℓ)
    apply Finset.singleton_subset_iff.mpr
    rcases Finset.mem_union.1 hmem with hℓ | hφ
    · exact absurd (Finset.mem_singleton.1 hℓ) hne
    · exact hφ

attribute [local instance] emptySig

/-- The erased local type is not present in these bytes: the continuation ignores the thunk. -/
def ambiguousHead : Comp :=
  .letC
    (.ret (.vthunk (.lam (.ret (.vvar 0)))))
    (.ret (.vint 0))

/-- For every value type `A`, the same computation has the same closed root judgment while its
discarded let-bound thunk has type `U ⊥ (A → F A)`. The existential is genuine erased evidence. -/
theorem ambiguousHead_typed_at_every_hidden_type (A : VTy EffRow QTT) :
    HasCTy (Eff := EffRow) (Mult := QTT) [] [] ambiguousHead ⊥ (CTy.F 1 VTy.int) := by
  let Uid := VTy.U (⊥ : EffRow) (CTy.arr 1 A (CTy.F 1 A))
  have hv : HasVTy (Eff := EffRow) (Mult := QTT) [1] [A] (.vvar 0) A :=
    by simpa [GradeVec.basis] using
      (HasVTy.vvar (Eff := EffRow) (Mult := QTT) (Γ := [A]) (i := 0) (A := A) (by simp))
  have hret : HasCTy (Eff := EffRow) (Mult := QTT) [1] [A]
      (.ret (.vvar 0)) ⊥ (CTy.F 1 A) :=
    HasCTy.ret (q := 1) (γ' := [1]) hv (by decide)
  have hlam : HasCTy (Eff := EffRow) (Mult := QTT) [] []
      (.lam (.ret (.vvar 0))) ⊥ (CTy.arr 1 A (CTy.F 1 A)) :=
    HasCTy.lam hret
  have hheadV : HasVTy (Eff := EffRow) (Mult := QTT) [] []
      (.vthunk (.lam (.ret (.vvar 0)))) Uid :=
    HasVTy.vthunk hlam
  have hhead : HasCTy (Eff := EffRow) (Mult := QTT) [] []
      (.ret (.vthunk (.lam (.ret (.vvar 0))))) ⊥ (CTy.F 0 Uid) :=
    HasCTy.ret (q := 0) (γ' := []) hheadV (by decide)
  have hbodyV : HasVTy (Eff := EffRow) (Mult := QTT) [0] [Uid] (.vint 0) VTy.int :=
    by simpa [GradeVec.zeros] using
      (HasVTy.vint (Eff := EffRow) (Mult := QTT) (Γ := [Uid]) (n := 0))
  have hbody : HasCTy (Eff := EffRow) (Mult := QTT) [0] [Uid]
      (.ret (.vint 0)) ⊥ (CTy.F 1 VTy.int) :=
    HasCTy.ret (q := 1) (γ' := [0]) hbodyV (by decide)
  exact HasCTy.letC (γ := []) (γ₁ := []) (γ₂ := [])
    (q1 := 0) (q2 := 0) hhead hbody (by decide)

-- Two concrete inhabitants make the non-uniqueness executable and resistant to prose drift.
example : HasCTy (Eff := EffRow) (Mult := QTT) [] [] ambiguousHead ⊥ (CTy.F 1 VTy.int) :=
  ambiguousHead_typed_at_every_hidden_type VTy.int

example : HasCTy (Eff := EffRow) (Mult := QTT) [] [] ambiguousHead ⊥ (CTy.F 1 VTy.int) :=
  ambiguousHead_typed_at_every_hidden_type VTy.unit

end Bang.BodyTypingProbe
