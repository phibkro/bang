/-
  Bang/CapEscapeWitness.lean — ADR-0054 escape witness (finding artifact, re-keyed to identity dispatch).
  ─────────────────────────────────────────────────────────────────────────────────
  THE FINDING (carried onto identity dispatch): a capability that ESCAPES its handler via the RESULT
  TYPE (`U {ℓ} (F _ _)` — the effect carried as data) is WELL-TYPED by the effect-row discipline. Under
  ADR-0054 IDENTITY dispatch the OPERATIONAL outcome of such an escape is no longer uniform:

    - DIRECT-FORCE (`escapeB`, forced at top level, no re-handler): STUCK — the cap names the popped
      handler's identity and `splitAtId [] 0 = none` (fail-loud). Rejected by `NonEscape`
      (`Bang.LWRegress.escapeB_not_nonEscape`). This is the robust, design-call-independent witness.
    - RE-HANDLED (`scratch/IdentityCollisionProbe.progB`, forced under a fresh same-depth handler):
      RESOLVES to the WRONG handler (identity collision) — the WC keystone-2c gap, pending an operator
      design call. NOT used as an oracle here (we do not assert the bug correct).

  The typed witness below is `h_perform`: the escape's op head `perform (vvar 0) "get" unit` is WELL-TYPED
  under the handle-bound capability `vvar 0 : Cap 1` (the 3-arg perform with a cap VALUE). Combined with
  the LWRegress behavioural+structural oracle (escapeB stuck + `¬ NonEscape`), this records that the
  TYPING permits the escape while `NonEscape` (a `type_safety` premise) is exactly what rules it out.

  Imports ONLY `Bang.Operational` (+ `Bang.Mult`, `Bang.LWRegress`).
-/
import Bang.Operational
import Bang.Mult
import Bang.LWRegress

namespace Bang.CapEscapeWitness

open Bang
open Bang.EffectRow (Label EffRow)

/-- A concrete `EffSig`: label `1` is a `state`-label whose ops are `get`/`put`, both `unit -> unit`. -/
@[reducible] def sigU : EffSig EffRow QTT where
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

attribute [local instance] sigU

/-- The escaping value's type: a thunk of the `{get}`-effectful computation `F 1 unit`. -/
abbrev U1 : VTy EffRow QTT := VTy.U ({1} : EffRow) (CTy.F 1 VTy.unit)

/-- **THE TYPED WITNESS.** ADR-0054: the escape's op head is well-typed under the handle-bound
capability `vvar 0 : Cap 1` (the 3-arg perform with a cap VALUE): `perform (vvar 0) "get" unit : F 1 unit`
at effect `{1}`, context `[Cap 1]`, grade `(1 . zeros) + basis 1 0` (the cap var is used once). -/
theorem h_perform :
    HasCTy (Eff := EffRow) (Mult := QTT)
      ((1 : QTT) • (GradeVec.zeros 1 : GradeVec QTT) + (GradeVec.basis 1 0 : GradeVec QTT)) ([VTy.cap 1] : TyCtx EffRow QTT)
      (.perform (.vvar 0) "get" .vunit) ({1} : EffRow) (CTy.F 1 VTy.unit) := by
  refine HasCTy.perform (Eff := EffRow) (Mult := QTT) (ℓ := 1) (q := 1)
    (A := VTy.unit) (B := VTy.unit)
    (HasVTy.vvar (Γ := ([VTy.cap 1] : TyCtx EffRow QTT)) (i := 0) rfl) ?hle rfl rfl (HasVTy.vunit (Γ := ([VTy.cap 1] : TyCtx EffRow QTT)))
  show EffSig.labelEff (Eff := EffRow) (Mult := QTT) 1 ≤ ({1} : EffRow)
  simp [EffSig.labelEff, sigU]

/-- The escape is STUCK on `Source.eval` and `¬ NonEscape` — the safety oracle lives in
`Bang.LWRegress` (`escapeB_stuck` #guard + `escapeB_not_nonEscape`). Re-export the structural rejection
here so this finding file is self-contained on the typed side. -/
theorem escape_rejected : ¬ NonEscape ([], Bang.LWRegress.escapeB) :=
  Bang.LWRegress.escapeB_not_nonEscape

end Bang.CapEscapeWitness
