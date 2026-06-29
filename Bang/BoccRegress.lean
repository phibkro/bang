/-
  Bang/BoccRegress.lean — B-occ regression oracle (ADR-0057).
  ─────────────────────────────────────────────────────────────────────────────────
  The ADR-0056 cap-escape gap was: `escapeB` (a `{get}`-thunk capturing its `state 1` handler's
  cap, RETURNED past the handler and forced with no re-handler) is WELL-TYPED at ⊥ yet gets STUCK
  (`splitAtId [] 0 = none`). The behavioural oracle (`Bang.LWRegress.escapeB_not_nonEscape` +
  `#guard escapeB_stuck`) records the stuck run; the TYPING was the hole.

  B-occ (ADR-0057) closes it: the `handleState` rule now carries `¬ LabelOccurs ℓ A` (the handled
  label may not occur in the answer type). `escapeB`'s inner `state 1` handle has answer type
  `U φ (F 1 unit)` — a thunk LATENT in label `1` — so its B-occ premise FAILS and the whole program
  is now `HasCTy`-UNTYPEABLE. This file is the regression:

    • `escapeB_not_typeable`     — the bug witness is rejected by typing, for ANY `EffSig` (the
                                   contradiction is purely structural: a `state 1` handle whose
                                   returned value names label `1`). The headline.
    • `safe_handle_typeable`     — a SAFE own-state handle (answer `unit`, no label-1 occurrence)
                                   STILL types under B-occ. B-occ rejects escape, not handlers.

  This is the oracle ADR-0056 asked for: "the fix must make `progB`/`escapeB` untypeable, then the
  diagonal closes." Self-contained on `Bang.Metatheory` (the inversion lemmas); `escapeB` is inlined
  to match `Bang.LWRegress.escapeB` (whose behavioural oracle `escapeB_stuck`/`escapeB_not_nonEscape`
  records the stuck run — that file is pre-existing RED on the ADR-0055 `Config` reshape, so we do
  not depend on it). `sigU` is the same `{get,put} : unit → unit` signature as `CapEscapeWitness.sigU`.
-/
module

public import Bang.Metatheory
public import Bang.Mult

namespace Bang.BoccRegress

open Bang
open Bang.EffectRow (Label EffRow)

/-- `escapeB` (= `Bang.LWRegress.escapeB`): a `{get}`-thunk capturing the inner `state 1` handler's
cap (`vvar 0`) is RETURNED out and forced at top level (no re-handler). The behavioural oracle in
`Bang.LWRegress` records `Source.eval escapeB = .stuck` + `¬ NonEscape`; here we show it is UNTYPEABLE. -/
def escapeB : Comp :=
  .letC (.handle (.state 1 .vunit) (.ret (.vthunk (.perform (.vvar 0) "get" .vunit))))
        (.force (.vvar 0))

/-! ## 1. The bug witness `escapeB` is now HasCTy-UNTYPEABLE (the headline regression).

If it typed, the inner `state 1` handle would have an answer type `A`; by B-occ, `¬ LabelOccurs 1 A`.
But its body `ret (vthunk (perform (vvar 0) "get" vunit))` forces `A = U φ' B'` where the buried
`perform` on the cap-`1` value requires `labelEff 1 ≤ φ'` — i.e. `LabelOccurs 1 A` holds. Contradiction.
No `EffSig`-specific facts are used: the rejection is structural (the handle is `state 1`, the escaping
value names label `1`). -/
theorem escapeB_not_typeable [EffSig EffRow QTT] :
    ¬ ∃ (γ : GradeVec QTT) (Γ : TyCtx EffRow QTT) (e : EffRow) (C : CTy EffRow QTT),
        HasCTy (Eff := EffRow) (Mult := QTT) γ Γ escapeB e C := by
  rintro ⟨γ, Γ, e, C, h⟩
  simp only [escapeB] at h
  -- peel the outer `letC`: the bound `handle …` types at `F q1 A_let`.
  obtain ⟨γ₁, γ₂, φ₁, φ₂, q1, q2, A_let, _he, _hγ, hHandle, _hN⟩ := h.letC_inv
  -- peel the `handle (state 1 …)`: B-occ gives `hbocc : ¬ LabelOccurs 1 A`, body types at `F q A`.
  obtain ⟨e_body, q, qc, S, A, hC, _hga, _hgr, _hpa, _hpr, _hif, _hs, hbody, _hle, hbocc⟩ :=
    hHandle.handleState_inv
  -- `F q1 A_let = F q A` ⇒ the handle's answer is `A`.
  obtain ⟨_, rfl⟩ := CTy.F.inj hC
  -- peel the `ret`: the returned `vthunk …` has type `A` (the answer type).
  obtain ⟨γ', A', q', _he', hCret, _hγret, hvthunk⟩ := hbody.ret_inv
  obtain ⟨_, rfl⟩ := CTy.F.inj hCret
  -- a `vthunk` only inhabits a `U` type: `A = U φ' B'`, body `perform … : φ' B'`.
  cases hvthunk with
  | vthunk hperf =>
    -- invert the `perform` on the cap-`1` value: its label-effect is below the thunk's row `φ'`.
    cases hperf with
    | perform hc hle' _hopArg _hopRes _hv =>
      -- the cap value is `vvar 0` in context `cap 1 :: Γ`, so its label is `1`.
      cases hc with
      | vvar hget =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, VTy.cap.injEq] at hget
        subst hget
        -- `labelEff 1 ≤ φ'` ⇒ `LabelOccurs 1 (U φ' B')` ⇒ contradicts B-occ.
        exact hbocc (Or.inl hle')

/-! ## 2. A SAFE own-state handle STILL types under B-occ (answer `unit`, no label-1 occurrence).

`sigU`: label `1` = `get`/`put`, both `unit → unit`. `handle (state 1 vunit) (ret vunit) : F 1 unit`
— the answer type `unit` carries no label, so `¬ LabelOccurs 1 unit` holds (`unit` ↦ `False`). B-occ
admits it: the discipline forbids ESCAPE (label in the answer), not handlers. -/
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

theorem safe_handle_typeable :
    HasCTy (Eff := EffRow) (Mult := QTT) [] []
      (.handle (.state 1 .vunit) (.ret .vunit)) ⊥ (CTy.F 1 VTy.unit) := by
  apply HasCTy.handleState (S := VTy.unit) (q := 1) (qc := 0)
    (s₀ := .vunit) (e := ⊥) (φ := ⊥)
  · show EffSig.opArg (Eff := EffRow) (Mult := QTT) 1 "get" = some VTy.unit
    simp [EffSig.opArg, sigU]
  · show EffSig.opRes (Eff := EffRow) (Mult := QTT) 1 "get" = some VTy.unit
    simp [EffSig.opRes, sigU]
  · show EffSig.opArg (Eff := EffRow) (Mult := QTT) 1 "put" = some VTy.unit
    simp [EffSig.opArg, sigU]
  · show EffSig.opRes (Eff := EffRow) (Mult := QTT) 1 "put" = some VTy.unit
    simp [EffSig.opRes, sigU]
  · intro op B hop
    by_cases hg : op = "get"
    · exact Or.inl hg
    by_cases hp : op = "put"
    · exact Or.inr hp
    · simp only [EffSig.opArg, sigU, hg, hp] at hop
      rw [if_neg (by tauto)] at hop; exact absurd hop (by simp)
  · exact HasVTy.vunit (Γ := [])
  · -- body `ret vunit : F 1 unit` under `[cap 1]`, grade `[0] = 1 • zeros`.
    have : HasCTy (Eff := EffRow) (Mult := QTT) ((1 : QTT) • GradeVec.zeros 1) [VTy.cap 1]
        (.ret .vunit) ⊥ (CTy.F 1 VTy.unit) :=
      HasCTy.ret (HasVTy.vunit (Γ := [VTy.cap 1])) rfl
    simpa using this
  · show (⊥ : EffRow) ≤ EffSig.labelEff (Eff := EffRow) (Mult := QTT) 1 ⊔ ⊥; exact bot_le
  · -- B-occ side-condition: label `1` does not occur in the answer type `unit`.
    show ¬ LabelOccurs (Eff := EffRow) (Mult := QTT) 1 VTy.unit
    simp [LabelOccurs, VTy.labelOccurs]

/-! ## 2.5. The ARROW-GUARDED escape — `escapeB_app` (the `wsCfg_step` POP wall).

B-occ on the answer type catches the SURFACE escape (`escapeB`, §1) but is structurally BLIND to a cap
hidden behind a function arrow that `app` ELIMINATES. `escapeB_app` wraps the same label-`1`-performing
thunk `w := vthunk(perform (vvar0) "get" vunit)` as the DISCARDED argument of `app (lam (ret vunit)) w`.
The `app` rule (Syntax.lean `app`) sets the result type to the arrow's RESULT (`F 1 unit`) and consumes
the argument type `A' = U {1} (F 1 unit)` — so the handle's answer type is `A = U ⊥ (F 1 unit)`, which
does NOT mention label `1`. Hence `¬ LabelOccurs 1 A` HOLDS and B-occ ADMITS `escapeB_app` — yet `w`'s
thunk row is `{1}`, so the deep-modulo-performability `WSV` invariant (Model.lean) flags the buried cap
as PERFORMABLE. That is exactly the `wsCfg_step` POP wall: `WScfg` is not preserved (a popped handler's
cap, performable per `WSV`, survives in the returned value while `¬ LabelOccurs 1 A`).

The program is operationally SAFE — the `lam` discards `w`, so `w` is never forced and `get` never runs.
The QTT grade records the death: the discarding `lam` binds its argument at multiplicity `q = 0`, so the
`app` annihilates `w`'s grade and the handle binds the capability at `qc = 0` (witnessed by the typing
below — the body derivation's grade vector is `[0]`). So this is a SAFE, B-occ-ADMITTED program whose
`WSV`-preservation fails at POP: a type-level B-occ premise on the answer type cannot see arrow-guarded
latent caps (the info is in the TERM, not the answer type) — the ADR-0041 later-modality territory. -/
def escapeB_app : Comp :=
  .handle (.state 1 .vunit)
    (.ret (.vthunk (.app (.lam (.ret .vunit)) (.vthunk (.perform (.vvar 0) "get" .vunit)))))

/-- The inner argument-thunk's type. `w : U {1} (F 1 unit)` — its thunk row `{1}` performs `get`, so
the buried cap IS performable (`labelOccurs 1 A' = True`, below). This is the type `app` CONSUMES. -/
@[reducible] def escapeB_app_argTy : VTy EffRow QTT :=
  VTy.U ({1} : EffRow) (CTy.F 1 VTy.unit)

/-- The handle's ANSWER type. `A = U ⊥ (F 1 unit)` — the arrow's RESULT, label `1` ABSENT
(`labelOccurs 1 A = False`, below). This is the type B-occ sees; it is blind to `argTy`. -/
@[reducible] def escapeB_app_ansTy : VTy EffRow QTT :=
  VTy.U (⊥ : EffRow) (CTy.F 1 VTy.unit)

/-! ### 2.5a — the gap, as two `labelOccurs` build-facts. -/

/-- The cap is DEEPLY present: label `1` occurs in the argument-thunk type (its row admits `1`). -/
theorem labelOccurs_argTy : LabelOccurs (Eff := EffRow) (Mult := QTT) 1 escapeB_app_argTy := by
  show VTy.labelOccurs 1 (VTy.U ({1} : EffRow) (CTy.F 1 VTy.unit))
  exact Or.inl (le_refl _)

/-- …yet B-occ is BLIND: label `1` does NOT occur in the answer type the handle exposes. -/
theorem not_labelOccurs_ansTy : ¬ LabelOccurs (Eff := EffRow) (Mult := QTT) 1 escapeB_app_ansTy := by
  show ¬ VTy.labelOccurs 1 (VTy.U (⊥ : EffRow) (CTy.F 1 VTy.unit))
  simp only [VTy.labelOccurs, CTy.labelOccurs]
  rintro (h | h)
  · exact (Finset.singleton_ne_empty (1 : Label)) (le_bot_iff.mp h)
  · exact h

/-! ### 2.5b — the headline: `escapeB_app` TYPES (B-occ ADMITS it), with the capability bound at `qc = 0`. -/

/-- **The B-occ-blind witness.** `escapeB_app` is `HasCTy`-typeable — B-occ ADMITS it (contrast
`escapeB_not_typeable`, §1) — at answer type `U ⊥ (F 1 unit)`, with the handled capability bound at
multiplicity `qc = 0` (the body grade is `[0]`). The discarding `lam` (grade `q = 0`) is what hides the
escaping cap from the answer type. So a SAFE program slips past the type-level B-occ premise. -/
theorem escapeB_app_typeable :
    HasCTy (Eff := EffRow) (Mult := QTT) [] [] escapeB_app ⊥
      (CTy.F 1 escapeB_app_ansTy) := by
  -- Bottom-up; `Eff`/`Mult`/`q` pinned on every constructor (so leaves can't default to ℕ and the grade
  -- equalities are concrete `decide` goals). The KEY line is `happ`: `app (q := 0)` ELIMINATES the arrow,
  -- annihilating `w`'s grade `[1]` ⇒ the handle body grade is `[0]` ⇒ the capability is bound at `qc = 0`.
  have hperf : HasCTy (Eff := EffRow) (Mult := QTT)
      [(1 : QTT)] [VTy.cap 1]
      (.perform (.vvar 0) "get" .vunit) ({1} : EffRow) (CTy.F 1 VTy.unit) :=
    HasCTy.perform (Eff := EffRow) (Mult := QTT) (ℓ := 1) (op := "get") (q := 1) (φ := ({1} : EffRow))
      (A := VTy.unit) (B := VTy.unit)
      (HasVTy.vvar (Eff := EffRow) (Mult := QTT) (Γ := [VTy.cap 1]) (i := 0) (A := VTy.cap 1) (by rfl))
      (by show EffSig.labelEff (Eff := EffRow) (Mult := QTT) 1 ≤ ({1} : EffRow);
          simp [EffSig.labelEff])
      (by show EffSig.opArg (Eff := EffRow) (Mult := QTT) 1 "get" = some VTy.unit; simp [EffSig.opArg])
      (by show EffSig.opRes (Eff := EffRow) (Mult := QTT) 1 "get" = some VTy.unit; simp [EffSig.opRes])
      (HasVTy.vunit (Eff := EffRow) (Mult := QTT) (Γ := [VTy.cap 1]))
  have hw : HasVTy (Eff := EffRow) (Mult := QTT)
      [(1 : QTT)] [VTy.cap 1]
      (.vthunk (.perform (.vvar 0) "get" .vunit)) escapeB_app_argTy :=
    HasVTy.vthunk hperf
  have hbody : HasCTy (Eff := EffRow) (Mult := QTT)
      [(0 : QTT), (0 : QTT)] (escapeB_app_argTy :: [VTy.cap 1])
      (.ret .vunit) ⊥ (CTy.F 1 VTy.unit) :=
    HasCTy.ret (Eff := EffRow) (Mult := QTT) (q := 1)
      (HasVTy.vunit (Eff := EffRow) (Mult := QTT) (Γ := escapeB_app_argTy :: [VTy.cap 1])) (by decide)
  have hlam : HasCTy (Eff := EffRow) (Mult := QTT)
      [(0 : QTT)] [VTy.cap 1]
      (.lam (.ret .vunit)) ⊥ (CTy.arr 0 escapeB_app_argTy (CTy.F 1 VTy.unit)) :=
    HasCTy.lam (Eff := EffRow) (Mult := QTT) hbody
  -- `app (lam …) w : F 1 unit` — arrow ELIMINATED at `q = 0` ⇒ `w`'s grade `[1]` is annihilated ⇒ `[0]`.
  have happ : HasCTy (Eff := EffRow) (Mult := QTT)
      [(0 : QTT)] [VTy.cap 1]
      (.app (.lam (.ret .vunit)) (.vthunk (.perform (.vvar 0) "get" .vunit))) ⊥ (CTy.F 1 VTy.unit) :=
    HasCTy.app (Eff := EffRow) (Mult := QTT) (q := 0) hlam hw (by decide)
  have hret : HasCTy (Eff := EffRow) (Mult := QTT)
      [(0 : QTT)] [VTy.cap 1]
      (.ret (.vthunk (.app (.lam (.ret .vunit)) (.vthunk (.perform (.vvar 0) "get" .vunit))))) ⊥
      (CTy.F 1 escapeB_app_ansTy) :=
    HasCTy.ret (Eff := EffRow) (Mult := QTT) (q := 1) (HasVTy.vthunk happ) (by decide)
  -- the `state 1` handle — its B-occ side-condition `¬ LabelOccurs 1 (U ⊥ (F 1 unit))` PASSES; `qc = 0`.
  refine HasCTy.handleState (S := VTy.unit) (q := 1) (qc := 0) (s₀ := .vunit) (e := ⊥) (φ := ⊥)
    ?_ ?_ ?_ ?_ ?_ (HasVTy.vunit (Γ := [])) hret bot_le not_labelOccurs_ansTy
  · show EffSig.opArg (Eff := EffRow) (Mult := QTT) 1 "get" = some VTy.unit; simp [EffSig.opArg]
  · show EffSig.opRes (Eff := EffRow) (Mult := QTT) 1 "get" = some VTy.unit; simp [EffSig.opRes]
  · show EffSig.opArg (Eff := EffRow) (Mult := QTT) 1 "put" = some VTy.unit; simp [EffSig.opArg]
  · show EffSig.opRes (Eff := EffRow) (Mult := QTT) 1 "put" = some VTy.unit; simp [EffSig.opRes]
  · intro op B hop
    by_cases hg : op = "get"
    · exact Or.inl hg
    by_cases hp : op = "put"
    · exact Or.inr hp
    · simp only [EffSig.opArg, hg, hp] at hop
      rw [if_neg (by tauto)] at hop; exact absurd hop (by simp)

/-! ## 3. How far phase-1 typing reaches toward the dissolution `HasConfigTy ⟹ NonEscape`.

The dissolution would need: every reachable `perform (vcap n ℓ) op v` focus has `splitAtId K n`
resolve. Typing DOES force the performed label into the focus effect (below): -/

variable {Eff : Type} [Lattice Eff] [OrderBot Eff] {Mult : Type} [CommSemiring Mult]
  [DecidableEq Mult] [EffSig Eff Mult]

/-- **A performed capability's label is in the focus effect.** If a `perform (vcap n ℓ) op v` focus is
well-typed at effect `e`, then `labelEff ℓ ≤ e` — so the stack typing (`HasStack`) must DISCHARGE `ℓ`,
i.e. SOME label-`ℓ` handler is on the stack. This is the half of the dissolution typing reaches; the
gap it does NOT close is IDENTITY (`n`), see the module note. -/
theorem perform_vcap_label_in_effect {n : Nat} {ℓ : Label} {op : OpId} {v : Val}
    {γ : GradeVec Mult} {Γ : TyCtx Eff Mult} {e : Eff} {C : CTy Eff Mult}
    (h : HasCTy (Eff := Eff) (Mult := Mult) γ Γ (Comp.perform (Val.vcap n ℓ) op v) e C) :
    EffSig.labelEff (Eff := Eff) (Mult := Mult) ℓ ≤ e := by
  cases h with
  | perform hc hle _ _ _ =>
    -- the cap value `vcap n ℓ` has type `cap ℓ`, pinning the perform's label to `ℓ`.
    cases hc with
    | vcap => exact hle

end Bang.BoccRegress
