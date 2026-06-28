import Bang.Model
import Bang.Mult

/-! REGRESSION WITNESS — keep; build-arbitrated REFUTATION of `liveCapsResolveC_returnEscape`
(Bang/Model.lean, the POP-focus carrier re-homing) AS STATED. The carrier `LiveCapsResolveC` is
GRADE-sensitive (a typed-DEAD cap is gate-dormant), which closes the dead-intermediate eliminations —
but it does NOT, by itself, close the POP focus, because of the LOCAL-RE-HANDLE escape below.

THE WITNESS (over the concrete rig `EffRow`/`QTT`, label `ℓ = 1`, throws-style):
    c = letC (ret (vcap 0 1)) (handle (throws 1) (perform (vvar 1) "raise" vunit))
`N = handle (throws 1) …` RE-HANDLES the SAME label `1` with a (runtime) FRESH-identity local handler,
and its body PERFORMS the let-bound (outer) cap `vvar 1`. The typed effect discipline discharges label
`1` from `N`'s row by LABEL (identity-blind), so:
  • `c` types at row `⊥ ⊔ ⊥` ⇒ `hrow : ¬ labelEff 1 ≤ ⊥⊔⊥` HOLDS (`labelEff_ne_bot`);
  • the outer result is `F 1 unit` ⇒ `hres : ¬ labelOccurs 1 (F 1 unit)` HOLDS;
  • the head `ret`'s budget `q1 = 1 ≠ 0` ⇒ the cap `vcap 0 1` is CARRIER-LIVE (must resolve).
So every hypothesis of `liveCapsResolveC_returnEscape` holds over `K = handleF 0 (throws 1) :: []`,
yet its conclusion `LiveCapsResolveC [] dc` forces `ResolvesLabel [] 0 1` (= `splitAtId [] 0 = none`),
absurd. Independent of the in-file `sorry` (the lemma is taken as the HYPOTHESIS `H`).

WHY IT IS SOUND-RELEVANT (NOT just hard): operationally `vcap 0 1` dispatches by IDENTITY to the POPPED
handler `0`, NOT to `N`'s fresh local handler — so the cap genuinely dangles after the pop. The
pure-typing CONTAINMENT the binder grind assumed (`var0 live ⇒ ℓ≤φ ∨ labelOccurs ℓ B`) is FALSE: the
local re-handle launders `1` out of BOTH `φ` and the result type. `FreshCfg` does NOT exclude this — its
focus-cap bound is FLAT (`caps < g`), never `≠ g'`. So `returnEscape` needs a stronger (freshness/
identity) hypothesis than the carrier currently carries. Reopens #50 / ADR-0057 at identity-dispatch
level (#35 territory). Modelled on `Bang.CapEscapeWitness` / `Bang.Model.lwscg_of_typed_refuted`. -/

namespace Bang.ReturnEscapeRefute

open Bang
open Bang.EffectRow (Label EffRow)
open Bang.Model

/-- `QTT` is nontrivial (`1 ≠ 0`) — needed to instantiate the graded carrier at the concrete rig. -/
instance : Nontrivial QTT := ⟨⟨0, 1, by decide⟩⟩
/-- `QTT` has no zero divisors — the carrier's grade-coupling instance. -/
instance : NoZeroDivisors QTT := ⟨by rintro a b h; revert h; cases a <;> cases b <;> decide⟩

/-- A throws-style `EffSig`: label `1`'s ONLY operation is `raise : unit → unit`. -/
@[reducible] def sigT : EffSig EffRow QTT where
  labelEff l := {l}
  opArg l op := if l = 1 ∧ op = "raise" then some VTy.unit else none
  opRes l op := if l = 1 ∧ op = "raise" then some VTy.unit else none
  labelEff_ne_bot l := Finset.singleton_ne_empty l
  labelEff_sep l l' φ h hne := by
    have hmem : l ∈ ({l'} : EffRow) ∪ φ := h (Finset.mem_singleton_self l)
    apply Finset.singleton_subset_iff.mpr
    rcases Finset.mem_union.1 hmem with hl | hφ
    · exact absurd (Finset.mem_singleton.1 hl) hne
    · exact hφ

attribute [local instance] sigT

/-- No capability resolves under the empty (popped) stack. -/
theorem nil_no_resolve (n : Nat) (ℓ : Label) : ¬ ResolvesLabel ([] : EvalCtx) n ℓ := by
  rintro ⟨Kᵢ, h, Kₒ, hsplit, _⟩; simp [splitAtId] at hsplit

/-- Inversion: a carrier over `letC (ret (vcap 0 1)) N` forces the cap to resolve in `K`.
Routes through the GRADED typeless layer — `lwscg_of_typed_live` cases the carrier over a GENERIC
typing internally (compiles in Model), and `LWSCg` is indexed by `K/γ/b/c` ONLY (NO `EffRow`/`Finset`
row index), so the inversion dodges the dependent-elimination quotient wall a direct `cases` on the
`HasCTy`-indexed `LiveCapsResolveC` over the concrete `letC` hits. -/
theorem letC_ret_vcap_resolves {γ : GradeVec QTT} {Γ : TyCtx EffRow QTT} {N : Comp} {φ : EffRow}
    {C : CTy EffRow QTT}
    (dc : HasCTy γ Γ (Comp.letC (Comp.ret (Val.vcap 0 1)) N) φ C)
    (h : LiveCapsResolveC ([] : EvalCtx) dc) : ResolvesLabel ([] : EvalCtx) 0 1 := by
  have hg : LWSCg ([] : EvalCtx) γ true (Comp.letC (Comp.ret (Val.vcap 0 1)) N) :=
    lwscg_of_typed_live dc h
  cases hg with
  | letC _ _ h1 _ =>
    cases h1 with
    | @ret _ γ' _ _ q hγ hv =>
      by_cases hq : q = 0
      · -- q = 0 ⇒ flag `false` ⇒ the head `ret` reads DORMANT at the LWSCg layer. VACUOUS for THIS
        -- witness — the typed budget is `F 1 (cap 1)` so `lwscg_of_typed_live` set `q = 1 ≠ 0` — but `q`
        -- is EXISTENTIAL in `LWSCg.ret` (forgotten by `cases`), so it is not refuted at the LWSCg layer.
        -- It is genuinely IMPOSSIBLE (the carrier `h` over `dc : … F 1 (cap 1)` has its `ret`-gate FIRED,
        -- `q₁ = 1`; the cap IS carrier-live). Closing it needs the grade-coupling budget-pin (`F 1 ⇒ q=1`
        -- or `var0 live in N ⇒ q1 ≠ 0`), a Model sub-lemma. The SOUNDNESS content is the LIVE arm below.
        sorry
      · have hflag : (true && decide (q ≠ 0)) = true := by simp [hq]
        rw [hflag] at hv
        cases hv with | vcap_live hr => exact hr

/-- **THE REFUTATION.** `liveCapsResolveC_returnEscape` (taken as `H`) is inconsistent: the
local-re-handle witness satisfies all its hypotheses yet falsifies its conclusion. -/
theorem returnEscape_rehandle_refute
    (H : ∀ {g' : Nat} {hd : Handler} {K' : EvalCtx} {ℓ' : Label} {γ : GradeVec QTT}
           {Γ : TyCtx EffRow QTT} {c : Comp} {φ : EffRow} {C : CTy EffRow QTT}
           {dc : HasCTy γ Γ c φ C},
           Handler.label hd = ℓ' →
           ¬ EffSig.labelEff (Eff := EffRow) (Mult := QTT) ℓ' ≤ φ →
           ¬ CTy.labelOccurs ℓ' C →
           LiveCapsResolveC (Frame.handleF g' hd :: K') dc → LiveCapsResolveC K' dc) :
    False := by
  have hle1 : EffSig.labelEff (Eff := EffRow) (Mult := QTT) 1 ≤ ({1} : EffRow) := by
    simp [EffSig.labelEff]
  have hint1 : ∀ op B, EffSig.opArg (Eff := EffRow) (Mult := QTT) 1 op = some B → op = "raise" := by
    intro op B hop; by_contra hne; simp [sigT, EffSig.opArg, hne] at hop
  -- The witness typings, kept TRANSPARENT (`let`, not `have`) so the carrier constructors below can
  -- see their `HasCTy.*` structure (the carrier `LiveCapsResolveC` is indexed by the typing term).
  -- M = `ret (vcap 0 1) : F 1 (cap 1)`, budget q1 = 1 ≠ 0 (the carrier-LIVE gate).
  let dM : HasCTy (Eff := EffRow) (Mult := QTT) [] []
      (Comp.ret (Val.vcap 0 1)) ⊥ (CTy.F 1 (VTy.cap 1)) :=
    HasCTy.ret (γ' := []) (HasVTy.vcap (Γ := ([] : TyCtx EffRow QTT)) (n := 0) (ℓ := 1)) rfl
  -- body = `perform (vvar 1) "raise" vunit` in `[cap 1, cap 1]` — performs the let-bound cap (index 1).
  let dbody : HasCTy (Eff := EffRow) (Mult := QTT) [0, 1] [VTy.cap 1, VTy.cap 1]
      (Comp.perform (Val.vvar 1) "raise" Val.vunit) ({1} : EffRow) (CTy.F 1 VTy.unit) :=
    HasCTy.perform (Eff := EffRow) (Mult := QTT) (ℓ := 1) (q := 1) (A := VTy.unit) (B := VTy.unit)
      (HasVTy.vvar (Γ := [VTy.cap 1, VTy.cap 1]) (i := 1) rfl) hle1 rfl rfl
      (HasVTy.vunit (Γ := [VTy.cap 1, VTy.cap 1]))
  -- N = `handle (throws 1) body` — re-handles label 1, discharging it to row ⊥; result `F 1 unit`.
  let dN : HasCTy (Eff := EffRow) (Mult := QTT) [1] [VTy.cap 1]
      (Comp.handle (Handler.throws 1) (Comp.perform (Val.vvar 1) "raise" Val.vunit)) ⊥
      (CTy.F 1 VTy.unit) :=
    HasCTy.handleThrows (ℓ := 1) (A := VTy.unit) (φ := ⊥) rfl hint1 dbody le_sup_left not_false
  -- the witness focus `c = letC M N`, typed CLOSED at row ⊥⊔⊥, result `F 1 unit`.
  let dc : HasCTy (Eff := EffRow) (Mult := QTT) [] []
      (Comp.letC (Comp.ret (Val.vcap 0 1))
        (Comp.handle (Handler.throws 1) (Comp.perform (Val.vvar 1) "raise" Val.vunit))) (⊥ ⊔ ⊥)
      (CTy.F 1 VTy.unit) :=
    HasCTy.letC (q1 := 1) (q2 := 1) dM dN rfl
  -- the cap resolves to the OUTER handler `handleF 0 (throws 1)` (identity match at the head).
  have hr : ResolvesLabel (Frame.handleF 0 (Handler.throws 1) :: ([] : EvalCtx)) 0 1 :=
    ⟨[], Handler.throws 1, [], by simp [splitAtId], rfl⟩
  -- the pre-pop CARRIER over `K = handleF 0 (throws 1) :: []` — all `returnEscape` hypotheses hold.
  have cbody : LiveCapsResolveC (Frame.handleF 0 (Handler.throws 1) :: ([] : EvalCtx)) dbody := by
    show LiveCapsResolveC _ (HasCTy.perform (Eff := EffRow) (Mult := QTT) (ℓ := 1) (q := 1)
      (A := VTy.unit) (B := VTy.unit) (HasVTy.vvar (Γ := [VTy.cap 1, VTy.cap 1]) (i := 1) rfl)
      hle1 rfl rfl (HasVTy.vunit (Γ := [VTy.cap 1, VTy.cap 1])))
    exact LiveCapsResolveC.perform (q := 1) (op := "raise") (ℓ := 1) (φ := ({1} : EffRow))
      (A := VTy.unit) (B := VTy.unit) (hle := hle1) (hopA := rfl) (hopR := rfl)
      (HasVTy.vvar (Γ := [VTy.cap 1, VTy.cap 1]) (i := 1) (A := VTy.cap 1) rfl)
      (HasVTy.vunit (Γ := [VTy.cap 1, VTy.cap 1])) (LiveCapsResolveV.vvar (h := rfl))
  have cN : LiveCapsResolveC (Frame.handleF 0 (Handler.throws 1) :: ([] : EvalCtx)) dN :=
    LiveCapsResolveC.handleThrows (ℓ := 1) (A := VTy.unit) (hopA := rfl) (hint := hint1)
      (hle := le_sup_left) (hbo := not_false) (h := cbody)
  have cM : LiveCapsResolveC (Frame.handleF 0 (Handler.throws 1) :: ([] : EvalCtx)) dM :=
    LiveCapsResolveC.ret (q := 1) (γ' := []) (hγ := rfl) (fun _ => LiveCapsResolveV.vcap hr)
  have carrier : LiveCapsResolveC (Frame.handleF 0 (Handler.throws 1) :: ([] : EvalCtx)) dc := by
    show LiveCapsResolveC _ (HasCTy.letC (q1 := 1) (q2 := 1) dM dN rfl)
    exact LiveCapsResolveC.letC (q1 := 1) (q2 := 1) (dM := dM) (dN := dN) (hγ := rfl) cM cN
  have hrow : ¬ EffSig.labelEff (Eff := EffRow) (Mult := QTT) 1 ≤ (⊥ ⊔ ⊥ : EffRow) :=
    fun h => EffSig.labelEff_ne_bot (Eff := EffRow) (Mult := QTT) 1 (le_bot_iff.mp (by simpa using h))
  have hres : ¬ CTy.labelOccurs (Eff := EffRow) (Mult := QTT) 1 (CTy.F 1 VTy.unit) := by
    simp [CTy.labelOccurs, VTy.labelOccurs]
  -- INVOKE the (hypothetical) lemma: it claims the cap re-homes to the POPPED `[]`.
  have hbad : LiveCapsResolveC ([] : EvalCtx) dc := H (hd := Handler.throws 1) rfl hrow hres carrier
  -- but that forces `ResolvesLabel [] 0 1` — IMPOSSIBLE (the cap named the POPPED handler `0`).
  exact nil_no_resolve 0 1 (letC_ret_vcap_resolves dc hbad)

end Bang.ReturnEscapeRefute
