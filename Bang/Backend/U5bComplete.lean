module

public import Bang.Backend.AbstractMachine
public import Bang.Core.Freshness

/-!
  Bang/Backend/U5bComplete.lean — the U5b-handler completeness spine (converse of run_evalD).
  Extracted from Wasm.lean (ADR-0086 wire-in): the store-threaded strong-fuel-induction converse
  that discharges evalD_complete_gen premised on VcapFree + CustomFree. sorryAx-free.
  Kept a standalone Backend module so its SStore/THeap/txnService reductions elaborate in a clean
  import environment (Wasm.lean's accumulated module-reveal state made the abbrevs non-reducing).
-/

/-! ═══════════════════════════════════════════════════════════════════════════════════
    U5b completeness spine (converse of run_evalD) — the route-B replacement for the walled
    evalD_complete_gen below. Premised on VcapFree + CustomFree (ADR-0086); sorryAx-free.
    ═══════════════════════════════════════════════════════════════════════════════════ -/


namespace Bang.CalcVM
@[expose] public section
open Bang.CalcVM
/-! ### Store / heap CustomFree invariants (Backend — depend on `SStore`/`THeap`/`txnService`).
Threaded through the converse spine so `perform get`/`put`/txn-service arms can prove the read
result value is `CFVal`. Preserved by every mutation. -/
open Bang.CustomFree (CFVal CFComp)

/-- Every stored value is CustomFree (state cells). -/
def CFStore (σ : SStore) : Prop := ∀ p ∈ σ, CFVal p.2

/-- Every heaped transaction-log value is CustomFree (txn cells). -/
def CFHeap (τ : THeap) : Prop := ∀ p ∈ τ, ∀ w ∈ p.2, CFVal w

theorem CFStore_nil : CFStore ([] : SStore) := by intro p hp; simp at hp
theorem CFHeap_nil : CFHeap ([] : THeap) := by intro p hp; simp at hp

theorem CFStore_push {σ : SStore} {ℓ : Bang.EffectRow.Label} {s : Val}
    (hσ : CFStore σ) (hs : CFVal s) : CFStore (σ.push ℓ s) := by
  intro p hp
  simp only [SStore.push, List.mem_cons] at hp
  rcases hp with rfl | hp
  · exact hs
  · exact hσ p hp

theorem CFStore_tail {σ : SStore} (hσ : CFStore σ) : CFStore σ.tail := by
  intro p hp; exact hσ p (List.mem_of_mem_tail hp)

theorem CFStore_put {σ : SStore} {ℓ : Bang.EffectRow.Label} {v : Val}
    (hσ : CFStore σ) (hv : CFVal v) : CFStore (σ.put ℓ v) := by
  intro p hp
  induction σ with
  | nil => simp [SStore.put] at hp
  | cons hd tl ih =>
      obtain ⟨ℓ0, w⟩ := hd
      simp only [SStore.put] at hp
      by_cases hℓ : ℓ0 = ℓ
      · simp only [hℓ, if_true, List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact hv
        · exact hσ p (List.mem_cons_of_mem _ hp)
      · simp only [hℓ, if_false, List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact hσ (ℓ0, w) (List.mem_cons_self ..)
        · exact ih (fun q hq => hσ q (List.mem_cons_of_mem _ hq)) hp

theorem CFStore_get {σ : SStore} {ℓ : Bang.EffectRow.Label} {sv : Val}
    (hσ : CFStore σ) (hget : σ.get? ℓ = some sv) : CFVal sv := by
  simp only [SStore.get?, Option.map_eq_some_iff] at hget
  obtain ⟨p, hfind, rfl⟩ := hget
  exact hσ p (List.mem_of_find?_eq_some hfind)

theorem CFHeap_push {τ : THeap} {ℓ : Bang.EffectRow.Label} {Θ : List Val}
    (hτ : CFHeap τ) (hΘ : ∀ w ∈ Θ, CFVal w) : CFHeap (τ.push ℓ Θ) := by
  intro p hp w hw
  simp only [THeap.push, List.mem_cons] at hp
  rcases hp with rfl | hp
  · exact hΘ w hw
  · exact hτ p hp w hw

theorem CFHeap_tail {τ : THeap} (hτ : CFHeap τ) : CFHeap τ.tail := by
  intro p hp w hw; exact hτ p (List.mem_of_mem_tail hp) w hw

theorem CFHeap_put {τ : THeap} {ℓ : Bang.EffectRow.Label} {Θ : List Val}
    (hτ : CFHeap τ) (hΘ : ∀ w ∈ Θ, CFVal w) : CFHeap (τ.put ℓ Θ) := by
  intro p hp w hw
  induction τ with
  | nil => simp [THeap.put] at hp
  | cons hd tl ih =>
      obtain ⟨ℓ0, Θ0⟩ := hd
      simp only [THeap.put] at hp
      by_cases hℓ : ℓ0 = ℓ
      · simp only [hℓ, if_true, List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact hΘ w hw
        · exact hτ p (List.mem_cons_of_mem _ hp) w hw
      · simp only [hℓ, if_false, List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact hτ (ℓ0, Θ0) (List.mem_cons_self ..) w hw
        · exact ih (fun q hq wq hwq => hτ q (List.mem_cons_of_mem _ hq) wq hwq) hp

theorem CFHeap_get {τ : THeap} {ℓ : Bang.EffectRow.Label} {Θ : List Val}
    (hτ : CFHeap τ) (hget : τ.get? ℓ = some Θ) : ∀ w ∈ Θ, CFVal w := by
  simp only [THeap.get?, Option.map_eq_some_iff] at hget
  obtain ⟨p, hfind, rfl⟩ := hget
  intro w hw
  exact hτ p (List.mem_of_find?_eq_some hfind) w hw

theorem CFVal_storeSet {Θ : List Val} {i : Nat} {w : Val}
    (hΘ : ∀ x ∈ Θ, CFVal x) (hw : CFVal w) : ∀ x ∈ Bang.storeSet Θ i w, CFVal x := by
  intro x hx
  simp only [Bang.storeSet] at hx
  rcases List.mem_or_eq_of_mem_set hx with hx | rfl
  · exact hΘ x hx
  · exact hw

/-- `txnService` preserves CustomFree: the serviced value AND the updated log are drawn from the
input log `Θ` and the CustomFree payload `v`. -/
theorem CFVal_txnService {op : Bang.OpId} {v : Val} {Θ : List Val}
    (hv : CFVal v) (hΘ : ∀ w ∈ Θ, CFVal w) :
    CFVal (txnService op v Θ).1 ∧ (∀ w ∈ (txnService op v Θ).2, CFVal w) := by
  simp only [txnService]
  by_cases h1 : op = "newTVar"
  · simp only [h1, if_true]
    refine ⟨by simp [CFVal], ?_⟩
    intro w hw; simp only [List.mem_append, List.mem_singleton] at hw
    rcases hw with hw | rfl
    · exact hΘ w hw
    · exact hv
  · by_cases h2 : op = "readTVar"
    · simp only [h1, h2, if_false, if_true]
      refine ⟨?_, hΘ⟩
      by_cases hlt : (Bang.tvarIdx v).getD 0 < Θ.length
      · rw [← List.getElem_eq_getD (Val.vint 0) (h := hlt)]
        exact hΘ _ (List.getElem_mem hlt)
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; simp [CFVal]
    · simp only [h1, h2, if_false]
      cases v with
      | pair iv w =>
          simp only [CFVal] at hv
          exact ⟨by simp [CFVal], CFVal_storeSet hΘ hv.2⟩
      | _ => exact ⟨by simp [CFVal], hΘ⟩

end -- @[expose] public section
end Bang.CalcVM

/-! # U5b-handler — converse-of-run_evalD completeness spine.

Single strengthened statement, DISJUNCTIVE conclusion over evalD's two outcomes
(term / raised) — the converse unifies what run_evalD splits by hypothesis.
Strong induction on Source `Config.run` fuel F; case on focus M. -/

namespace Bang.CalcVM
@[expose] public section
open Bang.CalcVM
open Bang (Val Comp Frame Config Result Handler)
open Bang.CapCoh (CapLabelCoh capLabelCoh_step capLabelCoh_perform_label)
open Bang.Model (FreshCfg freshCfg_step)
open Bang.CustomFree (CFComp CFVal CFHandler CFComp_subst CFVal_shiftFrom CFComp_ret CFVal_of_CFComp_ret)

/-! ### Ported de-risk lemmas (U5bPort) — the handler-kind `*_composes` bridges (0-delta port).
The fuel IH on the SUBSTITUTED body composes through `evalD`'s handle clause to the whole-handle
node — for each handler kind. No substitution-closure of a black-box relation (the route-A wall). -/

theorem handle_state_composes
    (f g : Nat) (σ : SStore) (τ : THeap) (κ : CStore) (ℓ0 : Bang.EffectRow.Label) (s0 : Val) (M : Comp)
    (v0 : Val) (g' : Nat) (σ' : SStore) (τ' : THeap) (κ' : CStore)
    (hbody : evalD f (g+1) (σ.push g s0) τ κ (Comp.subst (Val.vcap g ℓ0) M)
               = some (.term (.ret v0), g', σ', τ', κ')) :
    evalD (f+1) g σ τ κ (Comp.handle (Handler.state ℓ0 s0) M)
               = some (.term (.ret v0), g', σ'.tail, τ', κ') := by
  simp only [evalD, Handler.label, hbody, Option.bind_some]

theorem handle_txn_composes
    (f g : Nat) (σ : SStore) (τ : THeap) (κ : CStore) (ℓ0 : Bang.EffectRow.Label) (Θ : List Val) (M : Comp)
    (v0 : Val) (g' : Nat) (σ' : SStore) (τ' : THeap) (κ' : CStore)
    (hbody : evalD f (g+1) σ (τ.push g Θ) κ (Comp.subst (Val.vcap g ℓ0) M)
               = some (.term (.ret v0), g', σ', τ', κ')) :
    evalD (f+1) g σ τ κ (Comp.handle (Handler.transaction ℓ0 Θ) M)
               = some (.term (.ret v0), g', σ', τ'.tail, κ') := by
  simp only [evalD, Handler.label, hbody, Option.bind_some]

theorem handle_throws_normal_composes
    (f g : Nat) (σ : SStore) (τ : THeap) (κ : CStore) (ℓ0 : Bang.EffectRow.Label) (M : Comp)
    (v0 : Val) (g' : Nat) (σ' : SStore) (τ' : THeap) (κ' : CStore)
    (hbody : evalD f (g+1) σ τ κ (Comp.subst (Val.vcap g ℓ0) M)
               = some (.term (.ret v0), g', σ', τ', κ')) :
    evalD (f+1) g σ τ κ (Comp.handle (Handler.throws ℓ0) M)
               = some (.term (.ret v0), g', σ', τ', κ') := by
  simp only [evalD, Handler.label, hbody, Option.bind_some]

theorem handle_throws_caught_composes
    (f g : Nat) (σ : SStore) (τ : THeap) (κ : CStore) (ℓ0 : Bang.EffectRow.Label) (M : Comp)
    (w : Val) (g' : Nat) (σ' : SStore) (τ' : THeap) (κ' : CStore)
    (hbody : evalD f (g+1) σ τ κ (Comp.subst (Val.vcap g ℓ0) M)
               = some (.raised g "raise" w, g', σ', τ', κ')) :
    evalD (f+1) g σ τ κ (Comp.handle (Handler.throws ℓ0) M)
               = some (.term (.ret w), g', σ', τ', κ') := by
  simp only [evalD, Handler.label, hbody, Option.bind_some, and_self, if_true]

theorem handle_throws_forward_composes
    (f g : Nat) (σ : SStore) (τ : THeap) (κ : CStore) (ℓ0 : Bang.EffectRow.Label) (M : Comp)
    (n : Nat) (op : Bang.OpId) (w : Val) (g' : Nat) (σ' : SStore) (τ' : THeap) (κ' : CStore)
    (hne : ¬ (n = g ∧ op = "raise"))
    (hbody : evalD f (g+1) σ τ κ (Comp.subst (Val.vcap g ℓ0) M)
               = some (.raised n op w, g', σ', τ', κ')) :
    evalD (f+1) g σ τ κ (Comp.handle (Handler.throws ℓ0) M)
               = some (.raised n op w, g', σ', τ', κ') := by
  simp only [evalD, Handler.label, hbody, Option.bind_some, if_neg hne]

/-- STATE handler forwards a raise (body raised → whole handle raises, pop σ'.tail). -/
theorem handle_state_forward
    (f g : Nat) (σ : SStore) (τ : THeap) (κ : CStore) (ℓ0 : Bang.EffectRow.Label) (s0 : Val) (M : Comp)
    (n : Nat) (op : Bang.OpId) (w : Val) (g' : Nat) (σ' : SStore) (τ' : THeap) (κ' : CStore)
    (hbody : evalD f (g+1) (σ.push g s0) τ κ (Comp.subst (Val.vcap g ℓ0) M)
               = some (.raised n op w, g', σ', τ', κ')) :
    evalD (f+1) g σ τ κ (Comp.handle (Handler.state ℓ0 s0) M)
               = some (.raised n op w, g', σ'.tail, τ', κ') := by
  simp only [evalD, Handler.label, hbody, Option.bind_some]

/-- TRANSACTION handler forwards a raise (body raised → whole handle raises, pop τ'.tail). -/
theorem handle_txn_forward
    (f g : Nat) (σ : SStore) (τ : THeap) (κ : CStore) (ℓ0 : Bang.EffectRow.Label) (Θ : List Val) (M : Comp)
    (n : Nat) (op : Bang.OpId) (w : Val) (g' : Nat) (σ' : SStore) (τ' : THeap) (κ' : CStore)
    (hbody : evalD f (g+1) σ (τ.push g Θ) κ (Comp.subst (Val.vcap g ℓ0) M)
               = some (.raised n op w, g', σ', τ', κ')) :
    evalD (f+1) g σ τ κ (Comp.handle (Handler.transaction ℓ0 Θ) M)
               = some (.raised n op w, g', σ', τ'.tail, κ') := by
  simp only [evalD, Handler.label, hbody, Option.bind_some]

/-- CUSTOM handle composes (body terminates → whole handle terminates, pop κ'.tail). The user-effect
analog of `handle_state_composes`: the custom handle arm PUSHES `κ.push g p cls` for the body's extent
and POPS `κ'.tail` on a `term (ret v0)` exit (ADR-0085 Stage 4). Same 0-delta port shape. -/
theorem handle_custom_composes
    (f g : Nat) (σ : SStore) (τ : THeap) (κ : CStore) (ℓ0 : Bang.EffectRow.Label) (p : Val)
    (cls : List (Bang.OpId × Comp)) (M : Comp)
    (v0 : Val) (g' : Nat) (σ' : SStore) (τ' : THeap) (κ' : CStore)
    (hbody : evalD f (g+1) σ τ (κ.push g p cls) (Comp.subst (Val.vcap g ℓ0) M)
               = some (.term (.ret v0), g', σ', τ', κ')) :
    evalD (f+1) g σ τ κ (Comp.handle (Handler.custom ℓ0 p cls) M)
               = some (.term (.ret v0), g', σ', τ', κ'.tail) := by
  simp only [evalD, Handler.label, hbody, Option.bind_some]

/-- CUSTOM handler forwards a raise (body raised → whole handle raises, pop κ'.tail). The user-effect
analog of `handle_state_forward`. -/
theorem handle_custom_forward
    (f g : Nat) (σ : SStore) (τ : THeap) (κ : CStore) (ℓ0 : Bang.EffectRow.Label) (p : Val)
    (cls : List (Bang.OpId × Comp)) (M : Comp)
    (n : Nat) (op : Bang.OpId) (w : Val) (g' : Nat) (σ' : SStore) (τ' : THeap) (κ' : CStore)
    (hbody : evalD f (g+1) σ τ (κ.push g p cls) (Comp.subst (Val.vcap g ℓ0) M)
               = some (.raised n op w, g', σ', τ', κ')) :
    evalD (f+1) g σ τ κ (Comp.handle (Handler.custom ℓ0 p cls) M)
               = some (.raised n op w, g', σ', τ', κ'.tail) := by
  simp only [evalD, Handler.label, hbody, Option.bind_some]

/-- Fuel monotonicity for `evalD` (the `evalD` analog of `exec_succ`/`exec_mono`): more fuel
never changes a `some`. Needed by the converse spine, which COMBINES two `evalD` sub-runs at
different fuels (e.g. letC binds M0 at `n`, subst-N at `ns`) — run_evalD never needs this because
it inducts on `evalD` fuel directly. Induction on the smaller fuel, `cases` on the focus `M`. -/
theorem evalD_succ : ∀ (f g : Nat) (σ : SStore) (τ : THeap) (κ : CStore) (M : Comp) (r : Outcome × Nat × SStore × THeap × CStore),
    evalD f g σ τ κ M = some r → evalD (f+1) g σ τ κ M = some r := by
  intro f
  induction f with
  | zero => intro g σ τ κ M r h; simp [evalD] at h
  | succ f ih =>
    intro g σ τ κ M r h
    cases M with
    | ret w => simpa [evalD] using h
    | lam M0 => simpa [evalD] using h
    | letC M0 N =>
        simp only [evalD] at h ⊢
        cases hM0 : evalD f g σ τ κ M0 with
        | none => rw [hM0] at h; simp at h
        | some p =>
            rw [hM0] at h; rw [ih _ _ _ _ _ _ hM0]
            obtain ⟨o, g1, σ1, τ1, κ1⟩ := p
            cases o with
            | term t => cases t with
              | ret v0 => simp only [Option.bind_some] at h ⊢; exact ih _ _ _ _ _ _ h
              | _ => simp only [Option.bind_some] at h ⊢; exact h
            | raised n op w => simp only [Option.bind_some] at h ⊢; exact h
    | force a =>
        cases a with
        | vthunk M0 => simp only [evalD] at h ⊢; exact ih _ _ _ _ _ _ h
        | _ => simp [evalD] at h ⊢
    | app M0 u =>
        simp only [evalD] at h ⊢
        cases hM0 : evalD f g σ τ κ M0 with
        | none => rw [hM0] at h; simp at h
        | some p =>
            rw [hM0] at h; rw [ih _ _ _ _ _ _ hM0]
            obtain ⟨o, g1, σ1, τ1, κ1⟩ := p
            cases o with
            | term t => cases t with
              | lam N => simp only [Option.bind_some] at h ⊢; exact ih _ _ _ _ _ _ h
              | _ => simp only [Option.bind_some] at h ⊢; exact h
            | raised n op w => simp only [Option.bind_some] at h ⊢; exact h
    | perform cap op u =>
        -- id-first perform: fuel-agnostic in the state/txn/no-frame arms; RECURSES on a custom
        -- clause-hit (inline clause-service), so that sub-case needs the fuel-succ IH.
        cases cap with
        | vcap n ℓ =>
            simp only [evalD] at h ⊢
            cases hσ : σ.get? n with
            | some s => simp only [hσ] at h ⊢; exact h
            | none =>
            cases hτ : τ.get? n with
            | some Θ => simp only [hσ, hτ] at h ⊢; exact h
            | none =>
            cases hκ : κ.get? n with
            | none => simp only [hσ, hτ, hκ] at h ⊢; exact h
            | some pcls =>
                obtain ⟨p, cls⟩ := pcls
                cases hcl : cls.find? (·.1 == op) with
                | none => simp only [hσ, hτ, hκ, hcl] at h ⊢; exact h
                | some clause => simp only [hσ, hτ, hκ, hcl] at h ⊢; exact ih _ _ _ _ _ _ h
        | _ => simp [evalD] at h ⊢
    | handle h0 M0 =>
        cases h0 with
        | custom ℓ0 p0 cls0 =>
            simp only [evalD, Handler.label] at h ⊢
            cases hM0 : evalD f (g+1) σ τ (κ.push g p0 cls0) (Comp.subst (Val.vcap g ℓ0) M0) with
            | none => rw [hM0] at h; simp at h
            | some p =>
                rw [hM0] at h; rw [ih _ _ _ _ _ _ hM0]
                obtain ⟨o, g1, σ1, τ1, κ1⟩ := p
                cases o with
                | term t => cases t with
                  | ret v0 => simpa using h
                  | _ => simpa using h
                | raised n op w => simpa using h
        | state ℓ0 s0 =>
            simp only [evalD, Handler.label] at h ⊢
            cases hM0 : evalD f (g+1) (σ.push g s0) τ κ (Comp.subst (Val.vcap g ℓ0) M0) with
            | none => rw [hM0] at h; simp at h
            | some p =>
                rw [hM0] at h; rw [ih _ _ _ _ _ _ hM0]
                obtain ⟨o, g1, σ1, τ1, κ1⟩ := p
                cases o with
                | term t => cases t with
                  | ret v0 => simpa using h
                  | _ => simpa using h
                | raised n op w => simpa using h
        | transaction ℓ0 Θ =>
            simp only [evalD, Handler.label] at h ⊢
            cases hM0 : evalD f (g+1) σ (τ.push g Θ) κ (Comp.subst (Val.vcap g ℓ0) M0) with
            | none => rw [hM0] at h; simp at h
            | some p =>
                rw [hM0] at h; rw [ih _ _ _ _ _ _ hM0]
                obtain ⟨o, g1, σ1, τ1, κ1⟩ := p
                cases o with
                | term t => cases t with
                  | ret v0 => simpa using h
                  | _ => simpa using h
                | raised n op w => simpa using h
        | throws ℓ0 =>
            simp only [evalD, Handler.label] at h ⊢
            cases hM0 : evalD f (g+1) σ τ κ (Comp.subst (Val.vcap g ℓ0) M0) with
            | none => rw [hM0] at h; simp at h
            | some p =>
                rw [hM0] at h; rw [ih _ _ _ _ _ _ hM0]
                obtain ⟨o, g1, σ1, τ1, κ1⟩ := p
                cases o with
                | term t => cases t with
                  | ret v0 => simpa using h
                  | _ => simpa using h
                | raised n op w =>
                    by_cases hc : n = g ∧ op = "raise"
                    · simp only [Option.bind_some, if_pos hc] at h ⊢; exact h
                    · simp only [Option.bind_some, if_neg hc] at h ⊢; exact h
    | case a N1 N2 =>
        cases a with
        | inl v => simp only [evalD] at h ⊢; exact ih _ _ _ _ _ _ h
        | inr v => simp only [evalD] at h ⊢; exact ih _ _ _ _ _ _ h
        | _ => simp [evalD] at h ⊢
    | split a N =>
        cases a with
        | pair v w => simp only [evalD] at h ⊢; exact ih _ _ _ _ _ _ h
        | _ => simp [evalD] at h ⊢
    | unfold a =>
        cases a with
        | fold v => simpa [evalD] using h
        | _ => simp [evalD] at h ⊢
    | binop op a b =>
        cases a <;> cases b <;> (simp only [evalD] at h ⊢ <;> exact h)
    | oom => simp [evalD] at h
    | wrong a => simp [evalD] at h

theorem evalD_fuel_mono {f g : Nat} {σ : SStore} {τ : THeap} {κ : CStore} {M : Comp}
    {r : Outcome × Nat × SStore × THeap × CStore} {f2 : Nat}
    (h : evalD f g σ τ κ M = some r) (hle : f ≤ f2) : evalD f2 g σ τ κ M = some r := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hle
  clear hle
  induction k with
  | zero => simpa using h
  | succ k ih => rw [show f + (k+1) = (f + k) + 1 by omega]; exact evalD_succ _ _ _ _ _ _ _ ih

/-- `evalD`'s `.term` outcome is always a TERMINAL computation — `ret v` or `lam M0` (the two
values of CBPV). Every `evalD` clause that yields `.term t` yields one of these; the sequencing
clauses (`letC`/`app`) recurse. Needed by the converse's letC/app term arms to discharge the
non-terminal `t` cases that `cases t` would otherwise leave open. Induction on fuel, `cases` on `M`. -/
theorem evalD_term_shape : ∀ (f g : Nat) (σ : SStore) (τ : THeap) (κ : CStore) (M : Comp)
    (t : Comp) (g' : Nat) (σ' : SStore) (τ' : THeap) (κ' : CStore),
    evalD f g σ τ κ M = some (.term t, g', σ', τ', κ') →
    (∃ v, t = Comp.ret v) ∨ (∃ M0, t = Comp.lam M0) := by
  intro f
  induction f with
  | zero => intro g σ τ κ M t g' σ' τ' κ' h; simp [evalD] at h
  | succ f ih =>
    intro g σ τ κ M t g' σ' τ' κ' h
    cases M with
    | ret w => simp only [evalD, Option.some.injEq, Prod.mk.injEq, Outcome.term.injEq] at h
               exact Or.inl ⟨w, h.1.symm⟩
    | lam M0 => simp only [evalD, Option.some.injEq, Prod.mk.injEq, Outcome.term.injEq] at h
                exact Or.inr ⟨M0, h.1.symm⟩
    | letC M0 N =>
        simp only [evalD] at h
        cases hM0 : evalD f g σ τ κ M0 with
        | none => rw [hM0] at h; simp at h
        | some p =>
            rw [hM0] at h; obtain ⟨o, g1, σ1, τ1, κ1⟩ := p
            cases o with
            | term tt => cases tt with
              | ret v0 => simp only [Option.bind_some] at h; exact ih _ _ _ _ _ _ _ _ _ _ h
              | _ => simp [Option.bind_some] at h
            | raised n op w => simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
                               exact absurd h.1 (by simp)
    | force a =>
        cases a with
        | vthunk M0 => simp only [evalD] at h; exact ih _ _ _ _ _ _ _ _ _ _ h
        | _ => simp [evalD] at h
    | app M0 u =>
        simp only [evalD] at h
        cases hM0 : evalD f g σ τ κ M0 with
        | none => rw [hM0] at h; simp at h
        | some p =>
            rw [hM0] at h; obtain ⟨o, g1, σ1, τ1, κ1⟩ := p
            cases o with
            | term tt => cases tt with
              | lam N => simp only [Option.bind_some] at h; exact ih _ _ _ _ _ _ _ _ _ _ h
              | _ => simp [Option.bind_some] at h
            | raised n op w => simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
                               exact absurd h.1 (by simp)
    | perform cap op u =>
        cases cap with
        | vcap n ℓ =>
            -- id-first perform: resolve by identity `n` in σ/τ/κ. state/txn HITS yield `.ret` (get/put/
            -- txnService); a custom clause-HIT RECURSES (inline service) ⇒ IH; misses/no-frame yield
            -- `.raised` (contradicts the `.term` hypothesis).
            simp only [evalD] at h
            cases hσ : σ.get? n with
            | some sv =>
                by_cases hg : op = "get"
                · simp only [hσ, if_pos hg, Option.some.injEq, Prod.mk.injEq, Outcome.term.injEq] at h
                  exact Or.inl ⟨sv, h.1.symm⟩
                · by_cases hp : op = "put"
                  · simp only [hσ, if_neg hg, if_pos hp, Option.some.injEq, Prod.mk.injEq, Outcome.term.injEq] at h
                    exact Or.inl ⟨_, h.1.symm⟩
                  · simp only [hσ, if_neg hg, if_neg hp, Option.some.injEq, Prod.mk.injEq] at h
                    exact absurd h.1 (by simp)
            | none =>
            cases hτ : τ.get? n with
            | some Θ =>
                by_cases ht : isTxnOp op = true
                · simp only [hσ, hτ, if_pos ht, Option.some.injEq, Prod.mk.injEq, Outcome.term.injEq] at h
                  exact Or.inl ⟨_, h.1.symm⟩
                · rw [Bool.not_eq_true] at ht
                  simp only [hσ, hτ, ht, Bool.false_eq_true, if_false, Option.some.injEq, Prod.mk.injEq] at h
                  exact absurd h.1 (by simp)
            | none =>
            cases hκ : κ.get? n with
            | none => simp only [hσ, hτ, hκ, Option.some.injEq, Prod.mk.injEq] at h; exact absurd h.1 (by simp)
            | some pcls =>
                obtain ⟨p, cls⟩ := pcls
                cases hcl : cls.find? (·.1 == op) with
                | some clause => simp only [hσ, hτ, hκ, hcl] at h; exact ih _ _ _ _ _ _ _ _ _ _ h
                | none => simp only [hσ, hτ, hκ, hcl, Option.some.injEq, Prod.mk.injEq] at h; exact absurd h.1 (by simp)
        | _ => simp [evalD] at h
    | handle h0 M0 =>
        cases h0 with
        | custom ℓ0 p0 cls0 =>
            simp only [evalD, Handler.label] at h
            cases hM0 : evalD f (g+1) σ τ (κ.push g p0 cls0) (Comp.subst (Val.vcap g ℓ0) M0) with
            | none => rw [hM0] at h; simp at h
            | some p =>
                rw [hM0] at h; obtain ⟨o, g1, σ1, τ1, κ1⟩ := p
                cases o with
                | term tt => cases tt with
                  | ret v0 => simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq,
                                Outcome.term.injEq] at h; exact Or.inl ⟨v0, h.1.symm⟩
                  | _ => simp [Option.bind_some] at h
                | raised n op w => simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
                                   exact absurd h.1 (by simp)
        | state ℓ0 s0 =>
            simp only [evalD, Handler.label] at h
            cases hM0 : evalD f (g+1) (σ.push g s0) τ κ (Comp.subst (Val.vcap g ℓ0) M0) with
            | none => rw [hM0] at h; simp at h
            | some p =>
                rw [hM0] at h; obtain ⟨o, g1, σ1, τ1, κ1⟩ := p
                cases o with
                | term tt => cases tt with
                  | ret v0 => simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq,
                                Outcome.term.injEq] at h; exact Or.inl ⟨v0, h.1.symm⟩
                  | _ => simp [Option.bind_some] at h
                | raised n op w => simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
                                   exact absurd h.1 (by simp)
        | transaction ℓ0 Θ =>
            simp only [evalD, Handler.label] at h
            cases hM0 : evalD f (g+1) σ (τ.push g Θ) κ (Comp.subst (Val.vcap g ℓ0) M0) with
            | none => rw [hM0] at h; simp at h
            | some p =>
                rw [hM0] at h; obtain ⟨o, g1, σ1, τ1, κ1⟩ := p
                cases o with
                | term tt => cases tt with
                  | ret v0 => simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq,
                                Outcome.term.injEq] at h; exact Or.inl ⟨v0, h.1.symm⟩
                  | _ => simp [Option.bind_some] at h
                | raised n op w => simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
                                   exact absurd h.1 (by simp)
        | throws ℓ0 =>
            simp only [evalD, Handler.label] at h
            cases hM0 : evalD f (g+1) σ τ κ (Comp.subst (Val.vcap g ℓ0) M0) with
            | none => rw [hM0] at h; simp at h
            | some p =>
                rw [hM0] at h; obtain ⟨o, g1, σ1, τ1, κ1⟩ := p
                cases o with
                | term tt => cases tt with
                  | ret v0 => simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq,
                                Outcome.term.injEq] at h; exact Or.inl ⟨v0, h.1.symm⟩
                  | _ => simp [Option.bind_some] at h
                | raised n op w =>
                    by_cases hc : n = g ∧ op = "raise"
                    · simp only [Option.bind_some, if_pos hc, Option.some.injEq, Prod.mk.injEq,
                        Outcome.term.injEq] at h; exact Or.inl ⟨w, h.1.symm⟩
                    · simp only [Option.bind_some, if_neg hc, Option.some.injEq, Prod.mk.injEq] at h
                      exact absurd h.1 (by simp)
    | case a N1 N2 =>
        cases a with
        | inl v => simp only [evalD] at h; exact ih _ _ _ _ _ _ _ _ _ _ h
        | inr v => simp only [evalD] at h; exact ih _ _ _ _ _ _ _ _ _ _ h
        | _ => simp [evalD] at h
    | split a N =>
        cases a with
        | pair v w => simp only [evalD] at h; exact ih _ _ _ _ _ _ _ _ _ _ h
        | _ => simp [evalD] at h
    | unfold a =>
        cases a with
        | fold v => simp only [evalD, Option.some.injEq, Prod.mk.injEq, Outcome.term.injEq] at h
                    exact Or.inl ⟨v, h.1.symm⟩
        | _ => simp [evalD] at h
    | binop op a b =>
        cases a <;> cases b <;>
          first
          | (simp only [evalD, Option.some.injEq, Prod.mk.injEq, Outcome.term.injEq] at h
             exact Or.inl ⟨_, h.1.symm⟩)
          | simp [evalD] at h
    | oom => simp [evalD] at h
    | wrong a => simp [evalD] at h

/-- The disjunctive outcome-agreement the converse produces for a focus `M` under `K`, with the
CONTINUATION run's fuel BOUNDED by the input fuel `F` (`F' ≤ F`). The bound is the fuel-decrease
bookkeeping the sequencing arms (letC/app) need: M0's terminated-run leftover bounds the subst-run,
which must be `< F` to reapply the strong-induction IH. -/
-- κ-THREADED completeness (#62 Slice 2): `evalD` threads the custom store `κ` (input) → `κ'` (output),
-- exactly as it threads σ/τ. The CF (custom-free) conjuncts are GONE — custom content is now permitted;
-- the κ-store agreement `CCtxCorr κ' (ctxNetEffect K σ' τ')` (the κ-analog of the `CtxCorr σ'` conjunct)
-- replaces them, tying the output store to the context's active custom frames (as `run_evalD` does).
def CompletesTo (F : Nat) (g : Nat) (σ : SStore) (τ : THeap) (κ : CStore) (M : Comp) (K : Bang.EvalCtx) (v : Val) : Prop :=
  ∃ n g' σ' τ' κ',
    ((∃ t, evalD n g σ τ κ M = some (.term t, g', σ', τ', κ') ∧
      CtxCorr σ' (ctxNetEffect K σ' τ') ∧ CtxTxnCorr τ' (ctxNetEffect K σ' τ') ∧
      CCtxCorr κ' (ctxNetEffect K σ' τ') ∧
      CapLabelCoh (g', ctxNetEffect K σ' τ', t) ∧ FreshCfg (g', ctxNetEffect K σ' τ', t) ∧
      ∃ F', F' ≤ F ∧ Config.run F' (g', ctxNetEffect K σ' τ', t) = Result.done v)
    ∨
    (∃ nn oop vv, evalD n g σ τ κ M = some (.raised nn oop vv, g', σ', τ', κ') ∧
      CtxCorr σ' (ctxNetEffect K σ' τ') ∧ CtxTxnCorr τ' (ctxNetEffect K σ' τ') ∧
      CCtxCorr κ' (ctxNetEffect K σ' τ') ∧
      CapLabelCoh (g', ctxNetEffect K σ' τ', Comp.ret vv) ∧
      FreshCfg (g', ctxNetEffect K σ' τ', Comp.ret vv) ∧
      NoResume (ctxNetEffect K σ' τ') nn oop ∧
      ∃ F', F' ≤ F ∧ dispatchRun F' g' nn (ctxNetEffect K σ' τ') (labelOf (ctxNetEffect K σ' τ') nn) oop vv
              = Result.done v))

/-- A SAME-`K` single-reduction bridge for `CompletesTo`: if `M` reduces to `M'` in ONE `evalD`
step (`evalD (f+1) g σ τ M = evalD f g σ τ M'` for all f) AND ONE matching `Source.step`
(`(g,K,M) → (g,K,M')`), then `CompletesTo` for `M'` lifts to `M`. Covers force/case/split/unfold
(the pure same-context reductions); the evalD-step-equality is discharged per-constructor by `rfl`. -/
theorem completesTo_reduce {F g : Nat} {σ : SStore} {τ : THeap} {κ : CStore} {M M' : Comp} {K : Bang.EvalCtx} {v : Val}
    (hevD : ∀ f, evalD (f+1) g σ τ κ M = evalD f g σ τ κ M')
    (hstep : Source.step (g, K, M) = some (g, K, M'))
    (hM' : CompletesTo F g σ τ κ M' K v) : CompletesTo (F+1) g σ τ κ M K v := by
  obtain ⟨n, g', σ', τ', κ', hd⟩ := hM'
  refine ⟨n+1, g', σ', τ', κ', ?_⟩
  rcases hd with ⟨t, hev, hCf, hTf, hCCf, hCohf, hFf, F', hF'le, hcont⟩ | ⟨nn, oop, vv, hev, hCf, hTf, hCCf, hCohf, hFf, hNR, F', hF'le, hcont⟩
  · exact Or.inl ⟨t, by rw [hevD]; exact hev, hCf, hTf, hCCf, hCohf, hFf, F', by omega, hcont⟩
  · exact Or.inr ⟨nn, oop, vv, by rw [hevD]; exact hev, hCf, hTf, hCCf, hCohf, hFf, hNR, F', by omega, hcont⟩

/-- id-first store-disjointness (converse-side): an identity `n` resolving to a TXN frame cannot ALSO
resolve to a STATE frame — the `StratFresh` id-uniqueness makes `splitAtId` deterministic. The inverse
of the AbstractMachine `ctxTxns_get_none_of_ctxStates_some`; proved LOCALLY (own-file discipline) by
the same `splitAtId` determinism. Needed so the id-first `perform` completeness arms establish
`σ.get? n2 = none` (via `CtxCorr`) before a τ-hit — evalD checks σ FIRST. -/
theorem ctxStates_get_none_of_ctxTxns_some {n : Nat} {Θ : List Val} {K : Bang.EvalCtx}
    (hsf : Bang.Model.StratFresh K) (ht : (ctxTxns K).get? n = some Θ) : (ctxStates K).get? n = none := by
  cases hgs : (ctxStates K).get? n with
  | none => rfl
  | some s =>
      exfalso
      obtain ⟨Kᵢ, ℓs, Kₒ, hsps⟩ := splitAtId_of_ctxStates_get hsf hgs
      obtain ⟨Kᵢ', ℓt, Kₒ', hspt⟩ := splitAtId_of_ctxTxns_get hsf ht
      rw [hsps] at hspt; simp at hspt

/-- The perform RAISE base case (converse of `run_evalD`'s `close` helper, AbstractMachine.lean:4573):
a `perform (vcap n2 ℓ2) op u` whose op resolves NO resumptive frame at identity `n2` (state-miss or
non-get/put; txn-miss or non-txn) yields `evalD → raised n2 op u` (stores unchanged), and its
`dispatchRun` continuation IS the kernel's own `Config.run` on the perform (label reconstructed by
`labelOf`, or irrelevant on escape). `NoResume` follows: any frame that resolves is throws (abort) or
fails the op. -/
theorem perform_miss_raises {F g : Nat} {σ : SStore} {τ : THeap} {κ : CStore} {K : Bang.EvalCtx}
    {n2 : Nat} {ℓ2 : Bang.EffectRow.Label} {op : Bang.OpId} {u v : Val}
    (hCtx : CtxCorr σ K) (hTtx : CtxTxnCorr τ K) (hCK : CCtxCorr κ K)
    (hCoh : CapLabelCoh (g, K, Comp.perform (Val.vcap n2 ℓ2) op u))
    (hFresh : FreshCfg (g, K, Comp.perform (Val.vcap n2 ℓ2) op u))
    (hrun : Config.run (F+1) (g, K, Comp.perform (Val.vcap n2 ℓ2) op u) = Result.done v)
    (hst : (ctxStates K).get? n2 = none ∨ (op ≠ "get" ∧ op ≠ "put"))
    (htx : (ctxTxns K).get? n2 = none ∨ isTxnOp op = false)
    -- κ-side miss: no custom frame at n2, OR the frame's clause list has no matching op. Either way the
    -- id-first perform reaches its raise (mirrors evalD's custom perform arm: κ.get? then find?).
    (hcu : (ctxCustoms K).get? n2 = none ∨ ∀ p cl, (ctxCustoms K).get? n2 = some (p, cl) → cl.find? (·.1 == op) = none)
    (hev : evalD 1 g σ τ κ (Comp.perform (Val.vcap n2 ℓ2) op u) = some (.raised n2 op u, g, σ, τ, κ)) :
    CompletesTo (F+1) g σ τ κ (Comp.perform (Val.vcap n2 ℓ2) op u) K v := by
  refine ⟨1, g, σ, τ, κ, Or.inr ⟨n2, op, u, hev, ?_, ?_, ?_, ?_, ?_, ?_, F+1, by omega, ?_⟩⟩
  · rw [ctxNetEffect_self hCtx hTtx]; exact hCtx
  · rw [ctxNetEffect_self hCtx hTtx]; exact hTtx
  · -- CCtxCorr κ (ctxNetEffect K σ τ): ctxNetEffect only rebuilds σ/τ frames, custom projection invariant.
    rw [ctxNetEffect_self hCtx hTtx]; exact hCK
  · rw [ctxNetEffect_self hCtx hTtx]
    exact ⟨fun p hp => hCoh.1 p (by simp only [Bang.Model.capsC] at hp ⊢; exact List.mem_append_right _ hp), hCoh.2⟩
  · rw [ctxNetEffect_self hCtx hTtx]
    exact ⟨hFresh.1, fun p hp => hFresh.2.1 p (by simp only [Bang.Model.capsC] at hp ⊢; exact List.mem_append_right _ hp),
      hFresh.2.2.1, hFresh.2.2.2⟩
  · -- NoResume K n2 op: any resolved frame is throws (abort) or fails the op (miss rules out resuming kind).
    rw [ctxNetEffect_self hCtx hTtx]
    intro Kᵢ hh Kₒ hsp
    cases hh with
    | throws ℓ' => exact Or.inr ⟨ℓ', rfl⟩
    | state ℓ' s =>
        rcases hst with hmiss | ⟨hng, hnp⟩
        · exfalso; rw [splitAtId_state_value hsp] at hmiss; exact absurd hmiss (by simp)
        · left
          have e1 : (op == "get") = false := by simpa using hng
          have e2 : (op == "put") = false := by simpa using hnp
          simp [Handler.label, Bang.handlesOp, e1, e2]
    | transaction ℓ' Θ =>
        rcases htx with hmiss | hnt
        · exfalso; rw [splitAtId_txn_value hsp] at hmiss; exact absurd hmiss (by simp)
        · left
          simp only [isTxnOp, Bool.or_eq_false_iff] at hnt
          obtain ⟨⟨ea, eb⟩, ec⟩ := hnt
          simp only [Handler.label, Bang.handlesOp]
          simp [show (op == "newTVar") = false from by simpa using ea,
            show (op == "readTVar") = false from by simpa using eb,
            show (op == "writeTVar") = false from by simpa using ec]
    | custom ℓ' p cl =>
        -- custom frame resolves at n2 but its clause list misses op ⇒ handlesOp is false (NoResume left).
        left
        rcases hcu with hmiss | hclmiss
        · exfalso; rw [splitAtId_custom_value hsp] at hmiss; exact absurd hmiss (by simp)
        · have hcl := hclmiss p cl (by rw [splitAtId_custom_value hsp])
          simp only [Handler.label, Bang.handlesOp, hcl, Option.isSome_none, Bool.and_false]
  · -- dispatchRun continuation = the kernel's own Config.run on the perform (label reconstructed).
    rw [ctxNetEffect_self hCtx hTtx]
    simp only [dispatchRun]
    cases hsp : Bang.splitAtId K n2 with
    | none =>
        rw [run_perform_label_irrel (labelOf K n2) ℓ2 hsp (F+1)]; exact hrun
    | some t =>
        obtain ⟨Kᵢ, hh, Kₒ⟩ := t
        have hwk : Bang.CapCoh.WeakCoh K (n2, ℓ2) := hCoh.1 (n2, ℓ2) (by simp [Bang.Model.capsC, Bang.Model.capsV])
        have hlab : labelOf K n2 = ℓ2 := by
          simp only [labelOf, hsp, Option.map_some, Option.getD_some]; exact hwk Kᵢ hh Kₒ hsp
        rw [hlab]; exact hrun

set_option maxHeartbeats 1000000 in
theorem evalD_complete_gen_full : ∀ F,
    ∀ (M : Comp) (g : Nat) (σ : SStore) (τ : THeap) (κ : CStore) (K : Bang.EvalCtx) (v : Val),
      CtxCorr σ K → CtxTxnCorr τ K → CCtxCorr κ K → CapLabelCoh (g, K, M) → FreshCfg (g, K, M) →
      Config.run F (g, K, M) = Result.done v →
      -- κ-THREADED spine (#62 Slice 2): the machine custom-store `κ` mirrors the context's active custom
      -- frames (`CCtxCorr κ K`), threaded input→output exactly as σ/τ. The CustomFree premises are DROPPED
      -- (custom content permitted); the custom handle/perform arms resolve real clause-services.
      CompletesTo F g σ τ κ M K v := by
  intro F
  induction F using Nat.strong_induction_on with
  | _ F ih =>
    intro M g σ τ κ K v hCtx hTtx hCK hCoh hFresh hrun
    cases F with
    | zero => simp [Config.run] at hrun
    | succ F' =>
      cases M with
      | ret w =>
          refine ⟨1, g, σ, τ, κ, Or.inl ⟨.ret w, by simp [evalD], ?_, ?_, ?_, ?_, ?_, F'+1, le_rfl, ?_⟩⟩
          · rw [ctxNetEffect_self hCtx hTtx]; exact hCtx
          · rw [ctxNetEffect_self hCtx hTtx]; exact hTtx
          · rw [ctxNetEffect_self hCtx hTtx]; exact hCK
          · rw [ctxNetEffect_self hCtx hTtx]; exact hCoh
          · rw [ctxNetEffect_self hCtx hTtx]; exact hFresh
          · rw [ctxNetEffect_self hCtx hTtx]; exact hrun
      | lam M0 =>
          refine ⟨1, g, σ, τ, κ, Or.inl ⟨.lam M0, by simp [evalD], ?_, ?_, ?_, ?_, ?_, F'+1, le_rfl, ?_⟩⟩
          · rw [ctxNetEffect_self hCtx hTtx]; exact hCtx
          · rw [ctxNetEffect_self hCtx hTtx]; exact hTtx
          · rw [ctxNetEffect_self hCtx hTtx]; exact hCK
          · rw [ctxNetEffect_self hCtx hTtx]; exact hCoh
          · rw [ctxNetEffect_self hCtx hTtx]; exact hFresh
          · rw [ctxNetEffect_self hCtx hTtx]; exact hrun
      | letC M0 N =>
          -- Source steps (g,K,letC M0 N) → (g, letF N::K, M0). IH on focus M0 under letF N::K.
          have hpush : Source.step (g, K, Comp.letC M0 N) = some (g, Frame.letF N :: K, M0) := rfl
          have hCletF : CtxCorr σ (Frame.letF N :: K) := CtxCorr_cons_nonstate (by intro n ℓ s; simp) hCtx
          have hTletF : CtxTxnCorr τ (Frame.letF N :: K) := CtxTxnCorr_cons_nontxn (by intro n ℓ Θ; simp) hTtx
          have hCohletF := capLabelCoh_step _ _ hFresh hCoh hpush
          have hFletF := freshCfg_step _ _ hFresh hpush
          have hrun' : Config.run F' (g, Frame.letF N :: K, M0) = Result.done v := by
            have hs := Config.run_step F' (g, K, Comp.letC M0 N) (by intro gg vv hc; simp at hc)
            rw [hpush] at hs; simp only at hs; rw [← hs]; exact hrun
          have hKletF : CCtxCorr κ (Frame.letF N :: K) := CCtxCorr_cons_noncustom (by intro n ℓ p cls; simp) hCK
          obtain ⟨n, g1, σ1, τ1, κ1, hM0⟩ := ih F' (by omega) M0 g σ τ κ (Frame.letF N :: K) v hCletF hTletF hKletF hCohletF hFletF hrun'
          rcases hM0 with ⟨t, hev, hCf, hTf, hCCf, hCohf, hFf, F1, hF1le, hcont⟩ | ⟨nn, oop, vv, hev, hCf, hTf, hCCf, hCohf, hFf, hNR, F1, hF1le, hcont⟩
          · -- M0 terminated. t must be ret v0 (letF continuation pops ret). Recurse on subst.
            -- ctxNetEffect (letF N::K) = letF N :: ctxNetEffect K, so the letF frame is exposed.
            have hcne : ctxNetEffect (Frame.letF N :: K) σ1 τ1 = Frame.letF N :: ctxNetEffect K σ1 τ1 :=
              ctxNetEffect_cons_nonframe σ1 τ1 (by intro n ℓ s; simp) (by intro n ℓ Θ; simp)
            rw [hcne] at hCohf hFf hcont
            -- t is a terminal (ret / lam). letF only reduces on a ret; a lam under letF is stuck.
            rcases evalD_term_shape _ _ _ _ _ _ _ _ _ _ _ hev with ⟨v0, rfl⟩ | ⟨M2, rfl⟩
            ·
                have hCM' : CtxCorr σ1 (ctxNetEffect K σ1 τ1) :=
                  CtxCorr_ctxNetEffect_nonframe (by intro n ℓ s; simp) (by intro n ℓ Θ; simp) hCf
                have hTM' : CtxTxnCorr τ1 (ctxNetEffect K σ1 τ1) :=
                  CtxTxnCorr_ctxNetEffect_nonframe (by intro n ℓ s; simp) (by intro n ℓ Θ; simp) hTf
                have hKM' : CCtxCorr κ1 (ctxNetEffect K σ1 τ1) := by
                  rw [hcne] at hCCf; exact CCtxCorr_pop_noncustom (by intro n ℓ p cls; simp) hCCf
                have hpop : Source.step (g1, Frame.letF N :: ctxNetEffect K σ1 τ1, Comp.ret v0)
                    = some (g1, ctxNetEffect K σ1 τ1, Comp.subst v0 N) := rfl
                have hFsub := freshCfg_step _ _ hFf hpop
                have hCsub := capLabelCoh_step _ _ hFf hCohf hpop
                -- peel the ret step off the continuation run — the leftover Fs < F' < F (fuel-decrease).
                have hcont' : Config.run F1 (g1, Frame.letF N :: ctxNetEffect K σ1 τ1, Comp.ret v0) = Result.done v := hcont
                have hsub_run : ∃ Fs, Fs < F' ∧ Config.run Fs (g1, ctxNetEffect K σ1 τ1, Comp.subst v0 N) = Result.done v := by
                  cases F1 with
                  | zero => simp [Config.run] at hcont'
                  | succ F1' =>
                      have := Config.run_step F1' (g1, Frame.letF N :: ctxNetEffect K σ1 τ1, Comp.ret v0)
                        (by intro gg vv hc; simp at hc)
                      rw [hpop] at this; rw [this] at hcont'; exact ⟨F1', by omega, hcont'⟩
                obtain ⟨Fs, hFslt, hFs⟩ := hsub_run
                obtain ⟨ns, gs, σs, τs, κs, hsub⟩ :=
                  ih Fs (by omega) (Comp.subst v0 N) g1 σ1 τ1 κ1 (ctxNetEffect K σ1 τ1) v hCM' hTM' hKM' hCsub hFsub hFs
                -- whole letC evalD = evalD M0 (ret v0) then evalD (subst v0 N).
                refine ⟨max n ns + 1, gs, σs, τs, κs, ?_⟩
                rcases hsub with ⟨ts, hevs, hCs, hTs, hCCs, hCohs, hFsF, Fc, hFcle, hcs⟩ | ⟨nn2, oop2, vv2, hevs, hCs, hTs, hCCs, hCohs, hFsF, hNR2, Fc, hFcle, hcs⟩
                · left
                  refine ⟨ts, ?_, ?_, ?_, ?_, ?_, ?_, Fc, by omega, ?_⟩
                  · rw [show max n ns + 1 = (max n ns) + 1 from rfl]
                    simp only [evalD]
                    rw [evalD_fuel_mono hev (Nat.le_max_left n ns)]
                    simp only [Option.bind_some]
                    exact evalD_fuel_mono hevs (Nat.le_max_right n ns)
                  · rw [ctxNetEffect_ctxNetEffect] at hCs; exact hCs
                  · rw [ctxNetEffect_ctxNetEffect] at hTs; exact hTs
                  · rw [ctxNetEffect_ctxNetEffect] at hCCs; exact hCCs
                  · rw [ctxNetEffect_ctxNetEffect] at hCohs; exact hCohs
                  · rw [ctxNetEffect_ctxNetEffect] at hFsF; exact hFsF
                  · rw [ctxNetEffect_ctxNetEffect] at hcs; exact hcs
                · right
                  refine ⟨nn2, oop2, vv2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, Fc, by omega, ?_⟩
                  · rw [show max n ns + 1 = (max n ns) + 1 from rfl]
                    simp only [evalD]
                    rw [evalD_fuel_mono hev (Nat.le_max_left n ns)]
                    simp only [Option.bind_some]
                    exact evalD_fuel_mono hevs (Nat.le_max_right n ns)
                  · rw [ctxNetEffect_ctxNetEffect] at hCs; exact hCs
                  · rw [ctxNetEffect_ctxNetEffect] at hTs; exact hTs
                  · rw [ctxNetEffect_ctxNetEffect] at hCCs; exact hCCs
                  · rw [ctxNetEffect_ctxNetEffect] at hCohs; exact hCohs
                  · rw [ctxNetEffect_ctxNetEffect] at hFsF; exact hFsF
                  · rw [ctxNetEffect_ctxNetEffect] at hNR2; exact hNR2
                  · rw [ctxNetEffect_ctxNetEffect] at hcs; exact hcs
            · -- lam terminal under letF: Config.run gets stuck, contradicting hcont = done.
                exfalso
                cases F1 with
                | zero => simp [Config.run] at hcont
                | succ F1' =>
                    rw [Config.run_step F1' _ (by intro gg vv hc; simp at hc)] at hcont
                    simp [Source.step, Config.run] at hcont
          · -- M0 raised → evalD (letC M0 N) propagates it (letC raised arm). Strip the letF frame from
            -- the raised conclusion (splitAtId/labelOf/dispatch are letF-transparent). Mirror run_evalD:4747.
            have hns : ∀ h0 : Handler, Frame.letF N ≠ Frame.handleF nn h0 := by intro h0; simp
            have hcne : ctxNetEffect (Frame.letF N :: K) σ1 τ1 = Frame.letF N :: ctxNetEffect K σ1 τ1 :=
              ctxNetEffect_cons_nonframe σ1 τ1 (by intro n ℓ s; simp) (by intro n ℓ Θ; simp)
            have hCr' := CtxCorr_ctxNetEffect_nonframe (by intro ℓ s; simp) (by intro ℓ Θ; simp) hCf
            have hTr' := CtxTxnCorr_ctxNetEffect_nonframe (by intro ℓ s; simp) (by intro ℓ Θ; simp) hTf
            have hKr' : CCtxCorr κ1 (ctxNetEffect K σ1 τ1) := by
              rw [hcne] at hCCf; exact CCtxCorr_pop_noncustom (by intro n ℓ p cls; simp) hCCf
            rw [hcne] at hCohf hFf hNR
            have hCohr' := capLabelCoh_pop_letF hCohf
            have hFreshr' := freshCfg_pop_letF hFf
            have hNRr' := noResume_strip_cons hns hNR
            refine ⟨n+1, g1, σ1, τ1, κ1, Or.inr ⟨nn, oop, vv, ?_, hCr', hTr', hKr', hCohr', hFreshr', hNRr', F1, by omega, ?_⟩⟩
            · -- evalD (n+1) (letC M0 N) binds on evalD n M0 = raised (propagate).
              simp only [evalD]; rw [hev]; simp only [Option.bind_some]
            · -- The IH continuation hcont is over ctxNetEffect (letF N::K); strip the letF frame to get the
              -- goal over ctxNetEffect K (frame-transparent: idDispatch_cons_noResume + labelOf_cons_ne).
              have hidEq := idDispatch_cons_noResume (fr := Frame.letF N) (K := ctxNetEffect K σ1 τ1)
                (ℓ := labelOf (ctxNetEffect K σ1 τ1) nn) (op := oop) (v := vv) (by intro h0; simp) hNRr'
              have hlbl := labelOf_cons_ne (fr := Frame.letF N) (K := ctxNetEffect K σ1 τ1) (n := nn) hns
              rw [hcne, hlbl] at hcont
              simp only [dispatchRun] at hcont ⊢
              rw [run_perform_cons_eq hidEq F1] at hcont
              exact hcont
      | force a =>
          -- force (vthunk M0): Source steps (g,K,force(vthunk M0)) → (g,K,M0); evalD force = evalD M0.
          cases a with
          | vthunk M0 =>
              have hstep : Source.step (g, K, Comp.force (Val.vthunk M0)) = some (g, K, M0) := rfl
              have hrun' : Config.run F' (g, K, M0) = Result.done v := by
                have hs := Config.run_step F' (g, K, Comp.force (Val.vthunk M0)) (by intro gg vv hc; simp at hc)
                rw [hstep] at hs; simp only at hs; rw [← hs]; exact hrun
              exact completesTo_reduce (fun f => rfl) hstep
                (ih F' (by omega) M0 g σ τ κ K v hCtx hTtx hCK
                  (capLabelCoh_step _ _ hFresh hCoh hstep) (freshCfg_step _ _ hFresh hstep) hrun')
          | vcap _ _ => exfalso; cases F' <;> simp_all [Config.run, Source.step]
          | vunit => exfalso; cases F' <;> simp_all [Config.run, Source.step]
          | vint _ => exfalso; cases F' <;> simp_all [Config.run, Source.step]
          | vvar _ => exfalso; cases F' <;> simp_all [Config.run, Source.step]
          | inl _ => exfalso; cases F' <;> simp_all [Config.run, Source.step]
          | inr _ => exfalso; cases F' <;> simp_all [Config.run, Source.step]
          | pair _ _ => exfalso; cases F' <;> simp_all [Config.run, Source.step]
          | fold _ => exfalso; cases F' <;> simp_all [Config.run, Source.step]
      | case a N1 N2 =>
          cases a with
          | inl w =>
              have hstep : Source.step (g, K, Comp.case (Val.inl w) N1 N2) = some (g, K, Comp.subst w N1) := rfl
              have hrun' : Config.run F' (g, K, Comp.subst w N1) = Result.done v := by
                have hs := Config.run_step F' (g, K, Comp.case (Val.inl w) N1 N2) (by intro gg vv hc; simp at hc)
                rw [hstep] at hs; simp only at hs; rw [← hs]; exact hrun
              exact completesTo_reduce (fun f => rfl) hstep
                (ih F' (by omega) (Comp.subst w N1) g σ τ κ K v hCtx hTtx hCK
                  (capLabelCoh_step _ _ hFresh hCoh hstep) (freshCfg_step _ _ hFresh hstep) hrun')
          | inr w =>
              have hstep : Source.step (g, K, Comp.case (Val.inr w) N1 N2) = some (g, K, Comp.subst w N2) := rfl
              have hrun' : Config.run F' (g, K, Comp.subst w N2) = Result.done v := by
                have hs := Config.run_step F' (g, K, Comp.case (Val.inr w) N1 N2) (by intro gg vv hc; simp at hc)
                rw [hstep] at hs; simp only at hs; rw [← hs]; exact hrun
              exact completesTo_reduce (fun f => rfl) hstep
                (ih F' (by omega) (Comp.subst w N2) g σ τ κ K v hCtx hTtx hCK
                  (capLabelCoh_step _ _ hFresh hCoh hstep) (freshCfg_step _ _ hFresh hstep) hrun')
          | vcap _ _ => exfalso; cases F' <;> simp_all [Config.run, Source.step]
          | vunit => exfalso; cases F' <;> simp_all [Config.run, Source.step]
          | vint _ => exfalso; cases F' <;> simp_all [Config.run, Source.step]
          | vvar _ => exfalso; cases F' <;> simp_all [Config.run, Source.step]
          | vthunk _ => exfalso; cases F' <;> simp_all [Config.run, Source.step]
          | pair _ _ => exfalso; cases F' <;> simp_all [Config.run, Source.step]
          | fold _ => exfalso; cases F' <;> simp_all [Config.run, Source.step]
      | split a N =>
          cases a with
          | pair w u =>
              have hstep : Source.step (g, K, Comp.split (Val.pair w u) N)
                  = some (g, K, Comp.subst w (Comp.subst (Val.shift u) N)) := rfl
              have hrun' : Config.run F' (g, K, Comp.subst w (Comp.subst (Val.shift u) N)) = Result.done v := by
                have hs := Config.run_step F' (g, K, Comp.split (Val.pair w u) N) (by intro gg vv hc; simp at hc)
                rw [hstep] at hs; simp only at hs; rw [← hs]; exact hrun
              exact completesTo_reduce (fun f => rfl) hstep
                (ih F' (by omega) (Comp.subst w (Comp.subst (Val.shift u) N)) g σ τ κ K v hCtx hTtx hCK
                  (capLabelCoh_step _ _ hFresh hCoh hstep) (freshCfg_step _ _ hFresh hstep) hrun')
          | vcap _ _ => exfalso; cases F' <;> simp_all [Config.run, Source.step]
          | vunit => exfalso; cases F' <;> simp_all [Config.run, Source.step]
          | vint _ => exfalso; cases F' <;> simp_all [Config.run, Source.step]
          | vvar _ => exfalso; cases F' <;> simp_all [Config.run, Source.step]
          | vthunk _ => exfalso; cases F' <;> simp_all [Config.run, Source.step]
          | inl _ => exfalso; cases F' <;> simp_all [Config.run, Source.step]
          | inr _ => exfalso; cases F' <;> simp_all [Config.run, Source.step]
          | fold _ => exfalso; cases F' <;> simp_all [Config.run, Source.step]
      | unfold a =>
          cases a with
          | fold w =>
              -- unfold (fold w) → ret w (terminal). evalD returns .term (.ret w) directly; the
              -- continuation `Config.run F' (g,K,ret w)` follows by peeling the one fold-step off hrun.
              have hstep : Source.step (g, K, Comp.unfold (Val.fold w)) = some (g, K, Comp.ret w) := rfl
              have hrun' : Config.run F' (g, K, Comp.ret w) = Result.done v := by
                have hs := Config.run_step F' (g, K, Comp.unfold (Val.fold w)) (by intro gg vv hc; simp at hc)
                rw [hstep] at hs; simp only at hs; rw [← hs]; exact hrun
              refine ⟨1, g, σ, τ, κ, Or.inl ⟨.ret w, by simp [evalD], ?_, ?_, ?_, ?_, ?_, F', by omega, ?_⟩⟩
              · rw [ctxNetEffect_self hCtx hTtx]; exact hCtx
              · rw [ctxNetEffect_self hCtx hTtx]; exact hTtx
              · rw [ctxNetEffect_self hCtx hTtx]; exact hCK
              · rw [ctxNetEffect_self hCtx hTtx]; exact capLabelCoh_step _ _ hFresh hCoh hstep
              · rw [ctxNetEffect_self hCtx hTtx]; exact freshCfg_step _ _ hFresh hstep
              · rw [ctxNetEffect_self hCtx hTtx]; exact hrun'
          | vcap _ _ => exfalso; cases F' <;> simp_all [Config.run, Source.step]
          | vunit => exfalso; cases F' <;> simp_all [Config.run, Source.step]
          | vint _ => exfalso; cases F' <;> simp_all [Config.run, Source.step]
          | vvar _ => exfalso; cases F' <;> simp_all [Config.run, Source.step]
          | vthunk _ => exfalso; cases F' <;> simp_all [Config.run, Source.step]
          | inl _ => exfalso; cases F' <;> simp_all [Config.run, Source.step]
          | inr _ => exfalso; cases F' <;> simp_all [Config.run, Source.step]
          | pair _ _ => exfalso; cases F' <;> simp_all [Config.run, Source.step]
      | app M0 u =>
          -- sequencing sibling of letC (s/letF/appF, s/ret v0/lam N): Source pushes appF, IH on M0
          -- gives lam N (evalD_term_shape), peel appF → subst u N, recurse at strictly-smaller fuel.
          have hpush : Source.step (g, K, Comp.app M0 u) = some (g, Frame.appF u :: K, M0) := rfl
          have hCappF : CtxCorr σ (Frame.appF u :: K) := CtxCorr_cons_nonstate (by intro n ℓ s; simp) hCtx
          have hTappF : CtxTxnCorr τ (Frame.appF u :: K) := CtxTxnCorr_cons_nontxn (by intro n ℓ Θ; simp) hTtx
          have hCohappF := capLabelCoh_step _ _ hFresh hCoh hpush
          have hFappF := freshCfg_step _ _ hFresh hpush
          have hrun' : Config.run F' (g, Frame.appF u :: K, M0) = Result.done v := by
            have hs := Config.run_step F' (g, K, Comp.app M0 u) (by intro gg vv hc; simp at hc)
            rw [hpush] at hs; simp only at hs; rw [← hs]; exact hrun
          have hKappF : CCtxCorr κ (Frame.appF u :: K) := CCtxCorr_cons_noncustom (by intro n ℓ p cls; simp) hCK
          obtain ⟨n, g1, σ1, τ1, κ1, hM0⟩ := ih F' (by omega) M0 g σ τ κ (Frame.appF u :: K) v hCappF hTappF hKappF hCohappF hFappF hrun'
          rcases hM0 with ⟨t, hev, hCf, hTf, hCCf, hCohf, hFf, F1, hF1le, hcont⟩ | ⟨nn, oop, vv, hev, hCf, hTf, hCCf, hCohf, hFf, hNR, F1, hF1le, hcont⟩
          · have hcne : ctxNetEffect (Frame.appF u :: K) σ1 τ1 = Frame.appF u :: ctxNetEffect K σ1 τ1 :=
              ctxNetEffect_cons_nonframe σ1 τ1 (by intro n ℓ s; simp) (by intro n ℓ Θ; simp)
            rw [hcne] at hCohf hFf hcont
            -- t is a terminal (ret / lam); appF only reduces on a lam; a ret under appF is stuck.
            rcases evalD_term_shape _ _ _ _ _ _ _ _ _ _ _ hev with ⟨v0, rfl⟩ | ⟨M2, rfl⟩
            · -- ret terminal under appF: Config.run stuck, contradicting hcont = done.
              exfalso
              cases F1 with
              | zero => simp [Config.run] at hcont
              | succ F1' =>
                  rw [Config.run_step F1' _ (by intro gg vv hc; simp at hc)] at hcont
                  simp [Source.step, Config.run] at hcont
            · have hCM' : CtxCorr σ1 (ctxNetEffect K σ1 τ1) :=
                CtxCorr_ctxNetEffect_nonframe (by intro n ℓ s; simp) (by intro n ℓ Θ; simp) hCf
              have hTM' : CtxTxnCorr τ1 (ctxNetEffect K σ1 τ1) :=
                CtxTxnCorr_ctxNetEffect_nonframe (by intro n ℓ s; simp) (by intro n ℓ Θ; simp) hTf
              have hKM' : CCtxCorr κ1 (ctxNetEffect K σ1 τ1) := by
                rw [hcne] at hCCf; exact CCtxCorr_pop_noncustom (by intro n ℓ p cls; simp) hCCf
              have hpop : Source.step (g1, Frame.appF u :: ctxNetEffect K σ1 τ1, Comp.lam M2)
                  = some (g1, ctxNetEffect K σ1 τ1, Comp.subst u M2) := rfl
              have hFsub := freshCfg_step _ _ hFf hpop
              have hCsub := capLabelCoh_step _ _ hFf hCohf hpop
              have hcont' : Config.run F1 (g1, Frame.appF u :: ctxNetEffect K σ1 τ1, Comp.lam M2) = Result.done v := hcont
              have hsub_run : ∃ Fs, Fs < F' ∧ Config.run Fs (g1, ctxNetEffect K σ1 τ1, Comp.subst u M2) = Result.done v := by
                cases F1 with
                | zero => simp [Config.run] at hcont'
                | succ F1' =>
                    have := Config.run_step F1' (g1, Frame.appF u :: ctxNetEffect K σ1 τ1, Comp.lam M2)
                      (by intro gg vv hc; simp at hc)
                    rw [hpop] at this; rw [this] at hcont'; exact ⟨F1', by omega, hcont'⟩
              obtain ⟨Fs, hFslt, hFs⟩ := hsub_run
              obtain ⟨ns, gs, σs, τs, κs, hsub⟩ :=
                ih Fs (by omega) (Comp.subst u M2) g1 σ1 τ1 κ1 (ctxNetEffect K σ1 τ1) v hCM' hTM' hKM' hCsub hFsub hFs
              refine ⟨max n ns + 1, gs, σs, τs, κs, ?_⟩
              rcases hsub with ⟨ts, hevs, hCs, hTs, hCCs, hCohs, hFsF, Fc, hFcle, hcs⟩ | ⟨nn2, oop2, vv2, hevs, hCs, hTs, hCCs, hCohs, hFsF, hNR2, Fc, hFcle, hcs⟩
              · left
                refine ⟨ts, ?_, ?_, ?_, ?_, ?_, ?_, Fc, by omega, ?_⟩
                · simp only [evalD]
                  rw [evalD_fuel_mono hev (Nat.le_max_left n ns)]
                  simp only [Option.bind_some]
                  exact evalD_fuel_mono hevs (Nat.le_max_right n ns)
                · rw [ctxNetEffect_ctxNetEffect] at hCs; exact hCs
                · rw [ctxNetEffect_ctxNetEffect] at hTs; exact hTs
                · rw [ctxNetEffect_ctxNetEffect] at hCCs; exact hCCs
                · rw [ctxNetEffect_ctxNetEffect] at hCohs; exact hCohs
                · rw [ctxNetEffect_ctxNetEffect] at hFsF; exact hFsF
                · rw [ctxNetEffect_ctxNetEffect] at hcs; exact hcs
              · right
                refine ⟨nn2, oop2, vv2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, Fc, by omega, ?_⟩
                · simp only [evalD]
                  rw [evalD_fuel_mono hev (Nat.le_max_left n ns)]
                  simp only [Option.bind_some]
                  exact evalD_fuel_mono hevs (Nat.le_max_right n ns)
                · rw [ctxNetEffect_ctxNetEffect] at hCs; exact hCs
                · rw [ctxNetEffect_ctxNetEffect] at hTs; exact hTs
                · rw [ctxNetEffect_ctxNetEffect] at hCCs; exact hCCs
                · rw [ctxNetEffect_ctxNetEffect] at hCohs; exact hCohs
                · rw [ctxNetEffect_ctxNetEffect] at hFsF; exact hFsF
                · rw [ctxNetEffect_ctxNetEffect] at hNR2; exact hNR2
                · rw [ctxNetEffect_ctxNetEffect] at hcs; exact hcs
          · -- M0 raised → evalD (app M0 u) propagates it. Strip the appF frame (frame-transparent).
            -- Identical to letC-raised, s/letF N/appF u, s/pop_letF/pop_appF. Mirror run_evalD:4804.
            have hns : ∀ h0 : Handler, Frame.appF u ≠ Frame.handleF nn h0 := by intro h0; simp
            have hcne : ctxNetEffect (Frame.appF u :: K) σ1 τ1 = Frame.appF u :: ctxNetEffect K σ1 τ1 :=
              ctxNetEffect_cons_nonframe σ1 τ1 (by intro n ℓ s; simp) (by intro n ℓ Θ; simp)
            have hCr' := CtxCorr_ctxNetEffect_nonframe (by intro ℓ s; simp) (by intro ℓ Θ; simp) hCf
            have hTr' := CtxTxnCorr_ctxNetEffect_nonframe (by intro ℓ s; simp) (by intro ℓ Θ; simp) hTf
            have hKr' : CCtxCorr κ1 (ctxNetEffect K σ1 τ1) := by
              rw [hcne] at hCCf; exact CCtxCorr_pop_noncustom (by intro n ℓ p cls; simp) hCCf
            rw [hcne] at hCohf hFf hNR
            have hCohr' := capLabelCoh_pop_appF hCohf
            have hFreshr' := freshCfg_pop_appF hFf
            have hNRr' := noResume_strip_cons hns hNR
            refine ⟨n+1, g1, σ1, τ1, κ1, Or.inr ⟨nn, oop, vv, ?_, hCr', hTr', hKr', hCohr', hFreshr', hNRr', F1, by omega, ?_⟩⟩
            · simp only [evalD]; rw [hev]; simp only [Option.bind_some]
            · have hidEq := idDispatch_cons_noResume (fr := Frame.appF u) (K := ctxNetEffect K σ1 τ1)
                (ℓ := labelOf (ctxNetEffect K σ1 τ1) nn) (op := oop) (v := vv) (by intro h0; simp) hNRr'
              have hlbl := labelOf_cons_ne (fr := Frame.appF u) (K := ctxNetEffect K σ1 τ1) (n := nn) hns
              rw [hcne, hlbl] at hcont
              simp only [dispatchRun] at hcont ⊢
              rw [run_perform_cons_eq hidEq F1] at hcont
              exact hcont
      | perform cap op u =>
          -- BASE case (where a raise originates). Dispatch by IDENTITY: evalD resolves the state/txn
          -- store at key n2 directly. STORE-HIT → term(ret …) same-K close (mirror run_evalD:4159).
          -- STORE-MISS → raised n2 op u, NoResume from the miss, dispatchRun re-performs (mirror 4562).
          cases cap with
          | vcap n2 ℓ2 =>
            -- ID-FIRST dispatch (route-B): resolve `n2` in σ → τ → κ → raise, mirroring evalD's own perform
            -- arm (AbstractMachine.lean:287-313). A store HIT that services yields term(ret …); a miss OR a
            -- kind-mismatch falls through to the next store; κ HIT + clause HIT inline-services (recurse);
            -- everything unserviced raises via `perform_miss_raises`. `hcu` = "custom store misses n2 OR its
            -- clause list misses op" (established by store-disjointness at a σ/τ hit, or directly at a κ miss).
            cases hg : σ.get? n2 with
            | some sv =>
                -- STATE frame at n2. get/put SERVICE; any other op RAISES (op the state frame can't handle).
                have hgc : (ctxStates K).get? n2 = some sv := by rw [← hCtx]; exact hg
                obtain ⟨Kᵢ, ℓ', Kₒ, hsp⟩ := splitAtId_of_ctxStates_get hFresh.2.2.1 hgc
                have hlab : ℓ' = ℓ2 := by
                  have := capLabelCoh_perform_label hCoh hsp; simpa [Handler.label] using this
                by_cases hop : op = "get"
                · subst hop
                  have hcr : Bang.CapResolves K n2 ℓ2 "get" :=
                    ⟨Kᵢ, Handler.state ℓ' sv, Kₒ, hsp, by subst hlab; simp [Bang.handlesOp]⟩
                  have hstep : Source.step (g, K, Comp.perform (Val.vcap n2 ℓ2) "get" u)
                      = some (g, K, Comp.ret sv) := by
                    simp only [Source.step, dispatch_state_get hFresh.2.2.1 hcr hgc, Option.map_some]
                  have hrun' : Config.run F' (g, K, Comp.ret sv) = Result.done v := by
                    have hs := Config.run_step F' (g, K, Comp.perform (Val.vcap n2 ℓ2) "get" u)
                      (by intro gg vv hc; simp at hc)
                    rw [hstep] at hs; simp only at hs; rw [← hs]; exact hrun
                  refine ⟨1, g, σ, τ, κ, Or.inl ⟨.ret sv, ?_, ?_, ?_, ?_, ?_, ?_, F', by omega, ?_⟩⟩
                  · show evalD 1 g σ τ κ (Comp.perform (Val.vcap n2 ℓ2) "get" u) = _
                    simp only [evalD, hg, if_true]
                  · rw [ctxNetEffect_self hCtx hTtx]; exact hCtx
                  · rw [ctxNetEffect_self hCtx hTtx]; exact hTtx
                  · rw [ctxNetEffect_self hCtx hTtx]; exact hCK
                  · rw [ctxNetEffect_self hCtx hTtx]; exact capLabelCoh_step _ _ hFresh hCoh hstep
                  · rw [ctxNetEffect_self hCtx hTtx]; exact freshCfg_step _ _ hFresh hstep
                  · rw [ctxNetEffect_self hCtx hTtx]; exact hrun'
                · by_cases hop2 : op = "put"
                  · subst hop2
                    have hcr : Bang.CapResolves K n2 ℓ2 "put" :=
                      ⟨Kᵢ, Handler.state ℓ' sv, Kₒ, hsp, by subst hlab; simp [Bang.handlesOp]⟩
                    have hstep : Source.step (g, K, Comp.perform (Val.vcap n2 ℓ2) "put" u)
                        = some (g, updateCtxStates K ((ctxStates K).put n2 u), Comp.ret .vunit) := by
                      simp only [Source.step, dispatch_state_put hFresh.2.2.1 (w := u) hcr hgc, Option.map_some]
                    have hcoh' := capLabelCoh_step _ _ hFresh hCoh hstep
                    have hfr' := freshCfg_step _ _ hFresh hstep
                    have hK' : CCtxCorr κ (ctxNetEffect K (σ.put n2 u) τ) := by
                      unfold CCtxCorr at hCK ⊢; rw [hCK, ctxCustoms_ctxNetEffect]
                    have hctxeq : ctxNetEffect K (σ.put n2 u) τ = updateCtxStates K ((ctxStates K).put n2 u) := by
                      rw [hCtx, hTtx]; unfold ctxNetEffect
                      rw [show ctxTxns K = ctxTxns (updateCtxStates K ((ctxStates K).put n2 u)) from
                        (ctxTxns_updateCtxStates K _).symm, updateCtxTxns_self_aux]
                    have hrun' : Config.run F' (g, updateCtxStates K ((ctxStates K).put n2 u), Comp.ret .vunit)
                        = Result.done v := by
                      have hs := Config.run_step F' (g, K, Comp.perform (Val.vcap n2 ℓ2) "put" u)
                        (by intro gg vv hc; simp at hc)
                      rw [hstep] at hs; simp only at hs; rw [← hs]; exact hrun
                    refine ⟨1, g, σ.put n2 u, τ, κ,
                      Or.inl ⟨.ret .vunit, ?_, ?_, ?_, ?_, ?_, ?_, F', by omega, ?_⟩⟩
                    · show evalD 1 g σ τ κ (Comp.perform (Val.vcap n2 ℓ2) "put" u) = _
                      simp only [evalD, hg, if_neg (by decide : ¬ ("put" = "get")), if_true]
                    · rw [hctxeq, hCtx]; simp only [CtxCorr]; rw [ctxStates_updateCtxStates_put hgc]
                    · rw [hctxeq, hTtx]; simp only [CtxTxnCorr]; rw [ctxTxns_updateCtxStates]
                    · rw [hctxeq] at hK' ⊢; exact hK'
                    · rw [hctxeq]; exact hcoh'
                    · rw [hctxeq]; exact hfr'
                    · rw [hctxeq]; exact hrun'
                  · -- op ∉ {get,put} ⇒ state frame raises. τ/κ miss n2 by StratFresh id-uniqueness.
                    exact perform_miss_raises hCtx hTtx hCK hCoh hFresh hrun
                      (Or.inr ⟨hop, hop2⟩) (Or.inl (ctxTxns_get_none_of_ctxStates_some hFresh.2.2.1 hgc))
                      (Or.inl (ctxCustoms_get_none_of_ctxStates_some hFresh.2.2.1 hgc))
                      (by show evalD 1 g σ τ κ _ = _
                          simp only [evalD, hg, if_neg hop, if_neg hop2])
            | none =>
            cases hgt : τ.get? n2 with
            | some Θ =>
                -- TRANSACTION frame at n2. stm ops SERVICE; else raise.
                have hgt' : (ctxTxns K).get? n2 = some Θ := by rw [← hTtx]; exact hgt
                by_cases hopt : isTxnOp op = true
                · obtain ⟨Kᵢ, ℓ', Kₒ, hsp⟩ := splitAtId_of_ctxTxns_get hFresh.2.2.1 hgt'
                  have hlab : ℓ' = ℓ2 := by
                    have := capLabelCoh_perform_label hCoh hsp; simpa [Handler.label] using this
                  have hcr : Bang.CapResolves K n2 ℓ2 op :=
                    ⟨Kᵢ, Handler.transaction ℓ' Θ, Kₒ, hsp, by
                      subst hlab; rcases isTxnOp_iff.mp hopt with rfl | rfl | rfl <;> simp [Bang.handlesOp]⟩
                  have hstep : Source.step (g, K, Comp.perform (Val.vcap n2 ℓ2) op u)
                      = some (g, updateCtxTxns K ((ctxTxns K).put n2 (txnService op u Θ).2),
                          Comp.ret (txnService op u Θ).1) := by
                    simp only [Source.step, dispatch_txn_service hFresh.2.2.1 hopt hcr hgt', Option.map_some]
                  have hcoh' := capLabelCoh_step _ _ hFresh hCoh hstep
                  have hfr' := freshCfg_step _ _ hFresh hstep
                  have hK' : CCtxCorr κ (ctxNetEffect K σ (τ.put n2 (txnService op u Θ).2)) := by
                    unfold CCtxCorr at hCK ⊢; rw [hCK, ctxCustoms_ctxNetEffect]
                  have hctxeq : ctxNetEffect K σ (τ.put n2 (txnService op u Θ).2)
                      = updateCtxTxns K ((ctxTxns K).put n2 (txnService op u Θ).2) := by
                    rw [hCtx, hTtx]; unfold ctxNetEffect; rw [updateCtxStates_self_aux]
                  have hrun' : Config.run F' (g, updateCtxTxns K ((ctxTxns K).put n2 (txnService op u Θ).2),
                      Comp.ret (txnService op u Θ).1) = Result.done v := by
                    have hs := Config.run_step F' (g, K, Comp.perform (Val.vcap n2 ℓ2) op u)
                      (by intro gg vv hc; simp at hc)
                    rw [hstep] at hs; simp only at hs; rw [← hs]; exact hrun
                  refine ⟨1, g, σ, τ.put n2 (txnService op u Θ).2, κ,
                    Or.inl ⟨.ret (txnService op u Θ).1, ?_, ?_, ?_, ?_, ?_, ?_, F', by omega, ?_⟩⟩
                  · show evalD 1 g σ τ κ (Comp.perform (Val.vcap n2 ℓ2) op u) = _
                    simp only [evalD, hg, hgt, hopt, if_true]
                  · rw [hctxeq, hCtx]; simp only [CtxCorr]; rw [ctxStates_updateCtxTxns]
                  · rw [hctxeq, hTtx]; simp only [CtxTxnCorr]; rw [ctxTxns_updateCtxTxns_service hgt']
                  · rw [hctxeq] at hK' ⊢; exact hK'
                  · rw [hctxeq]; exact hcoh'
                  · rw [hctxeq]; exact hfr'
                  · rw [hctxeq]; exact hrun'
                · -- op the txn frame can't handle ⇒ raise. σ misses (hg); κ misses n2 by id-uniqueness.
                  rw [Bool.not_eq_true] at hopt
                  exact perform_miss_raises hCtx hTtx hCK hCoh hFresh hrun
                    (Or.inl (by rw [← hCtx]; exact hg)) (Or.inr hopt)
                    (Or.inl (ctxCustoms_get_none_of_ctxTxns_some hFresh.2.2.1 hgt'))
                    (by show evalD 1 g σ τ κ _ = _
                        simp only [evalD, hg, hgt, hopt, Bool.false_eq_true, if_false])
            | none =>
            cases hck : κ.get? n2 with
            | none =>
                -- n2 in NO store ⇒ raise (escape or non-resumptive op).
                exact perform_miss_raises hCtx hTtx hCK hCoh hFresh hrun
                  (Or.inl (by rw [← hCtx]; exact hg)) (Or.inl (by rw [← hTtx]; exact hgt))
                  (Or.inl (by rw [← hCK]; exact hck))
                  (by show evalD 1 g σ τ κ _ = _
                      simp only [evalD, hg, hgt, hck])
            | some pcls =>
                obtain ⟨p, cls⟩ := pcls
                have hgc : (ctxCustoms K).get? n2 = some (p, cls) := by rw [← hCK]; exact hck
                cases hcl : cls.find? (·.1 == op) with
                | some clause =>
                    -- CUSTOM clause HIT: evalD INLINE-SERVICES the clause body against the LIVE store (κ, K
                    -- unchanged — the frame stays installed). The kernel `dispatch_custom` runs the SAME clause
                    -- body: (g,K,perform) → (g,K, subst p (subst (shift u) clause.2)). SAME-K single-reduction
                    -- bridge (mirror the forward sim's custom-perform arm, AbstractMachine.lean:5777).
                    obtain ⟨Kᵢ, ℓ', Kₒ, hsp⟩ := splitAtId_of_ctxCustoms_get hFresh.2.2.1 hgc
                    have hlab : ℓ' = ℓ2 := by
                      have := capLabelCoh_perform_label hCoh hsp; simpa [Handler.label] using this
                    have hho : Bang.handlesOp (Handler.custom ℓ' p cls) ℓ2 op = true := by
                      subst hlab
                      have hsome : ((cls.find? (·.1 == op)).isSome) = true := by rw [hcl]; rfl
                      simp only [Bang.handlesOp, hsome, Bool.and_true, decide_true]
                    have hcr : Bang.CapResolves K n2 ℓ2 op := ⟨Kᵢ, Handler.custom ℓ' p cls, Kₒ, hsp, hho⟩
                    have hstep : Source.step (g, K, Comp.perform (Val.vcap n2 ℓ2) op u)
                        = some (g, K, Comp.subst p (Comp.subst (Val.shift u) clause.2)) := by
                      simp only [Source.step, dispatch_custom hFresh.2.2.1 hcr hgc hcl, Option.map_some]
                    have hrun' : Config.run F' (g, K, Comp.subst p (Comp.subst (Val.shift u) clause.2))
                        = Result.done v := by
                      have hs := Config.run_step F' (g, K, Comp.perform (Val.vcap n2 ℓ2) op u)
                        (by intro gg vv hc; simp at hc)
                      rw [hstep] at hs; simp only at hs; rw [← hs]; exact hrun
                    refine completesTo_reduce ?_ hstep
                      (ih F' (by omega) (Comp.subst p (Comp.subst (Val.shift u) clause.2)) g σ τ κ K v
                        hCtx hTtx hCK (capLabelCoh_step _ _ hFresh hCoh hstep)
                        (freshCfg_step _ _ hFresh hstep) hrun')
                    -- evalD (f+1) (perform) = evalD f (subst body): the κ-clause-hit recurses at f.
                    intro f
                    show evalD (f+1) g σ τ κ (Comp.perform (Val.vcap n2 ℓ2) op u) = _
                    simp only [evalD, hg, hgt, hck, hcl]
                | none =>
                    -- CUSTOM clause MISS: op unserviced by this custom frame ⇒ raise. σ/τ miss (hg/hgt);
                    -- κ hits but the clause list misses op ⇒ `hcu`'s clause-miss disjunct.
                    exact perform_miss_raises hCtx hTtx hCK hCoh hFresh hrun
                      (Or.inl (by rw [← hCtx]; exact hg)) (Or.inl (by rw [← hTtx]; exact hgt))
                      (Or.inr (by intro p' cl' he; rw [hgc] at he; cases he; exact hcl))
                      (by show evalD 1 g σ τ κ _ = _
                          simp only [evalD, hg, hgt, hck, hcl])
          | _ =>
              -- non-cap perform: evalD = none, so Config.run is stuck ≠ done (absurd).
              exfalso; cases F' <;> simp_all [Config.run, Source.step]
      | handle h0 M0 =>
          -- MIRROR run_evalD handle arms (state 4268 / throws 4328 / txn 4417). Mint id:=g, install the
          -- handleF g h0 frame, run the substituted body via IH; compose the whole-handle evalD via the
          -- ported U5bPort.*_composes lemmas. The fuel IH lands on `subst (vcap g h.label) M0` directly
          -- (the de-risk's core: mint+subst absorbed by the fuel IH, no congruence).
          cases h0 with
          | custom ℓ0 p0 cls0 =>
              -- ADR-0085 Stage 4 (the #62 Slice-2 headline): install a custom frame. MINT id := g, PUSH
              -- (id ↦ (p0,cls0)) on κ, run subst body at g+1; κ POPS on return (CCtxCorr_pop_custom). The
              -- converse mirror of run_evalD's custom handle arm (AbstractMachine.lean:5808) — same install/
              -- pop, composed through `handle_custom_composes`/`handle_custom_forward`. σ/τ pass through.
              have hmint : Source.step (g, K, Comp.handle (Handler.custom ℓ0 p0 cls0) M0)
                  = some (g+1, Frame.handleF g (Handler.custom ℓ0 p0 cls0) :: K, Comp.subst (Val.vcap g ℓ0) M0) := rfl
              have hCinstall : CtxCorr σ (Frame.handleF g (Handler.custom ℓ0 p0 cls0) :: K) :=
                CtxCorr_cons_nonstate (by intro n ℓ s; simp) hCtx
              have hTinstall : CtxTxnCorr τ (Frame.handleF g (Handler.custom ℓ0 p0 cls0) :: K) :=
                CtxTxnCorr_cons_nontxn (by intro n ℓ Θ; simp) hTtx
              have hKinstall : CCtxCorr (κ.push g p0 cls0) (Frame.handleF g (Handler.custom ℓ0 p0 cls0) :: K) :=
                CCtxCorr_install hCK
              have hCohInstall := capLabelCoh_step _ _ hFresh hCoh hmint
              have hFreshInstall := freshCfg_step _ _ hFresh hmint
              have hrun' : Config.run F' (g+1, Frame.handleF g (Handler.custom ℓ0 p0 cls0) :: K,
                  Comp.subst (Val.vcap g ℓ0) M0) = Result.done v := by
                have hs := Config.run_step F' (g, K, Comp.handle (Handler.custom ℓ0 p0 cls0) M0)
                  (by intro gg vv hc; simp at hc)
                rw [hmint] at hs; simp only at hs; rw [← hs]; exact hrun
              obtain ⟨n, g1, σ1, τ1, κ1, hbody⟩ := ih F' (by omega) (Comp.subst (Val.vcap g ℓ0) M0) (g+1)
                σ τ (κ.push g p0 cls0) (Frame.handleF g (Handler.custom ℓ0 p0 cls0) :: K) v
                hCinstall hTinstall hKinstall hCohInstall hFreshInstall hrun'
              rcases hbody with ⟨t, hev, hCf, hTf, hCCf, hCohf, hFf, F1, hF1le, hcont⟩ | ⟨nn, oop, vv, hev, hCf, hTf, hCCf, hCohf, hFf, hNR, F1, hF1le, hcont⟩
              · -- body terminates: t = ret v0 (evalD_term_shape; lam under handleF is stuck).
                rcases evalD_term_shape _ _ _ _ _ _ _ _ _ _ _ hev with ⟨v0, rfl⟩ | ⟨M2, rfl⟩
                · -- POP the custom frame: whole handle → term(ret v0), κ1.tail. Compose via handle_custom_composes.
                  obtain ⟨⟨hCpop, hTpop⟩, hnetEq⟩ := CtxCorr_ctxNetEffect_pop_custom hCf hTf
                  have hKpop : CCtxCorr κ1.tail (ctxNetEffect K σ1 τ1) := by
                    rw [hnetEq] at hCCf; exact CCtxCorr_pop_custom hCCf
                  rw [hnetEq] at hCohf hFf hcont
                  have hunmark : Source.step (g1, Frame.handleF g (Handler.custom ℓ0 p0 cls0) :: ctxNetEffect K σ1 τ1,
                      Comp.ret v0) = some (g1, ctxNetEffect K σ1 τ1, Comp.ret v0) := rfl
                  have hCohPop := capLabelCoh_step _ _ hFf hCohf hunmark
                  have hFreshPop := freshCfg_step _ _ hFf hunmark
                  have hcont'' : ∃ Fs, Fs < F' ∧ Config.run Fs (g1, ctxNetEffect K σ1 τ1, Comp.ret v0)
                      = Result.done v := by
                    cases F1 with
                    | zero => simp [Config.run] at hcont
                    | succ F1' =>
                        have := Config.run_step F1' (g1, Frame.handleF g (Handler.custom ℓ0 p0 cls0) :: ctxNetEffect K σ1 τ1,
                          Comp.ret v0) (by intro gg vv hc; simp at hc)
                        rw [hunmark] at this; rw [this] at hcont; exact ⟨F1', by omega, hcont⟩
                  obtain ⟨Fs, hFslt, hFs⟩ := hcont''
                  refine ⟨n+1, g1, σ1, τ1, κ1.tail, Or.inl ⟨.ret v0, ?_, hCpop, hTpop, hKpop, hCohPop, hFreshPop, Fs, by omega, hFs⟩⟩
                  exact handle_custom_composes n g σ τ κ ℓ0 p0 cls0 M0 v0 g1 σ1 τ1 κ1 hev
                · -- lam under handleF-custom (UNMARK expects ret): stuck ⟹ hcont-absurd.
                  exfalso
                  obtain ⟨⟨_, _⟩, hnetEq⟩ := CtxCorr_ctxNetEffect_pop_custom hCf hTf
                  rw [hnetEq] at hcont
                  cases F1 with
                  | zero => simp [Config.run] at hcont
                  | succ F1' =>
                      rw [Config.run_step F1' _ (by intro gg vv hc; simp at hc)] at hcont
                      simp [Source.step, Config.run] at hcont
              · -- body raises → custom FORWARDS it (pop κ1.tail), strip the handleF-g frame. Mirror the state
                -- forward arm; custom never catches a raise (only throws does), so this is pure propagation.
                obtain ⟨⟨hCpop, hTpop⟩, hnetEq⟩ := CtxCorr_ctxNetEffect_pop_custom hCf hTf
                have hKpop : CCtxCorr κ1.tail (ctxNetEffect K σ1 τ1) := by
                  rw [hnetEq] at hCCf; exact CCtxCorr_pop_custom hCCf
                rw [hnetEq] at hCohf hFf hNR
                have hcbpop : Bang.Model.CapsBelow g (ctxNetEffect K σ1 τ1) :=
                  CapsBelow_ctxNetEffect _ _ hFresh.1
                have hCohr' := capLabelCoh_pop_handleF hcbpop hCohf
                have hFreshr' := freshCfg_pop_handleF hFf
                have hNRr' : NoResume (ctxNetEffect K σ1 τ1) nn oop := by
                  by_cases hℓg : nn = g
                  · subst hℓg; intro Kᵢ h Kₒ hsp
                    exact absurd hsp (by rw [splitAtId_none_of_capsBelow hcbpop]; simp)
                  · exact noResume_strip_cons (by intro h0 he; exact hℓg ((Frame.handleF.inj he).1.symm)) hNR
                have hhof : nn = g → Bang.handlesOp (Handler.custom ℓ0 p0 cls0)
                    (Handler.label (Handler.custom ℓ0 p0 cls0)) oop = false := by
                  intro hgl; subst hgl
                  rcases hNR [] (Handler.custom ℓ0 p0 cls0) (ctxNetEffect K σ1 τ1)
                    (by simp [Bang.splitAtId]) with hf | ⟨_, he⟩
                  · exact hf
                  · exact absurd he (by simp)
                refine ⟨n+1, g1, σ1, τ1, κ1.tail, Or.inr ⟨nn, oop, vv, ?_, hCpop, hTpop, hKpop, hCohr', hFreshr', hNRr', F1, by omega, ?_⟩⟩
                · exact handle_custom_forward n g σ τ κ ℓ0 p0 cls0 M0 nn oop vv g1 σ1 τ1 κ1 hev
                · rw [hnetEq] at hcont
                  simp only [dispatchRun] at hcont ⊢
                  rw [run_perform_pop_handleF hcbpop hNRr' hhof F1] at hcont
                  exact hcont
          | state ℓ0 s0 =>
              -- install handleF g (state ℓ0 s0), push σ.push g s0, run subst body at g+1. κ passes through
              -- unchanged (state is non-custom).
              have hmint : Source.step (g, K, Comp.handle (Handler.state ℓ0 s0) M0)
                  = some (g+1, Frame.handleF g (Handler.state ℓ0 s0) :: K, Comp.subst (Val.vcap g ℓ0) M0) := rfl
              have hCinstall : CtxCorr (σ.push g s0) (Frame.handleF g (Handler.state ℓ0 s0) :: K) :=
                CtxCorr_install hCtx
              have hTinstall : CtxTxnCorr τ (Frame.handleF g (Handler.state ℓ0 s0) :: K) :=
                CtxTxnCorr_cons_nontxn (by intro n ℓ Θ; simp) hTtx
              have hKinstall : CCtxCorr κ (Frame.handleF g (Handler.state ℓ0 s0) :: K) :=
                CCtxCorr_cons_noncustom (by intro n ℓ p cls; simp) hCK
              have hCohInstall := capLabelCoh_step _ _ hFresh hCoh hmint
              have hFreshInstall := freshCfg_step _ _ hFresh hmint
              have hrun' : Config.run F' (g+1, Frame.handleF g (Handler.state ℓ0 s0) :: K,
                  Comp.subst (Val.vcap g ℓ0) M0) = Result.done v := by
                have hs := Config.run_step F' (g, K, Comp.handle (Handler.state ℓ0 s0) M0)
                  (by intro gg vv hc; simp at hc)
                rw [hmint] at hs; simp only at hs; rw [← hs]; exact hrun
              obtain ⟨n, g1, σ1, τ1, κ1, hbody⟩ := ih F' (by omega) (Comp.subst (Val.vcap g ℓ0) M0) (g+1)
                (σ.push g s0) τ κ (Frame.handleF g (Handler.state ℓ0 s0) :: K) v
                hCinstall hTinstall hKinstall hCohInstall hFreshInstall hrun'
              rcases hbody with ⟨t, hev, hCf, hTf, hCCf, hCohf, hFf, F1, hF1le, hcont⟩ | ⟨nn, oop, vv, hev, hCf, hTf, hCCf, hCohf, hFf, hNR, F1, hF1le, hcont⟩
              · -- body terminates: t = ret v0 (evalD_term_shape; lam under handleF is stuck).
                rcases evalD_term_shape _ _ _ _ _ _ _ _ _ _ _ hev with ⟨v0, rfl⟩ | ⟨M2, rfl⟩
                · -- POP the state frame: whole handle → term(ret v0), σ1.tail. Compose via handle_state_composes.
                  obtain ⟨⟨hCpop, hTpop⟩, hnetEq⟩ := CtxCorr_ctxNetEffect_pop_state hCf hTf
                  have hKpop : CCtxCorr κ1 (ctxNetEffect K σ1.tail τ1) := by
                    unfold CCtxCorr at hCCf ⊢; rw [hCCf, hnetEq]
                    simp only [ctxCustoms, ctxCustoms_ctxNetEffect]
                  rw [hnetEq] at hCohf hFf hcont
                  have hunmark : Source.step (g1, Frame.handleF g
                      (Handler.state ℓ0 (σ1.headD (default, default)).2) :: ctxNetEffect K σ1.tail τ1,
                      Comp.ret v0) = some (g1, ctxNetEffect K σ1.tail τ1, Comp.ret v0) := rfl
                  have hCohPop := capLabelCoh_step _ _ hFf hCohf hunmark
                  have hFreshPop := freshCfg_step _ _ hFf hunmark
                  have hcont'' : ∃ Fs, Fs < F' ∧ Config.run Fs (g1, ctxNetEffect K σ1.tail τ1, Comp.ret v0)
                      = Result.done v := by
                    cases F1 with
                    | zero => simp [Config.run] at hcont
                    | succ F1' =>
                        have := Config.run_step F1' (g1, Frame.handleF g
                          (Handler.state ℓ0 (σ1.headD (default, default)).2) :: ctxNetEffect K σ1.tail τ1,
                          Comp.ret v0) (by intro gg vv hc; simp at hc)
                        rw [hunmark] at this; rw [this] at hcont; exact ⟨F1', by omega, hcont⟩
                  obtain ⟨Fs, hFslt, hFs⟩ := hcont''
                  refine ⟨n+1, g1, σ1.tail, τ1, κ1, Or.inl ⟨.ret v0, ?_, hCpop, hTpop, hKpop, hCohPop, hFreshPop, Fs, by omega, hFs⟩⟩
                  exact handle_state_composes n g σ τ κ ℓ0 s0 M0 v0 g1 σ1 τ1 κ1 hev
                · -- lam under handleF-state (UNMARK expects ret): stuck ⟹ hcont-absurd.
                  exfalso
                  obtain ⟨⟨_, _⟩, hnetEq⟩ := CtxCorr_ctxNetEffect_pop_state hCf hTf
                  rw [hnetEq] at hcont
                  cases F1 with
                  | zero => simp [Config.run] at hcont
                  | succ F1' =>
                      rw [Config.run_step F1' _ (by intro gg vv hc; simp at hc)] at hcont
                      simp [Source.step, Config.run] at hcont
              · -- body raises → state FORWARDS it (pop σ1.tail), strip the handleF-g frame. Mirror 4900.
                obtain ⟨⟨hCpop, hTpop⟩, hnetEq⟩ := CtxCorr_ctxNetEffect_pop_state hCf hTf
                have hKpop : CCtxCorr κ1 (ctxNetEffect K σ1.tail τ1) := by
                  unfold CCtxCorr at hCCf ⊢; rw [hCCf, hnetEq]
                  simp only [ctxCustoms, ctxCustoms_ctxNetEffect]
                rw [hnetEq] at hCohf hFf hNR
                have hcbpop : Bang.Model.CapsBelow g (ctxNetEffect K σ1.tail τ1) :=
                  CapsBelow_ctxNetEffect _ _ hFresh.1
                have hCohr' := capLabelCoh_pop_handleF hcbpop hCohf
                have hFreshr' := freshCfg_pop_handleF hFf
                have hNRr' : NoResume (ctxNetEffect K σ1.tail τ1) nn oop := by
                  by_cases hℓg : nn = g
                  · subst hℓg; intro Kᵢ h Kₒ hsp
                    exact absurd hsp (by rw [splitAtId_none_of_capsBelow hcbpop]; simp)
                  · exact noResume_strip_cons (by intro h0 he; exact hℓg ((Frame.handleF.inj he).1.symm)) hNR
                have hhof : nn = g → Bang.handlesOp (Handler.state ℓ0 (σ1.headD (default, default)).2)
                    (Handler.label (Handler.state ℓ0 (σ1.headD (default, default)).2)) oop = false := by
                  intro hgl; subst hgl
                  rcases hNR [] (Handler.state ℓ0 (σ1.headD (default, default)).2) (ctxNetEffect K σ1.tail τ1)
                    (by simp [Bang.splitAtId]) with hf | ⟨_, he⟩
                  · exact hf
                  · exact absurd he (by simp)
                refine ⟨n+1, g1, σ1.tail, τ1, κ1, Or.inr ⟨nn, oop, vv, ?_, hCpop, hTpop, hKpop, hCohr', hFreshr', hNRr', F1, by omega, ?_⟩⟩
                · exact handle_state_forward n g σ τ κ ℓ0 s0 M0 nn oop vv g1 σ1 τ1 κ1 hev
                · rw [hnetEq] at hcont
                  simp only [dispatchRun] at hcont ⊢
                  rw [run_perform_pop_handleF hcbpop hNRr' hhof F1] at hcont
                  exact hcont
          | throws ℓ0 =>
              -- throws: no store push. Normal return pops the frame. A raise to identity g op "raise" is
              -- CAUGHT (→ term(ret w), zero-shot abort); any other raise is FORWARDED. Mirror run_evalD:4948.
              have hmint : Source.step (g, K, Comp.handle (Handler.throws ℓ0) M0)
                  = some (g+1, Frame.handleF g (Handler.throws ℓ0) :: K, Comp.subst (Val.vcap g ℓ0) M0) := rfl
              have hCinstall : CtxCorr σ (Frame.handleF g (Handler.throws ℓ0) :: K) :=
                CtxCorr_cons_nonstate (by intro n ℓ s; simp) hCtx
              have hTinstall : CtxTxnCorr τ (Frame.handleF g (Handler.throws ℓ0) :: K) :=
                CtxTxnCorr_cons_nontxn (by intro n ℓ Θ; simp) hTtx
              have hKinstall : CCtxCorr κ (Frame.handleF g (Handler.throws ℓ0) :: K) :=
                CCtxCorr_cons_noncustom (by intro n ℓ p cls; simp) hCK
              have hCohInstall := capLabelCoh_step _ _ hFresh hCoh hmint
              have hFreshInstall := freshCfg_step _ _ hFresh hmint
              have hrun' : Config.run F' (g+1, Frame.handleF g (Handler.throws ℓ0) :: K,
                  Comp.subst (Val.vcap g ℓ0) M0) = Result.done v := by
                have hs := Config.run_step F' (g, K, Comp.handle (Handler.throws ℓ0) M0)
                  (by intro gg vv hc; simp at hc)
                rw [hmint] at hs; simp only at hs; rw [← hs]; exact hrun
              obtain ⟨n, g1, σ1, τ1, κ1, hbody⟩ := ih F' (by omega) (Comp.subst (Val.vcap g ℓ0) M0) (g+1)
                σ τ κ (Frame.handleF g (Handler.throws ℓ0) :: K) v
                hCinstall hTinstall hKinstall hCohInstall hFreshInstall hrun'
              rcases hbody with ⟨t, hev, hCf, hTf, hCCf, hCohf, hFf, F1, hF1le, hcont⟩ | ⟨nn, oop, vv, hev, hCf, hTf, hCCf, hCohf, hFf, hNR, F1, hF1le, hcont⟩
              · -- body normal return: pop the throws frame → term(ret v0). Stores pass through.
                rcases evalD_term_shape _ _ _ _ _ _ _ _ _ _ _ hev with ⟨v0, rfl⟩ | ⟨M2, rfl⟩
                · obtain ⟨⟨hCpop, hTpop⟩, hnetEq⟩ := CtxCorr_ctxNetEffect_pop_throws hCf hTf
                  have hKpop : CCtxCorr κ1 (ctxNetEffect K σ1 τ1) := by
                    unfold CCtxCorr at hCCf ⊢; rw [hCCf, hnetEq]
                    simp only [ctxCustoms, ctxCustoms_ctxNetEffect]
                  rw [hnetEq] at hCohf hFf hcont
                  have hunmark : Source.step (g1, Frame.handleF g (Handler.throws ℓ0) :: ctxNetEffect K σ1 τ1,
                      Comp.ret v0) = some (g1, ctxNetEffect K σ1 τ1, Comp.ret v0) := rfl
                  have hCohPop := capLabelCoh_step _ _ hFf hCohf hunmark
                  have hFreshPop := freshCfg_step _ _ hFf hunmark
                  have hcont'' : ∃ Fs, Fs < F' ∧ Config.run Fs (g1, ctxNetEffect K σ1 τ1, Comp.ret v0)
                      = Result.done v := by
                    cases F1 with
                    | zero => simp [Config.run] at hcont
                    | succ F1' =>
                        have := Config.run_step F1' (g1, Frame.handleF g (Handler.throws ℓ0) :: ctxNetEffect K σ1 τ1,
                          Comp.ret v0) (by intro gg vv hc; simp at hc)
                        rw [hunmark] at this; rw [this] at hcont; exact ⟨F1', by omega, hcont⟩
                  obtain ⟨Fs, hFslt, hFs⟩ := hcont''
                  refine ⟨n+1, g1, σ1, τ1, κ1, Or.inl ⟨.ret v0, ?_, hCpop, hTpop, hKpop, hCohPop, hFreshPop, Fs, by omega, hFs⟩⟩
                  exact handle_throws_normal_composes n g σ τ κ ℓ0 M0 v0 g1 σ1 τ1 κ1 hev
                · exfalso
                  obtain ⟨⟨_, _⟩, hnetEq⟩ := CtxCorr_ctxNetEffect_pop_throws hCf hTf
                  rw [hnetEq] at hcont
                  cases F1 with
                  | zero => simp [Config.run] at hcont
                  | succ F1' =>
                      rw [Config.run_step F1' _ (by intro gg vv hc; simp at hc)] at hcont
                      simp [Source.step, Config.run] at hcont
              · -- body raised: CAUGHT (nn=g ∧ oop="raise") → term(ret vv); else FORWARDED → raised.
                by_cases hk : nn = g ∧ oop = "raise"
                · obtain ⟨hng, hno⟩ := hk; subst nn; subst oop
                  -- CAUGHT: zero-shot abort to term(ret vv), stores kept (σ1/τ1). Continuation = the
                  -- kernel's own abort step (perform (vcap g ℓ0) "raise" vv over the throws frame → ret vv).
                  obtain ⟨⟨hCpop, hTpop⟩, hnetEq⟩ := CtxCorr_ctxNetEffect_pop_throws hCf hTf
                  rw [hnetEq] at hCohf hFf hcont hNR
                  have hsp : Bang.splitAtId (Frame.handleF g (Handler.throws ℓ0) :: ctxNetEffect K σ1 τ1) g
                      = some ([], Handler.throws ℓ0, ctxNetEffect K σ1 τ1) := by simp [Bang.splitAtId]
                  have hho : Bang.handlesOp (Handler.throws ℓ0) ℓ0 "raise" = true := by simp [Bang.handlesOp]
                  have hid : Bang.idDispatch (Frame.handleF g (Handler.throws ℓ0) :: ctxNetEffect K σ1 τ1)
                      g ℓ0 "raise" vv = some (ctxNetEffect K σ1 τ1, Comp.ret vv) := by
                    simp only [Bang.idDispatch, hsp, Option.bind_some, hho, if_true, Bang.dispatchOn]
                  have hstep_perf : Source.step (g1, Frame.handleF g (Handler.throws ℓ0) :: ctxNetEffect K σ1 τ1,
                      Comp.perform (Val.vcap g ℓ0) "raise" vv) = some (g1, ctxNetEffect K σ1 τ1, Comp.ret vv) := by
                    simp only [Source.step, hid, Option.map_some]
                  have hlabel : labelOf (Frame.handleF g (Handler.throws ℓ0) :: ctxNetEffect K σ1 τ1) g = ℓ0 := by
                    simp only [labelOf, hsp, Option.map_some, Option.getD_some, Handler.label]
                  -- hcont is dispatchRun over the throws-installed context; it aborts to ret vv then runs.
                  have hcont' : ∃ Fs, Fs < F' ∧ Config.run Fs (g1, ctxNetEffect K σ1 τ1, Comp.ret vv)
                      = Result.done v := by
                    simp only [dispatchRun, hlabel] at hcont
                    cases F1 with
                    | zero => simp [Config.run] at hcont
                    | succ F1' =>
                        rw [Config.run_step F1' _ (by intro gg vv2 hc; simp at hc), hstep_perf] at hcont
                        exact ⟨F1', by omega, hcont⟩
                  obtain ⟨Fs, hFslt, hFs⟩ := hcont'
                  -- pop the throws frame's coherence to the outer context (UNMARK-style, ret focus).
                  have hunmark : Source.step (g1, Frame.handleF g (Handler.throws ℓ0) :: ctxNetEffect K σ1 τ1,
                      Comp.ret vv) = some (g1, ctxNetEffect K σ1 τ1, Comp.ret vv) := rfl
                  have hCohPop := capLabelCoh_step _ _ hFf hCohf hunmark
                  have hFreshPop := freshCfg_step _ _ hFf hunmark
                  have hKpop : CCtxCorr κ1 (ctxNetEffect K σ1 τ1) := by
                    unfold CCtxCorr at hCCf ⊢; rw [hCCf, hnetEq]
                    simp only [ctxCustoms, ctxCustoms_ctxNetEffect]
                  refine ⟨n+1, g1, σ1, τ1, κ1, Or.inl ⟨.ret vv, ?_, hCpop, hTpop, hKpop, hCohPop, hFreshPop, Fs, by omega, hFs⟩⟩
                  exact handle_throws_caught_composes n g σ τ κ ℓ0 M0 vv g1 σ1 τ1 κ1 hev
                · -- FORWARDED: raise to nn≠g or oop≠"raise"; propagate, strip the handleF-g frame.
                  obtain ⟨⟨hCpop, hTpop⟩, hnetEq⟩ := CtxCorr_ctxNetEffect_pop_throws hCf hTf
                  have hKpop : CCtxCorr κ1 (ctxNetEffect K σ1 τ1) := by
                    unfold CCtxCorr at hCCf ⊢; rw [hCCf, hnetEq]
                    simp only [ctxCustoms, ctxCustoms_ctxNetEffect]
                  rw [hnetEq] at hCohf hFf hNR
                  have hcbpop : Bang.Model.CapsBelow g (ctxNetEffect K σ1 τ1) :=
                    CapsBelow_ctxNetEffect _ _ hFresh.1
                  have hCohr' := capLabelCoh_pop_handleF hcbpop hCohf
                  have hFreshr' := freshCfg_pop_handleF hFf
                  have hNRr' : NoResume (ctxNetEffect K σ1 τ1) nn oop := by
                    by_cases hℓg : nn = g
                    · subst hℓg; intro Kᵢ h Kₒ hsp
                      exact absurd hsp (by rw [splitAtId_none_of_capsBelow hcbpop]; simp)
                    · exact noResume_strip_cons (by intro h0 he; exact hℓg ((Frame.handleF.inj he).1.symm)) hNR
                  have hhof : nn = g → Bang.handlesOp (Handler.throws ℓ0) (Handler.label (Handler.throws ℓ0)) oop = false := by
                    intro hgl
                    have hnr : oop ≠ "raise" := fun he => hk ⟨hgl, he⟩
                    simp [Handler.label, Bang.handlesOp, hnr]
                  refine ⟨n+1, g1, σ1, τ1, κ1, Or.inr ⟨nn, oop, vv, ?_, hCpop, hTpop, hKpop, hCohr', hFreshr', hNRr', F1, by omega, ?_⟩⟩
                  · exact handle_throws_forward_composes n g σ τ κ ℓ0 M0 nn oop vv g1 σ1 τ1 κ1 hk hev
                  · rw [hnetEq] at hcont
                    simp only [dispatchRun] at hcont ⊢
                    rw [run_perform_pop_handleF hcbpop hNRr' hhof F1] at hcont
                    exact hcont
          | transaction ℓ0 Θ =>
              -- txn: push τ.push g Θ, pop τ1.tail (free rollback). Mirror the state arm on the τ side. κ
              -- passes through unchanged (transaction is non-custom).
              have hmint : Source.step (g, K, Comp.handle (Handler.transaction ℓ0 Θ) M0)
                  = some (g+1, Frame.handleF g (Handler.transaction ℓ0 Θ) :: K, Comp.subst (Val.vcap g ℓ0) M0) := rfl
              have hCinstall : CtxCorr σ (Frame.handleF g (Handler.transaction ℓ0 Θ) :: K) :=
                CtxCorr_cons_nonstate (by intro n ℓ s; simp) hCtx
              have hTinstall : CtxTxnCorr (τ.push g Θ) (Frame.handleF g (Handler.transaction ℓ0 Θ) :: K) :=
                CtxTxnCorr_install hTtx
              have hKinstall : CCtxCorr κ (Frame.handleF g (Handler.transaction ℓ0 Θ) :: K) :=
                CCtxCorr_cons_noncustom (by intro n ℓ p cls; simp) hCK
              have hCohInstall := capLabelCoh_step _ _ hFresh hCoh hmint
              have hFreshInstall := freshCfg_step _ _ hFresh hmint
              have hrun' : Config.run F' (g+1, Frame.handleF g (Handler.transaction ℓ0 Θ) :: K,
                  Comp.subst (Val.vcap g ℓ0) M0) = Result.done v := by
                have hs := Config.run_step F' (g, K, Comp.handle (Handler.transaction ℓ0 Θ) M0)
                  (by intro gg vv hc; simp at hc)
                rw [hmint] at hs; simp only at hs; rw [← hs]; exact hrun
              obtain ⟨n, g1, σ1, τ1, κ1, hbody⟩ := ih F' (by omega) (Comp.subst (Val.vcap g ℓ0) M0) (g+1)
                σ (τ.push g Θ) κ (Frame.handleF g (Handler.transaction ℓ0 Θ) :: K) v
                hCinstall hTinstall hKinstall hCohInstall hFreshInstall hrun'
              rcases hbody with ⟨t, hev, hCf, hTf, hCCf, hCohf, hFf, F1, hF1le, hcont⟩ | ⟨nn, oop, vv, hev, hCf, hTf, hCCf, hCohf, hFf, hNR, F1, hF1le, hcont⟩
              · rcases evalD_term_shape _ _ _ _ _ _ _ _ _ _ _ hev with ⟨v0, rfl⟩ | ⟨M2, rfl⟩
                · obtain ⟨⟨hCpop, hTpop⟩, hnetEq⟩ := CtxCorr_ctxNetEffect_pop_txn hCf hTf
                  have hKpop : CCtxCorr κ1 (ctxNetEffect K σ1 τ1.tail) := by
                    unfold CCtxCorr at hCCf ⊢; rw [hCCf, hnetEq]
                    simp only [ctxCustoms, ctxCustoms_ctxNetEffect]
                  rw [hnetEq] at hCohf hFf hcont
                  have hunmark : Source.step (g1, Frame.handleF g
                      (Handler.transaction ℓ0 (τ1.headD (default, default)).2) :: ctxNetEffect K σ1 τ1.tail,
                      Comp.ret v0) = some (g1, ctxNetEffect K σ1 τ1.tail, Comp.ret v0) := rfl
                  have hCohPop := capLabelCoh_step _ _ hFf hCohf hunmark
                  have hFreshPop := freshCfg_step _ _ hFf hunmark
                  have hcont'' : ∃ Fs, Fs < F' ∧ Config.run Fs (g1, ctxNetEffect K σ1 τ1.tail, Comp.ret v0)
                      = Result.done v := by
                    cases F1 with
                    | zero => simp [Config.run] at hcont
                    | succ F1' =>
                        have := Config.run_step F1' (g1, Frame.handleF g
                          (Handler.transaction ℓ0 (τ1.headD (default, default)).2) :: ctxNetEffect K σ1 τ1.tail,
                          Comp.ret v0) (by intro gg vv hc; simp at hc)
                        rw [hunmark] at this; rw [this] at hcont; exact ⟨F1', by omega, hcont⟩
                  obtain ⟨Fs, hFslt, hFs⟩ := hcont''
                  refine ⟨n+1, g1, σ1, τ1.tail, κ1, Or.inl ⟨.ret v0, ?_, hCpop, hTpop, hKpop, hCohPop, hFreshPop, Fs, by omega, hFs⟩⟩
                  exact handle_txn_composes n g σ τ κ ℓ0 Θ M0 v0 g1 σ1 τ1 κ1 hev
                · exfalso
                  obtain ⟨⟨_, _⟩, hnetEq⟩ := CtxCorr_ctxNetEffect_pop_txn hCf hTf
                  rw [hnetEq] at hcont
                  cases F1 with
                  | zero => simp [Config.run] at hcont
                  | succ F1' =>
                      rw [Config.run_step F1' _ (by intro gg vv hc; simp at hc)] at hcont
                      simp [Source.step, Config.run] at hcont
              · obtain ⟨⟨hCpop, hTpop⟩, hnetEq⟩ := CtxCorr_ctxNetEffect_pop_txn hCf hTf
                have hKpop : CCtxCorr κ1 (ctxNetEffect K σ1 τ1.tail) := by
                  unfold CCtxCorr at hCCf ⊢; rw [hCCf, hnetEq]
                  simp only [ctxCustoms, ctxCustoms_ctxNetEffect]
                rw [hnetEq] at hCohf hFf hNR
                have hcbpop : Bang.Model.CapsBelow g (ctxNetEffect K σ1 τ1.tail) :=
                  CapsBelow_ctxNetEffect _ _ hFresh.1
                have hCohr' := capLabelCoh_pop_handleF hcbpop hCohf
                have hFreshr' := freshCfg_pop_handleF hFf
                have hNRr' : NoResume (ctxNetEffect K σ1 τ1.tail) nn oop := by
                  by_cases hℓg : nn = g
                  · subst hℓg; intro Kᵢ h Kₒ hsp
                    exact absurd hsp (by rw [splitAtId_none_of_capsBelow hcbpop]; simp)
                  · exact noResume_strip_cons (by intro h0 he; exact hℓg ((Frame.handleF.inj he).1.symm)) hNR
                have hhof : nn = g → Bang.handlesOp (Handler.transaction ℓ0 (τ1.headD (default, default)).2)
                    (Handler.label (Handler.transaction ℓ0 (τ1.headD (default, default)).2)) oop = false := by
                  intro hgl; subst hgl
                  rcases hNR [] (Handler.transaction ℓ0 (τ1.headD (default, default)).2) (ctxNetEffect K σ1 τ1.tail)
                    (by simp [Bang.splitAtId]) with hf | ⟨_, he⟩
                  · exact hf
                  · exact absurd he (by simp)
                refine ⟨n+1, g1, σ1, τ1.tail, κ1, Or.inr ⟨nn, oop, vv, ?_, hCpop, hTpop, hKpop, hCohr', hFreshr', hNRr', F1, by omega, ?_⟩⟩
                · exact handle_txn_forward n g σ τ κ ℓ0 Θ M0 nn oop vv g1 σ1 τ1 κ1 hev
                · rw [hnetEq] at hcont
                  simp only [dispatchRun] at hcont ⊢
                  rw [run_perform_pop_handleF hcbpop hNRr' hhof F1] at hcont
                  exact hcont
      | oom => exfalso; cases F' <;> simp_all [Config.run, Source.step]
      | wrong a => exfalso; cases F' <;> simp_all [Config.run, Source.step]
      | binop op a b =>
          cases a <;> cases b <;>
            first
            | (rename_i x y
               have hstep : Source.step (g, K, Comp.binop op (Val.vint x) (Val.vint y))
                   = some (g, K, Comp.ret (op.eval x y)) := rfl
               have hrun' : Config.run F' (g, K, Comp.ret (op.eval x y)) = Result.done v := by
                 have hs := Config.run_step F' (g, K, Comp.binop op (Val.vint x) (Val.vint y))
                   (by intro gg vv hc; simp at hc)
                 rw [hstep] at hs; simp only at hs; rw [← hs]; exact hrun
               refine ⟨1, g, σ, τ, κ, Or.inl ⟨.ret (op.eval x y), by simp [evalD], ?_, ?_, ?_, ?_, ?_, F', by omega, ?_⟩⟩
               · rw [ctxNetEffect_self hCtx hTtx]; exact hCtx
               · rw [ctxNetEffect_self hCtx hTtx]; exact hTtx
               · rw [ctxNetEffect_self hCtx hTtx]; exact hCK
               · rw [ctxNetEffect_self hCtx hTtx]; exact capLabelCoh_step _ _ hFresh hCoh hstep
               · rw [ctxNetEffect_self hCtx hTtx]; exact freshCfg_step _ _ hFresh hstep
               · rw [ctxNetEffect_self hCtx hTtx]; exact hrun')
            | (exfalso; cases F' <;> simp_all [Config.run, Source.step])

/-! ### Deriving the frozen `evalD_complete_gen` at K=[] (the consumer's only call, Wasm.lean:2156).
`plug [] c = c`, so the full spine at K=[] yields the frozen conclusion — MODULO two obligations that
are STATEMENT/DEFINITIONAL, not proof gaps (surfaced to the manager):

1. **`FreshCfg (0, [], c)`** unfolds to `∀ p ∈ capsC c, p.1 < 0`, i.e. `c` has NO capability literals.
   TRUE for the consumer (`c` = a compiled SOURCE program; caps only arise by minting during a run),
   but the FROZEN `evalD_complete_gen` statement (Wasm.lean:1970) carries NO such hypothesis. Either
   the statement needs a `capsC c = []` / well-formedness premise (FROZEN — manager/kernel call), or
   there is an upstream fact (Source.eval's `c` is cap-free) that should be threaded at the call site.

2. **term-vs-raised**: extracting the `.term (.ret v)` conclusion needs the RAISED disjunct ruled out
   at K=[] — a top-level raise under the EMPTY context escapes (`dispatchRun` on `[]` → escapedCap),
   contradicting `= done v`. Provable (needs a `dispatchRun_nil_ne_done` helper), left for the wiring.

The full spine `evalD_complete_gen_full` (above, sorry-free — the custom stage-1 sorry was
discharged; `#print axioms` is the gate, not this prose) is the deliverable; this
derivation is the thin adapter. Obligation (2) is discharged by the manager's ruling (option (a)):
the consumer's `c` is a compiled SOURCE program, hence cap-free — threaded as a `capsC c = []`
premise on the K=[] instance (the frozen `evalD_complete_gen` at Wasm.lean:1970 is the general form;
the consumer only calls it at K=[], and a cap-free source `c` is exactly what `Source.eval` feeds). -/

/-- A raise at the EMPTY context escapes: `dispatchRun` on `[]` performs `vcap nn ℓ` which resolves
NO frame (`splitAtId [] = none`), so `Source.step` is `none` and `Config.run` yields `escapedCap`
(never `done`). Rules out the RAISED disjunct at K=[] (obligation 3). -/
theorem dispatchRun_nil_ne_done (F g nn : Nat) (ℓ : Bang.EffectRow.Label) (op : Bang.OpId) (w v : Val) :
    dispatchRun F g nn [] ℓ op w ≠ Result.done v := by
  simp only [dispatchRun]
  cases F with
  | zero => simp [Config.run]
  | succ F' =>
      rw [Config.run_step F' _ (by intro gg vv hc; simp at hc)]
      have hstep : Source.step (g, ([] : Bang.EvalCtx), Comp.perform (Val.vcap nn ℓ) op w) = none := by
        simp [Source.step, Bang.idDispatch, Bang.splitAtId]
      rw [hstep]; simp

/-- The frozen `evalD_complete_gen` at K=[] for a cap-free source program (obligation 2 via option (a)).
`plug [] c = c`; the full spine at K=[] yields the term disjunct (the raised one escapes, obligation 3). -/
theorem evalD_complete_gen_nil (F : Nat) (c : Comp) (v : Val)
    (hcapfree : Bang.Model.capsC c = [])
    (hrun : Config.run F (0, [], c) = Result.done v) :
    ∃ n g', evalD n 0 [] [] [] c = some (.term (.ret v), g', [], [], []) := by
  have hCtx : CtxCorr [] ([] : Bang.EvalCtx) := rfl
  have hTtx : CtxTxnCorr [] ([] : Bang.EvalCtx) := rfl
  have hCoh : CapLabelCoh (0, ([] : Bang.EvalCtx), c) := by
    refine ⟨fun p hp => ?_, fun p hp => ?_⟩
    · rw [hcapfree] at hp; simp at hp
    · simp [Bang.Model.capsK] at hp
  have hFresh : FreshCfg (0, ([] : Bang.EvalCtx), c) := by
    refine ⟨trivial, fun p hp => ?_, trivial, fun p hp => ?_⟩
    · rw [hcapfree] at hp; simp at hp
    · simp [Bang.Model.capsK] at hp
  have hCK : CCtxCorr [] ([] : Bang.EvalCtx) := rfl
  obtain ⟨n, g', σ', τ', κ', hd⟩ :=
    evalD_complete_gen_full F c 0 [] [] [] [] v hCtx hTtx hCK hCoh hFresh hrun
  have hne : ctxNetEffect [] σ' τ' = [] := by simp only [ctxNetEffect, updateCtxStates, updateCtxTxns]
  rcases hd with ⟨t, hev, hCf, hTf, hCCf, _, _, F', _, hcont⟩ | ⟨nn, oop, vv, hev, _, _, _, _, _, _, F', _, hcont⟩
  · -- term disjunct. At K=[], ctxNetEffect [] σ' τ' = [], so CtxCorr/CtxTxnCorr/CCtxCorr force σ'=τ'=κ'=[].
    rw [hne] at hCf hTf hCCf hcont
    have hσ : σ' = [] := hCf
    have hτ : τ' = [] := hTf
    have hκ : κ' = [] := by unfold CCtxCorr at hCCf; rw [hCCf]; rfl
    subst hσ; subst hτ; subst hκ
    -- t is ret/lam; only `ret v0` can Config.run to `done` under []; and then v0 = v.
    rcases evalD_term_shape _ _ _ _ _ _ _ _ _ _ _ hev with ⟨v0, rfl⟩ | ⟨M2, rfl⟩
    · -- Config.run F' (g', [], ret v0) = done v ⇒ v0 = v (done arm reads the ret payload).
      have hv0 : v0 = v := by
        cases F' with
        | zero => simp [Config.run] at hcont
        | succ F'' => simp only [Config.run, Result.done.injEq] at hcont; exact hcont
      subst hv0; exact ⟨n, g', hev⟩
    · -- lam under []: Config.run is stuck (not a done shape), contradicting = done v.
      exfalso
      cases F' with
      | zero => simp [Config.run] at hcont
      | succ F'' =>
          rw [Config.run_step F'' _ (by intro gg vv hc; simp at hc)] at hcont
          simp [Source.step, Config.run] at hcont
  · -- raised disjunct at K=[]: dispatchRun on [] escapes, contradicting = done v (obligation 3).
    rw [hne] at hcont
    exact absurd hcont (dispatchRun_nil_ne_done F' g' nn (labelOf [] nn) oop vv v)

end -- @[expose] public section
end Bang.CalcVM
