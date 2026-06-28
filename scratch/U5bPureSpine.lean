import Bang.CalcVM

/-! # U5b pure-spine CORE (fast-iterate; transplant into Bang/Compile.lean)

Route-B re-key of the WALL-FREE pure spine: `evalD_mono`/`add`/`some_le`, `Sim`,
`Sim.letC`/`Sim.app`, the reduce-sims, and a PureCtx-restricted `evalD_plug_sim_pure`
(handleF VACUOUS — avoids the `Sim.handle` substitution wall) + pure transfer lemmas.
`PureCtxS` here is a stand-in for Compile's `PureCtx` (same handleF=False shape). -/

open Bang CalcVM

namespace U5bPure

/-- `evalD` fuel monotonicity (route-B: g threaded; outcome carries g'). -/
theorem evalD_mono : ∀ (f g : Nat) (σ : CalcVM.SStore) (τ : CalcVM.THeap) (c : Comp) r,
    CalcVM.evalD f g σ τ c = some r → CalcVM.evalD (f + 1) g σ τ c = some r := by
  intro f
  induction f with
  | zero => intro g σ τ c r h; simp [CalcVM.evalD] at h
  | succ f ih =>
    intro g σ τ c r h
    cases c with
    | ret v => simpa [CalcVM.evalD] using h
    | lam M => simpa [CalcVM.evalD] using h
    | force w =>
        cases w with
        | vthunk M => simp only [CalcVM.evalD] at h ⊢; exact ih g σ τ M r h
        | _ => simp [CalcVM.evalD] at h
    | letC M N =>
        simp only [CalcVM.evalD] at h ⊢
        cases hM : CalcVM.evalD f g σ τ M with
        | none => rw [hM] at h; simp at h
        | some oM =>
            rw [hM] at h; rw [ih g σ τ M oM hM]
            obtain ⟨out, g1, σ1, τ1⟩ := oM
            cases out with
            | term t =>
                cases t with
                | ret w => simp only [Option.bind_some] at h ⊢; exact ih g1 σ1 τ1 (Comp.subst w N) r h
                | _ => simp only [Option.bind_some] at h ⊢; exact h
            | raised n op w => simpa only [Option.bind_some] using h
    | app M v =>
        simp only [CalcVM.evalD] at h ⊢
        cases hM : CalcVM.evalD f g σ τ M with
        | none => rw [hM] at h; simp at h
        | some oM =>
            rw [hM] at h; rw [ih g σ τ M oM hM]
            obtain ⟨out, g1, σ1, τ1⟩ := oM
            cases out with
            | term t =>
                cases t with
                | lam N => simp only [Option.bind_some] at h ⊢; exact ih g1 σ1 τ1 (Comp.subst v N) r h
                | _ => simp only [Option.bind_some] at h ⊢; exact h
            | raised n op w => simpa only [Option.bind_some] using h
    | perform cap op v => cases cap <;> simpa [CalcVM.evalD] using h
    | handle hh M =>
        cases hh with
        | state ℓ s =>
            simp only [CalcVM.evalD, Handler.label] at h ⊢
            cases hM : CalcVM.evalD f (g+1) (σ.push g s) τ (Comp.subst (Val.vcap g ℓ) M) with
            | none => rw [hM] at h; simp at h
            | some oM =>
                rw [hM] at h; rw [ih (g+1) (σ.push g s) τ (Comp.subst (Val.vcap g ℓ) M) oM hM]
                obtain ⟨out, g1, σ1, τ1⟩ := oM
                cases out with
                | term t => cases t with
                  | ret w => simpa only [Option.bind_some] using h
                  | _ => simpa only [Option.bind_some] using h
                | raised n op' w => simpa only [Option.bind_some] using h
        | transaction ℓ Θ =>
            simp only [CalcVM.evalD, Handler.label] at h ⊢
            cases hM : CalcVM.evalD f (g+1) σ (τ.push g Θ) (Comp.subst (Val.vcap g ℓ) M) with
            | none => rw [hM] at h; simp at h
            | some oM =>
                rw [hM] at h; rw [ih (g+1) σ (τ.push g Θ) (Comp.subst (Val.vcap g ℓ) M) oM hM]
                obtain ⟨out, g1, σ1, τ1⟩ := oM
                cases out with
                | term t => cases t with
                  | ret w => simpa only [Option.bind_some] using h
                  | _ => simpa only [Option.bind_some] using h
                | raised n op' w => simpa only [Option.bind_some] using h
        | throws ℓ0 =>
            simp only [CalcVM.evalD, Handler.label] at h ⊢
            cases hM : CalcVM.evalD f (g+1) σ τ (Comp.subst (Val.vcap g ℓ0) M) with
            | none => rw [hM] at h; simp at h
            | some oM =>
                rw [hM] at h; rw [ih (g+1) σ τ (Comp.subst (Val.vcap g ℓ0) M) oM hM]
                obtain ⟨out, g1, σ1, τ1⟩ := oM
                cases out with
                | term t => cases t with
                  | ret w => simpa only [Option.bind_some] using h
                  | _ => simpa only [Option.bind_some] using h
                | raised n op' w => simpa only [Option.bind_some] using h
    | case w N₁ N₂ =>
        cases w <;> simp only [CalcVM.evalD] at h ⊢ <;> first
          | exact ih _ _ _ _ r h
          | (exact h)
    | split w N =>
        cases w <;> simp only [CalcVM.evalD] at h ⊢ <;> first
          | exact ih _ _ _ _ r h
          | (exact h)
    | unfold w =>
        cases w <;> simp only [CalcVM.evalD] at h ⊢ <;> exact h
    | oom => simp [CalcVM.evalD] at h
    | wrong s => simp [CalcVM.evalD] at h

theorem evalD_add (k : Nat) : ∀ (f g : Nat) (σ : CalcVM.SStore) (τ : CalcVM.THeap) (c : Comp) r,
    CalcVM.evalD f g σ τ c = some r → CalcVM.evalD (f + k) g σ τ c = some r := by
  induction k with
  | zero => intro f g σ τ c r h; simpa using h
  | succ k ih =>
    intro f g σ τ c r h
    rw [show f + (k + 1) = (f + k) + 1 by omega]
    exact evalD_mono (f + k) g σ τ c r (ih f g σ τ c r h)

theorem evalD_some_le {f g0 : Nat} {g : Nat} {σ : CalcVM.SStore} {τ : CalcVM.THeap} {c : Comp} {r : _}
    (hfg : f ≤ g0) (h : CalcVM.evalD f g σ τ c = some r) :
    CalcVM.evalD g0 g σ τ c = some r := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hfg
  exact evalD_add k f g σ τ c r h

/-- Route-B `Sim`: threads the global counter `g`; outcome carries `(Outcome × Nat × SStore × THeap)`. -/
def Sim (cx cy : Comp) : Prop :=
  ∀ g σ τ b r, CalcVM.evalD b g σ τ cy = some r → ∃ a, CalcVM.evalD a g σ τ cx = some r

theorem Sim.letC {cx cy : Comp} (h : Sim cx cy) (N : Comp) : Sim (.letC cx N) (.letC cy N) := by
  intro g σ τ b r hb
  cases b with
  | zero => simp [CalcVM.evalD] at hb
  | succ b =>
      simp only [CalcVM.evalD] at hb
      cases hy : CalcVM.evalD b g σ τ cy with
      | none => rw [hy] at hb; simp at hb
      | some oy =>
          rw [hy] at hb
          obtain ⟨a, ha⟩ := h g σ τ b oy hy
          obtain ⟨out, g1, σ1, τ1⟩ := oy
          cases out with
          | term t =>
              cases t with
              | ret w =>
                  simp only [Option.bind_some] at hb
                  refine ⟨(max a b) + 1, ?_⟩
                  simp only [CalcVM.evalD, evalD_some_le (Nat.le_max_left a b) ha, Option.bind_some]
                  exact evalD_some_le (Nat.le_max_right a b) hb
              | _ => simp at hb
          | raised n op w =>
              simp only [Option.bind_some] at hb
              refine ⟨a + 1, ?_⟩
              simp only [CalcVM.evalD, ha, Option.bind_some]
              exact hb

theorem Sim.app {cx cy : Comp} (h : Sim cx cy) (u : Bang.Val) : Sim (.app cx u) (.app cy u) := by
  intro g σ τ b r hb
  cases b with
  | zero => simp [CalcVM.evalD] at hb
  | succ b =>
      simp only [CalcVM.evalD] at hb
      cases hy : CalcVM.evalD b g σ τ cy with
      | none => rw [hy] at hb; simp at hb
      | some oy =>
          rw [hy] at hb
          obtain ⟨a, ha⟩ := h g σ τ b oy hy
          obtain ⟨out, g1, σ1, τ1⟩ := oy
          cases out with
          | term t =>
              cases t with
              | lam N =>
                  simp only [Option.bind_some] at hb
                  refine ⟨(max a b) + 1, ?_⟩
                  simp only [CalcVM.evalD, evalD_some_le (Nat.le_max_left a b) ha, Option.bind_some]
                  exact evalD_some_le (Nat.le_max_right a b) hb
              | _ => simp at hb
          | raised n op w =>
              simp only [Option.bind_some] at hb
              refine ⟨a + 1, ?_⟩
              simp only [CalcVM.evalD, ha, Option.bind_some]
              exact hb

theorem sim_letC_ret (w : Bang.Val) (N : Comp) : Sim (.letC (.ret w) N) (Comp.subst w N) := by
  intro g σ τ b r hb
  refine ⟨b + 2, ?_⟩
  simp only [CalcVM.evalD, Option.bind_some]
  exact evalD_some_le (by omega) hb

theorem sim_app_lam (u : Bang.Val) (M : Comp) : Sim (.app (.lam M) u) (Comp.subst u M) := by
  intro g σ τ b r hb
  refine ⟨b + 2, ?_⟩
  simp only [CalcVM.evalD, Option.bind_some]
  exact evalD_some_le (by omega) hb

theorem sim_force (M : Comp) : Sim (.force (.vthunk M)) M := by
  intro g σ τ b r hb
  exact ⟨b + 1, by simp only [CalcVM.evalD]; exact evalD_some_le (by omega) hb⟩

theorem sim_case_inl (v : Bang.Val) (N₁ N₂ : Comp) :
    Sim (.case (.inl v) N₁ N₂) (Comp.subst v N₁) := by
  intro g σ τ b r hb; exact ⟨b + 1, by simp only [CalcVM.evalD]; exact evalD_some_le (by omega) hb⟩
theorem sim_case_inr (v : Bang.Val) (N₁ N₂ : Comp) :
    Sim (.case (.inr v) N₁ N₂) (Comp.subst v N₂) := by
  intro g σ τ b r hb; exact ⟨b + 1, by simp only [CalcVM.evalD]; exact evalD_some_le (by omega) hb⟩
theorem sim_split (v u : Bang.Val) (N : Comp) :
    Sim (.split (.pair v u) N) (Comp.subst v (Comp.subst (Val.shift u) N)) := by
  intro g σ τ b r hb; exact ⟨b + 1, by simp only [CalcVM.evalD]; exact evalD_some_le (by omega) hb⟩

theorem sim_unfold (v : Bang.Val) : Sim (.unfold (.fold v)) (Comp.ret v) := by
  intro g σ τ b r hb
  cases b with
  | zero => simp [CalcVM.evalD] at hb
  | succ b =>
      simp only [CalcVM.evalD] at hb
      exact ⟨1, by simp only [CalcVM.evalD]; exact hb⟩

/-- Stand-in for Compile's `PureCtx` — only the handleF=False shape matters for the lift. -/
def PureCtxS : Bang.EvalCtx → Prop
  | [] => True
  | .letF _ :: K => PureCtxS K
  | .appF _ :: K => PureCtxS K
  | .handleF _ _ :: _ => False

/-- PureCtx-restricted plug-congruence: lifts a focus `Sim` through a PURE frame stack.
The `handleF` case is VACUOUS (PureCtxS forbids it) — this is precisely how the pure bridge
AVOIDS the `Sim.handle` substitution wall. `g` is threaded unchanged (no mint in pure K). -/
theorem evalD_plug_sim_pure : ∀ {K : Bang.EvalCtx} {cx cy : Comp}, PureCtxS K → Sim cx cy →
    ∀ {g n r}, CalcVM.evalD n g [] [] (plug K cy) = some r →
    ∃ m, CalcVM.evalD m g [] [] (plug K cx) = some r
  | [], cx, cy, _, h, g, n, r, hn => h _ _ _ n r (by simpa [plug] using hn)
  | .letF N :: K, cx, cy, hK, h, g, n, r, hn => by
      rw [plug_cons, Frame.wrapStep] at hn ⊢
      exact evalD_plug_sim_pure (by simpa only [PureCtxS] using hK) (h.letC N) hn
  | .appF u :: K, cx, cy, hK, h, g, n, r, hn => by
      rw [plug_cons, Frame.wrapStep] at hn ⊢
      exact evalD_plug_sim_pure (by simpa only [PureCtxS] using hK) (h.app u) hn
  | .handleF _ hh :: K, cx, cy, hK, h, g, n, r, hn => by
      simp only [PureCtxS] at hK

-- Pure transfer lemmas: the reduce-sims lifted through a PURE K. `g'` existential (pure ⇒ no mint,
-- but kept general for the consumer); stores pinned `[] []`.
theorem evalD_plug_letC_ret_pure {w' : Bang.Val} (K : Bang.EvalCtx) (hK : PureCtxS K)
    (w : Bang.Val) (N : Comp) (g g' n : Nat)
    (h : CalcVM.evalD n g [] [] (plug K (Comp.subst w N)) = some (.term (.ret w'), g', [], [])) :
    ∃ m, CalcVM.evalD m g [] [] (plug K (.letC (.ret w) N)) = some (.term (.ret w'), g', [], []) :=
  evalD_plug_sim_pure hK (sim_letC_ret w N) h

theorem evalD_plug_app_lam_pure {w' : Bang.Val} (K : Bang.EvalCtx) (hK : PureCtxS K)
    (u : Bang.Val) (M : Comp) (g g' n : Nat)
    (h : CalcVM.evalD n g [] [] (plug K (Comp.subst u M)) = some (.term (.ret w'), g', [], [])) :
    ∃ m, CalcVM.evalD m g [] [] (plug K (.app (.lam M) u)) = some (.term (.ret w'), g', [], []) :=
  evalD_plug_sim_pure hK (sim_app_lam u M) h

theorem evalD_plug_force_pure {w' : Bang.Val} (K : Bang.EvalCtx) (hK : PureCtxS K)
    (M : Comp) (g g' n : Nat)
    (h : CalcVM.evalD n g [] [] (plug K M) = some (.term (.ret w'), g', [], [])) :
    ∃ m, CalcVM.evalD m g [] [] (plug K (.force (.vthunk M))) = some (.term (.ret w'), g', [], []) :=
  evalD_plug_sim_pure hK (sim_force M) h

theorem evalD_plug_case_inl_pure {w' : Bang.Val} (K : Bang.EvalCtx) (hK : PureCtxS K)
    (v : Bang.Val) (N₁ N₂ : Comp) (g g' n : Nat)
    (h : CalcVM.evalD n g [] [] (plug K (Comp.subst v N₁)) = some (.term (.ret w'), g', [], [])) :
    ∃ m, CalcVM.evalD m g [] [] (plug K (.case (.inl v) N₁ N₂)) = some (.term (.ret w'), g', [], []) :=
  evalD_plug_sim_pure hK (sim_case_inl v N₁ N₂) h

theorem evalD_plug_case_inr_pure {w' : Bang.Val} (K : Bang.EvalCtx) (hK : PureCtxS K)
    (v : Bang.Val) (N₁ N₂ : Comp) (g g' n : Nat)
    (h : CalcVM.evalD n g [] [] (plug K (Comp.subst v N₂)) = some (.term (.ret w'), g', [], [])) :
    ∃ m, CalcVM.evalD m g [] [] (plug K (.case (.inr v) N₁ N₂)) = some (.term (.ret w'), g', [], []) :=
  evalD_plug_sim_pure hK (sim_case_inr v N₁ N₂) h

theorem evalD_plug_split_pure {w' : Bang.Val} (K : Bang.EvalCtx) (hK : PureCtxS K)
    (v u : Bang.Val) (N : Comp) (g g' n : Nat)
    (h : CalcVM.evalD n g [] [] (plug K (Comp.subst v (Comp.subst (Val.shift u) N))) = some (.term (.ret w'), g', [], [])) :
    ∃ m, CalcVM.evalD m g [] [] (plug K (.split (.pair v u) N)) = some (.term (.ret w'), g', [], []) :=
  evalD_plug_sim_pure hK (sim_split v u N) h

theorem evalD_plug_unfold_pure {w' : Bang.Val} (K : Bang.EvalCtx) (hK : PureCtxS K)
    (v : Bang.Val) (g g' n : Nat)
    (h : CalcVM.evalD n g [] [] (plug K (Comp.ret v)) = some (.term (.ret w'), g', [], [])) :
    ∃ m, CalcVM.evalD m g [] [] (plug K (.unfold (.fold v))) = some (.term (.ret w'), g', [], []) :=
  evalD_plug_sim_pure hK (sim_unfold v) h

end U5bPure
