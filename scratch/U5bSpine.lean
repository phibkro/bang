import Bang.Backend.AbstractMachine

/-! # U5b-handler — converse-of-run_evalD completeness spine (scratch).

Single strengthened statement, DISJUNCTIVE conclusion over evalD's two outcomes
(term / raised) — the converse unifies what run_evalD splits by hypothesis.
Strong induction on Source `Config.run` fuel F; case on focus M. -/

namespace Bang.CalcVM
open Bang (Val Comp Frame Config Result Handler)
open Bang.CapCoh (CapLabelCoh capLabelCoh_step capLabelCoh_perform_label)
open Bang.Model (FreshCfg freshCfg_step)

/-! ### Ported de-risk lemmas (U5bPort) — the handler-kind `*_composes` bridges (0-delta port).
The fuel IH on the SUBSTITUTED body composes through `evalD`'s handle clause to the whole-handle
node — for each handler kind. No substitution-closure of a black-box relation (the route-A wall). -/

theorem handle_state_composes
    (f g : Nat) (σ : SStore) (τ : THeap) (ℓ0 : Bang.EffectRow.Label) (s0 : Val) (M : Comp)
    (v0 : Val) (g' : Nat) (σ' : SStore) (τ' : THeap)
    (hbody : evalD f (g+1) (σ.push g s0) τ (Comp.subst (Val.vcap g ℓ0) M)
               = some (.term (.ret v0), g', σ', τ')) :
    evalD (f+1) g σ τ (Comp.handle (Handler.state ℓ0 s0) M)
               = some (.term (.ret v0), g', σ'.tail, τ') := by
  simp only [evalD, Handler.label, hbody, Option.bind_some]

theorem handle_txn_composes
    (f g : Nat) (σ : SStore) (τ : THeap) (ℓ0 : Bang.EffectRow.Label) (Θ : List Val) (M : Comp)
    (v0 : Val) (g' : Nat) (σ' : SStore) (τ' : THeap)
    (hbody : evalD f (g+1) σ (τ.push g Θ) (Comp.subst (Val.vcap g ℓ0) M)
               = some (.term (.ret v0), g', σ', τ')) :
    evalD (f+1) g σ τ (Comp.handle (Handler.transaction ℓ0 Θ) M)
               = some (.term (.ret v0), g', σ', τ'.tail) := by
  simp only [evalD, Handler.label, hbody, Option.bind_some]

theorem handle_throws_normal_composes
    (f g : Nat) (σ : SStore) (τ : THeap) (ℓ0 : Bang.EffectRow.Label) (M : Comp)
    (v0 : Val) (g' : Nat) (σ' : SStore) (τ' : THeap)
    (hbody : evalD f (g+1) σ τ (Comp.subst (Val.vcap g ℓ0) M)
               = some (.term (.ret v0), g', σ', τ')) :
    evalD (f+1) g σ τ (Comp.handle (Handler.throws ℓ0) M)
               = some (.term (.ret v0), g', σ', τ') := by
  simp only [evalD, Handler.label, hbody, Option.bind_some]

theorem handle_throws_caught_composes
    (f g : Nat) (σ : SStore) (τ : THeap) (ℓ0 : Bang.EffectRow.Label) (M : Comp)
    (w : Val) (g' : Nat) (σ' : SStore) (τ' : THeap)
    (hbody : evalD f (g+1) σ τ (Comp.subst (Val.vcap g ℓ0) M)
               = some (.raised g "raise" w, g', σ', τ')) :
    evalD (f+1) g σ τ (Comp.handle (Handler.throws ℓ0) M)
               = some (.term (.ret w), g', σ', τ') := by
  simp only [evalD, Handler.label, hbody, Option.bind_some, and_self, if_true]

theorem handle_throws_forward_composes
    (f g : Nat) (σ : SStore) (τ : THeap) (ℓ0 : Bang.EffectRow.Label) (M : Comp)
    (n : Nat) (op : Bang.OpId) (w : Val) (g' : Nat) (σ' : SStore) (τ' : THeap)
    (hne : ¬ (n = g ∧ op = "raise"))
    (hbody : evalD f (g+1) σ τ (Comp.subst (Val.vcap g ℓ0) M)
               = some (.raised n op w, g', σ', τ')) :
    evalD (f+1) g σ τ (Comp.handle (Handler.throws ℓ0) M)
               = some (.raised n op w, g', σ', τ') := by
  simp only [evalD, Handler.label, hbody, Option.bind_some, if_neg hne]

/-- Fuel monotonicity for `evalD` (the `evalD` analog of `exec_succ`/`exec_mono`): more fuel
never changes a `some`. Needed by the converse spine, which COMBINES two `evalD` sub-runs at
different fuels (e.g. letC binds M0 at `n`, subst-N at `ns`) — run_evalD never needs this because
it inducts on `evalD` fuel directly. Induction on the smaller fuel, `cases` on the focus `M`. -/
theorem evalD_succ : ∀ (f g : Nat) (σ : SStore) (τ : THeap) (M : Comp) (r : Outcome × Nat × SStore × THeap),
    evalD f g σ τ M = some r → evalD (f+1) g σ τ M = some r := by
  intro f
  induction f with
  | zero => intro g σ τ M r h; simp [evalD] at h
  | succ f ih =>
    intro g σ τ M r h
    cases M with
    | ret w => simpa [evalD] using h
    | lam M0 => simpa [evalD] using h
    | letC M0 N =>
        simp only [evalD] at h ⊢
        cases hM0 : evalD f g σ τ M0 with
        | none => rw [hM0] at h; simp at h
        | some p =>
            rw [hM0] at h; rw [ih _ _ _ _ _ hM0]
            obtain ⟨o, g1, σ1, τ1⟩ := p
            cases o with
            | term t => cases t with
              | ret v0 => simp only [Option.bind_some] at h ⊢; exact ih _ _ _ _ _ h
              | _ => simp only [Option.bind_some] at h ⊢; exact h
            | raised n op w => simp only [Option.bind_some] at h ⊢; exact h
    | force a =>
        cases a with
        | vthunk M0 => simp only [evalD] at h ⊢; exact ih _ _ _ _ _ h
        | _ => simp [evalD] at h ⊢ <;> exact h
    | app M0 u =>
        simp only [evalD] at h ⊢
        cases hM0 : evalD f g σ τ M0 with
        | none => rw [hM0] at h; simp at h
        | some p =>
            rw [hM0] at h; rw [ih _ _ _ _ _ hM0]
            obtain ⟨o, g1, σ1, τ1⟩ := p
            cases o with
            | term t => cases t with
              | lam N => simp only [Option.bind_some] at h ⊢; exact ih _ _ _ _ _ h
              | _ => simp only [Option.bind_some] at h ⊢; exact h
            | raised n op w => simp only [Option.bind_some] at h ⊢; exact h
    | perform cap op u =>
        -- perform is FUEL-AGNOSTIC (no recursion): the `f+1` and `f+2` clauses are byte-identical.
        cases cap with
        | vcap n ℓ => simp only [evalD] at h ⊢; exact h
        | _ => simp [evalD] at h ⊢ <;> exact h
    | handle h0 M0 =>
        cases h0 with
        | custom _ _ _ => simp [evalD] at h
        | state ℓ0 s0 =>
            simp only [evalD, Handler.label] at h ⊢
            cases hM0 : evalD f (g+1) (σ.push g s0) τ (Comp.subst (Val.vcap g ℓ0) M0) with
            | none => rw [hM0] at h; simp at h
            | some p =>
                rw [hM0] at h; rw [ih _ _ _ _ _ hM0]
                obtain ⟨o, g1, σ1, τ1⟩ := p
                cases o with
                | term t => cases t with
                  | ret v0 => simpa using h
                  | _ => simpa using h
                | raised n op w => simpa using h
        | transaction ℓ0 Θ =>
            simp only [evalD, Handler.label] at h ⊢
            cases hM0 : evalD f (g+1) σ (τ.push g Θ) (Comp.subst (Val.vcap g ℓ0) M0) with
            | none => rw [hM0] at h; simp at h
            | some p =>
                rw [hM0] at h; rw [ih _ _ _ _ _ hM0]
                obtain ⟨o, g1, σ1, τ1⟩ := p
                cases o with
                | term t => cases t with
                  | ret v0 => simpa using h
                  | _ => simpa using h
                | raised n op w => simpa using h
        | throws ℓ0 =>
            simp only [evalD, Handler.label] at h ⊢
            cases hM0 : evalD f (g+1) σ τ (Comp.subst (Val.vcap g ℓ0) M0) with
            | none => rw [hM0] at h; simp at h
            | some p =>
                rw [hM0] at h; rw [ih _ _ _ _ _ hM0]
                obtain ⟨o, g1, σ1, τ1⟩ := p
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
        | inl v => simp only [evalD] at h ⊢; exact ih _ _ _ _ _ h
        | inr v => simp only [evalD] at h ⊢; exact ih _ _ _ _ _ h
        | _ => simp [evalD] at h ⊢ <;> exact h
    | split a N =>
        cases a with
        | pair v w => simp only [evalD] at h ⊢; exact ih _ _ _ _ _ h
        | _ => simp [evalD] at h ⊢ <;> exact h
    | unfold a =>
        cases a with
        | fold v => simpa [evalD] using h
        | _ => simp [evalD] at h ⊢ <;> exact h
    | binop op a b =>
        cases a <;> cases b <;> (simp only [evalD] at h ⊢ <;> exact h)
    | oom => simp [evalD] at h
    | wrong a => simp [evalD] at h

theorem evalD_fuel_mono {f g : Nat} {σ : SStore} {τ : THeap} {M : Comp}
    {r : Outcome × Nat × SStore × THeap} {f2 : Nat}
    (h : evalD f g σ τ M = some r) (hle : f ≤ f2) : evalD f2 g σ τ M = some r := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hle
  clear hle
  induction k with
  | zero => simpa using h
  | succ k ih => rw [show f + (k+1) = (f + k) + 1 by omega]; exact evalD_succ _ _ _ _ _ _ ih

/-- `evalD`'s `.term` outcome is always a TERMINAL computation — `ret v` or `lam M0` (the two
values of CBPV). Every `evalD` clause that yields `.term t` yields one of these; the sequencing
clauses (`letC`/`app`) recurse. Needed by the converse's letC/app term arms to discharge the
non-terminal `t` cases that `cases t` would otherwise leave open. Induction on fuel, `cases` on `M`. -/
theorem evalD_term_shape : ∀ (f g : Nat) (σ : SStore) (τ : THeap) (M : Comp)
    (t : Comp) (g' : Nat) (σ' : SStore) (τ' : THeap),
    evalD f g σ τ M = some (.term t, g', σ', τ') →
    (∃ v, t = Comp.ret v) ∨ (∃ M0, t = Comp.lam M0) := by
  intro f
  induction f with
  | zero => intro g σ τ M t g' σ' τ' h; simp [evalD] at h
  | succ f ih =>
    intro g σ τ M t g' σ' τ' h
    cases M with
    | ret w => simp only [evalD, Option.some.injEq, Prod.mk.injEq, Outcome.term.injEq] at h
               exact Or.inl ⟨w, h.1.symm⟩
    | lam M0 => simp only [evalD, Option.some.injEq, Prod.mk.injEq, Outcome.term.injEq] at h
                exact Or.inr ⟨M0, h.1.symm⟩
    | letC M0 N =>
        simp only [evalD] at h
        cases hM0 : evalD f g σ τ M0 with
        | none => rw [hM0] at h; simp at h
        | some p =>
            rw [hM0] at h; obtain ⟨o, g1, σ1, τ1⟩ := p
            cases o with
            | term tt => cases tt with
              | ret v0 => simp only [Option.bind_some] at h; exact ih _ _ _ _ _ _ _ _ h
              | _ => simp [Option.bind_some] at h
            | raised n op w => simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
                               exact absurd h.1 (by simp)
    | force a =>
        cases a with
        | vthunk M0 => simp only [evalD] at h; exact ih _ _ _ _ _ _ _ _ h
        | _ => simp [evalD] at h
    | app M0 u =>
        simp only [evalD] at h
        cases hM0 : evalD f g σ τ M0 with
        | none => rw [hM0] at h; simp at h
        | some p =>
            rw [hM0] at h; obtain ⟨o, g1, σ1, τ1⟩ := p
            cases o with
            | term tt => cases tt with
              | lam N => simp only [Option.bind_some] at h; exact ih _ _ _ _ _ _ _ _ h
              | _ => simp [Option.bind_some] at h
            | raised n op w => simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
                               exact absurd h.1 (by simp)
    | perform cap op u =>
        cases cap with
        | vcap n ℓ =>
            -- perform's `.term` result (get/put/txn success) is always `ret`; failures are `.raised`.
            simp only [evalD] at h
            by_cases hg : op = "get"
            · rw [if_pos hg] at h
              cases hσ : σ.get? n with
              | some sv => rw [hσ] at h; simp only [Option.some.injEq, Prod.mk.injEq, Outcome.term.injEq] at h
                           exact Or.inl ⟨sv, h.1.symm⟩
              | none => rw [hσ] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; exact absurd h.1 (by simp)
            · by_cases hp : op = "put"
              · rw [if_neg hg, if_pos hp] at h
                cases hσ : σ.get? n with
                | some sv => rw [hσ] at h; simp only [Option.some.injEq, Prod.mk.injEq, Outcome.term.injEq] at h
                             exact Or.inl ⟨_, h.1.symm⟩
                | none => rw [hσ] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; exact absurd h.1 (by simp)
              · by_cases ht : isTxnOp op = true
                · rw [if_neg hg, if_neg hp, if_pos ht] at h
                  cases hτ : τ.get? n with
                  | some Θ => rw [hτ] at h; simp only [Option.some.injEq, Prod.mk.injEq, Outcome.term.injEq] at h
                              exact Or.inl ⟨_, h.1.symm⟩
                  | none => rw [hτ] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; exact absurd h.1 (by simp)
                · rw [Bool.not_eq_true] at ht
                  rw [if_neg hg, if_neg hp, if_neg (by rw [ht]; simp)] at h
                  simp only [Option.some.injEq, Prod.mk.injEq] at h
                  exact absurd h.1 (by simp)
        | _ => simp [evalD] at h
    | handle h0 M0 =>
        cases h0 with
        | custom _ _ _ => simp [evalD] at h
        | state ℓ0 s0 =>
            simp only [evalD, Handler.label] at h
            cases hM0 : evalD f (g+1) (σ.push g s0) τ (Comp.subst (Val.vcap g ℓ0) M0) with
            | none => rw [hM0] at h; simp at h
            | some p =>
                rw [hM0] at h; obtain ⟨o, g1, σ1, τ1⟩ := p
                cases o with
                | term tt => cases tt with
                  | ret v0 => simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq,
                                Outcome.term.injEq] at h; exact Or.inl ⟨v0, h.1.symm⟩
                  | _ => simp [Option.bind_some] at h
                | raised n op w => simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
                                   exact absurd h.1 (by simp)
        | transaction ℓ0 Θ =>
            simp only [evalD, Handler.label] at h
            cases hM0 : evalD f (g+1) σ (τ.push g Θ) (Comp.subst (Val.vcap g ℓ0) M0) with
            | none => rw [hM0] at h; simp at h
            | some p =>
                rw [hM0] at h; obtain ⟨o, g1, σ1, τ1⟩ := p
                cases o with
                | term tt => cases tt with
                  | ret v0 => simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq,
                                Outcome.term.injEq] at h; exact Or.inl ⟨v0, h.1.symm⟩
                  | _ => simp [Option.bind_some] at h
                | raised n op w => simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
                                   exact absurd h.1 (by simp)
        | throws ℓ0 =>
            simp only [evalD, Handler.label] at h
            cases hM0 : evalD f (g+1) σ τ (Comp.subst (Val.vcap g ℓ0) M0) with
            | none => rw [hM0] at h; simp at h
            | some p =>
                rw [hM0] at h; obtain ⟨o, g1, σ1, τ1⟩ := p
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
        | inl v => simp only [evalD] at h; exact ih _ _ _ _ _ _ _ _ h
        | inr v => simp only [evalD] at h; exact ih _ _ _ _ _ _ _ _ h
        | _ => simp [evalD] at h
    | split a N =>
        cases a with
        | pair v w => simp only [evalD] at h; exact ih _ _ _ _ _ _ _ _ h
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
def CompletesTo (F : Nat) (g : Nat) (σ : SStore) (τ : THeap) (M : Comp) (K : Bang.EvalCtx) (v : Val) : Prop :=
  ∃ n g' σ' τ',
    (∃ t, evalD n g σ τ M = some (.term t, g', σ', τ') ∧
      CtxCorr σ' (ctxNetEffect K σ' τ') ∧ CtxTxnCorr τ' (ctxNetEffect K σ' τ') ∧
      CapLabelCoh (g', ctxNetEffect K σ' τ', t) ∧ FreshCfg (g', ctxNetEffect K σ' τ', t) ∧
      ∃ F', F' ≤ F ∧ Config.run F' (g', ctxNetEffect K σ' τ', t) = Result.done v)
    ∨
    (∃ nn oop vv, evalD n g σ τ M = some (.raised nn oop vv, g', σ', τ') ∧
      CtxCorr σ' (ctxNetEffect K σ' τ') ∧ CtxTxnCorr τ' (ctxNetEffect K σ' τ') ∧
      CapLabelCoh (g', ctxNetEffect K σ' τ', Comp.ret vv) ∧
      FreshCfg (g', ctxNetEffect K σ' τ', Comp.ret vv) ∧
      NoResume (ctxNetEffect K σ' τ') nn oop ∧
      ∃ F', F' ≤ F ∧ dispatchRun F' g' nn (ctxNetEffect K σ' τ') (labelOf (ctxNetEffect K σ' τ') nn) oop vv
              = Result.done v)

/-- A SAME-`K` single-reduction bridge for `CompletesTo`: if `M` reduces to `M'` in ONE `evalD`
step (`evalD (f+1) g σ τ M = evalD f g σ τ M'` for all f) AND ONE matching `Source.step`
(`(g,K,M) → (g,K,M')`), then `CompletesTo` for `M'` lifts to `M`. Covers force/case/split/unfold
(the pure same-context reductions); the evalD-step-equality is discharged per-constructor by `rfl`. -/
theorem completesTo_reduce {F g : Nat} {σ : SStore} {τ : THeap} {M M' : Comp} {K : Bang.EvalCtx} {v : Val}
    (hevD : ∀ f, evalD (f+1) g σ τ M = evalD f g σ τ M')
    (hstep : Source.step (g, K, M) = some (g, K, M'))
    (hM' : CompletesTo F g σ τ M' K v) : CompletesTo (F+1) g σ τ M K v := by
  obtain ⟨n, g', σ', τ', hd⟩ := hM'
  refine ⟨n+1, g', σ', τ', ?_⟩
  rcases hd with ⟨t, hev, hCf, hTf, hCohf, hFf, F', hF'le, hcont⟩ | ⟨nn, oop, vv, hev, hCf, hTf, hCohf, hFf, hNR, F', hF'le, hcont⟩
  · exact Or.inl ⟨t, by rw [hevD]; exact hev, hCf, hTf, hCohf, hFf, F', by omega, hcont⟩
  · exact Or.inr ⟨nn, oop, vv, by rw [hevD]; exact hev, hCf, hTf, hCohf, hFf, hNR, F', by omega, hcont⟩

/-- The perform RAISE base case (converse of `run_evalD`'s `close` helper, AbstractMachine.lean:4573):
a `perform (vcap n2 ℓ2) op u` whose op resolves NO resumptive frame at identity `n2` (state-miss or
non-get/put; txn-miss or non-txn) yields `evalD → raised n2 op u` (stores unchanged), and its
`dispatchRun` continuation IS the kernel's own `Config.run` on the perform (label reconstructed by
`labelOf`, or irrelevant on escape). `NoResume` follows: any frame that resolves is throws (abort) or
fails the op. -/
theorem perform_miss_raises {F g : Nat} {σ : SStore} {τ : THeap} {K : Bang.EvalCtx}
    {n2 : Nat} {ℓ2 : Bang.EffectRow.Label} {op : Bang.OpId} {u v : Val}
    (hCtx : CtxCorr σ K) (hTtx : CtxTxnCorr τ K)
    (hCoh : CapLabelCoh (g, K, Comp.perform (Val.vcap n2 ℓ2) op u))
    (hFresh : FreshCfg (g, K, Comp.perform (Val.vcap n2 ℓ2) op u))
    (hrun : Config.run (F+1) (g, K, Comp.perform (Val.vcap n2 ℓ2) op u) = Result.done v)
    (hst : (ctxStates K).get? n2 = none ∨ (op ≠ "get" ∧ op ≠ "put"))
    (htx : (ctxTxns K).get? n2 = none ∨ isTxnOp op = false)
    (hev : evalD 1 g σ τ (Comp.perform (Val.vcap n2 ℓ2) op u) = some (.raised n2 op u, g, σ, τ)) :
    CompletesTo (F+1) g σ τ (Comp.perform (Val.vcap n2 ℓ2) op u) K v := by
  refine ⟨1, g, σ, τ, Or.inr ⟨n2, op, u, hev, ?_, ?_, ?_, ?_, ?_, F+1, by omega, ?_⟩⟩
  · rw [ctxNetEffect_self hCtx hTtx]; exact hCtx
  · rw [ctxNetEffect_self hCtx hTtx]; exact hTtx
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
    | custom ℓ' p cl => left; simp [Bang.handlesOp]
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
    ∀ (M : Comp) (g : Nat) (σ : SStore) (τ : THeap) (K : Bang.EvalCtx) (v : Val),
      CtxCorr σ K → CtxTxnCorr τ K → CapLabelCoh (g, K, M) → FreshCfg (g, K, M) →
      Config.run F (g, K, M) = Result.done v →
      CompletesTo F g σ τ M K v := by
  intro F
  induction F using Nat.strong_induction_on with
  | _ F ih =>
    intro M g σ τ K v hCtx hTtx hCoh hFresh hrun
    cases F with
    | zero => simp [Config.run] at hrun
    | succ F' =>
      cases M with
      | ret w =>
          refine ⟨1, g, σ, τ, Or.inl ⟨.ret w, by simp [evalD], ?_, ?_, ?_, ?_, F'+1, le_rfl, ?_⟩⟩
          · rw [ctxNetEffect_self hCtx hTtx]; exact hCtx
          · rw [ctxNetEffect_self hCtx hTtx]; exact hTtx
          · rw [ctxNetEffect_self hCtx hTtx]; exact hCoh
          · rw [ctxNetEffect_self hCtx hTtx]; exact hFresh
          · rw [ctxNetEffect_self hCtx hTtx]; exact hrun
      | lam M0 =>
          refine ⟨1, g, σ, τ, Or.inl ⟨.lam M0, by simp [evalD], ?_, ?_, ?_, ?_, F'+1, le_rfl, ?_⟩⟩
          · rw [ctxNetEffect_self hCtx hTtx]; exact hCtx
          · rw [ctxNetEffect_self hCtx hTtx]; exact hTtx
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
          obtain ⟨n, g1, σ1, τ1, hM0⟩ := ih F' (by omega) M0 g σ τ (Frame.letF N :: K) v hCletF hTletF hCohletF hFletF hrun'
          rcases hM0 with ⟨t, hev, hCf, hTf, hCohf, hFf, F1, hF1le, hcont⟩ | ⟨nn, oop, vv, hev, hCf, hTf, hCohf, hFf, hNR, F1, hF1le, hcont⟩
          · -- M0 terminated. t must be ret v0 (letF continuation pops ret). Recurse on subst.
            -- ctxNetEffect (letF N::K) = letF N :: ctxNetEffect K, so the letF frame is exposed.
            have hcne : ctxNetEffect (Frame.letF N :: K) σ1 τ1 = Frame.letF N :: ctxNetEffect K σ1 τ1 :=
              ctxNetEffect_cons_nonframe σ1 τ1 (by intro n ℓ s; simp) (by intro n ℓ Θ; simp)
            rw [hcne] at hCohf hFf hcont
            -- t is a terminal (ret / lam). letF only reduces on a ret; a lam under letF is stuck.
            rcases evalD_term_shape _ _ _ _ _ _ _ _ _ hev with ⟨v0, rfl⟩ | ⟨M2, rfl⟩
            ·
                have hCM' : CtxCorr σ1 (ctxNetEffect K σ1 τ1) :=
                  CtxCorr_ctxNetEffect_nonframe (by intro n ℓ s; simp) (by intro n ℓ Θ; simp) hCf
                have hTM' : CtxTxnCorr τ1 (ctxNetEffect K σ1 τ1) :=
                  CtxTxnCorr_ctxNetEffect_nonframe (by intro n ℓ s; simp) (by intro n ℓ Θ; simp) hTf
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
                obtain ⟨ns, gs, σs, τs, hsub⟩ :=
                  ih Fs (by omega) (Comp.subst v0 N) g1 σ1 τ1 (ctxNetEffect K σ1 τ1) v hCM' hTM' hCsub hFsub hFs
                -- whole letC evalD = evalD M0 (ret v0) then evalD (subst v0 N).
                refine ⟨max n ns + 1, gs, σs, τs, ?_⟩
                rcases hsub with ⟨ts, hevs, hCs, hTs, hCohs, hFsF, Fc, hFcle, hcs⟩ | ⟨nn2, oop2, vv2, hevs, hCs, hTs, hCohs, hFsF, hNR2, Fc, hFcle, hcs⟩
                · left
                  refine ⟨ts, ?_, ?_, ?_, ?_, ?_, Fc, by omega, ?_⟩
                  · rw [show max n ns + 1 = (max n ns) + 1 from rfl]
                    simp only [evalD]
                    rw [evalD_fuel_mono hev (Nat.le_max_left n ns)]
                    simp only [Option.bind_some]
                    exact evalD_fuel_mono hevs (Nat.le_max_right n ns)
                  · rw [ctxNetEffect_ctxNetEffect] at hCs; exact hCs
                  · rw [ctxNetEffect_ctxNetEffect] at hTs; exact hTs
                  · rw [ctxNetEffect_ctxNetEffect] at hCohs; exact hCohs
                  · rw [ctxNetEffect_ctxNetEffect] at hFsF; exact hFsF
                  · rw [ctxNetEffect_ctxNetEffect] at hcs; exact hcs
                · right
                  refine ⟨nn2, oop2, vv2, ?_, ?_, ?_, ?_, ?_, ?_, Fc, by omega, ?_⟩
                  · rw [show max n ns + 1 = (max n ns) + 1 from rfl]
                    simp only [evalD]
                    rw [evalD_fuel_mono hev (Nat.le_max_left n ns)]
                    simp only [Option.bind_some]
                    exact evalD_fuel_mono hevs (Nat.le_max_right n ns)
                  · rw [ctxNetEffect_ctxNetEffect] at hCs; exact hCs
                  · rw [ctxNetEffect_ctxNetEffect] at hTs; exact hTs
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
            rw [hcne] at hCohf hFf hNR
            have hCohr' := capLabelCoh_pop_letF hCohf
            have hFreshr' := freshCfg_pop_letF hFf
            have hNRr' := noResume_strip_cons hns hNR
            refine ⟨n+1, g1, σ1, τ1, Or.inr ⟨nn, oop, vv, ?_, hCr', hTr', hCohr', hFreshr', hNRr', F1, by omega, ?_⟩⟩
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
                (ih F' (by omega) M0 g σ τ K v hCtx hTtx
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
                (ih F' (by omega) (Comp.subst w N1) g σ τ K v hCtx hTtx
                  (capLabelCoh_step _ _ hFresh hCoh hstep) (freshCfg_step _ _ hFresh hstep) hrun')
          | inr w =>
              have hstep : Source.step (g, K, Comp.case (Val.inr w) N1 N2) = some (g, K, Comp.subst w N2) := rfl
              have hrun' : Config.run F' (g, K, Comp.subst w N2) = Result.done v := by
                have hs := Config.run_step F' (g, K, Comp.case (Val.inr w) N1 N2) (by intro gg vv hc; simp at hc)
                rw [hstep] at hs; simp only at hs; rw [← hs]; exact hrun
              exact completesTo_reduce (fun f => rfl) hstep
                (ih F' (by omega) (Comp.subst w N2) g σ τ K v hCtx hTtx
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
                (ih F' (by omega) (Comp.subst w (Comp.subst (Val.shift u) N)) g σ τ K v hCtx hTtx
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
              refine ⟨1, g, σ, τ, Or.inl ⟨.ret w, by simp [evalD], ?_, ?_, ?_, ?_, F', by omega, ?_⟩⟩
              · rw [ctxNetEffect_self hCtx hTtx]; exact hCtx
              · rw [ctxNetEffect_self hCtx hTtx]; exact hTtx
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
          obtain ⟨n, g1, σ1, τ1, hM0⟩ := ih F' (by omega) M0 g σ τ (Frame.appF u :: K) v hCappF hTappF hCohappF hFappF hrun'
          rcases hM0 with ⟨t, hev, hCf, hTf, hCohf, hFf, F1, hF1le, hcont⟩ | ⟨nn, oop, vv, hev, hCf, hTf, hCohf, hFf, hNR, F1, hF1le, hcont⟩
          · have hcne : ctxNetEffect (Frame.appF u :: K) σ1 τ1 = Frame.appF u :: ctxNetEffect K σ1 τ1 :=
              ctxNetEffect_cons_nonframe σ1 τ1 (by intro n ℓ s; simp) (by intro n ℓ Θ; simp)
            rw [hcne] at hCohf hFf hcont
            -- t is a terminal (ret / lam); appF only reduces on a lam; a ret under appF is stuck.
            rcases evalD_term_shape _ _ _ _ _ _ _ _ _ hev with ⟨v0, rfl⟩ | ⟨M2, rfl⟩
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
              obtain ⟨ns, gs, σs, τs, hsub⟩ :=
                ih Fs (by omega) (Comp.subst u M2) g1 σ1 τ1 (ctxNetEffect K σ1 τ1) v hCM' hTM' hCsub hFsub hFs
              refine ⟨max n ns + 1, gs, σs, τs, ?_⟩
              rcases hsub with ⟨ts, hevs, hCs, hTs, hCohs, hFsF, Fc, hFcle, hcs⟩ | ⟨nn2, oop2, vv2, hevs, hCs, hTs, hCohs, hFsF, hNR2, Fc, hFcle, hcs⟩
              · left
                refine ⟨ts, ?_, ?_, ?_, ?_, ?_, Fc, by omega, ?_⟩
                · simp only [evalD]
                  rw [evalD_fuel_mono hev (Nat.le_max_left n ns)]
                  simp only [Option.bind_some]
                  exact evalD_fuel_mono hevs (Nat.le_max_right n ns)
                · rw [ctxNetEffect_ctxNetEffect] at hCs; exact hCs
                · rw [ctxNetEffect_ctxNetEffect] at hTs; exact hTs
                · rw [ctxNetEffect_ctxNetEffect] at hCohs; exact hCohs
                · rw [ctxNetEffect_ctxNetEffect] at hFsF; exact hFsF
                · rw [ctxNetEffect_ctxNetEffect] at hcs; exact hcs
              · right
                refine ⟨nn2, oop2, vv2, ?_, ?_, ?_, ?_, ?_, ?_, Fc, by omega, ?_⟩
                · simp only [evalD]
                  rw [evalD_fuel_mono hev (Nat.le_max_left n ns)]
                  simp only [Option.bind_some]
                  exact evalD_fuel_mono hevs (Nat.le_max_right n ns)
                · rw [ctxNetEffect_ctxNetEffect] at hCs; exact hCs
                · rw [ctxNetEffect_ctxNetEffect] at hTs; exact hTs
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
            rw [hcne] at hCohf hFf hNR
            have hCohr' := capLabelCoh_pop_appF hCohf
            have hFreshr' := freshCfg_pop_appF hFf
            have hNRr' := noResume_strip_cons hns hNR
            refine ⟨n+1, g1, σ1, τ1, Or.inr ⟨nn, oop, vv, ?_, hCr', hTr', hCohr', hFreshr', hNRr', F1, by omega, ?_⟩⟩
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
            by_cases hop : op = "get"
            · subst hop
              cases hg : σ.get? n2 with
              | some sv =>
                  -- get-hit: evalD → term(ret sv); kernel dispatch_state_get → ret sv, SAME K.
                  have hgc : (ctxStates K).get? n2 = some sv := by rw [← hCtx]; exact hg
                  obtain ⟨Kᵢ, ℓ', Kₒ, hsp⟩ := splitAtId_of_ctxStates_get hFresh.2.2.1 hgc
                  have hlab : ℓ' = ℓ2 := by
                    have := capLabelCoh_perform_label hCoh hsp; simpa [Handler.label] using this
                  have hcr : Bang.CapResolves K n2 ℓ2 "get" :=
                    ⟨Kᵢ, Handler.state ℓ' sv, Kₒ, hsp, by subst hlab; simp [Bang.handlesOp]⟩
                  have hstep : Source.step (g, K, Comp.perform (Val.vcap n2 ℓ2) "get" u)
                      = some (g, K, Comp.ret sv) := by
                    simp only [Source.step, dispatch_state_get hcr hgc, Option.map_some]
                  have hrun' : Config.run F' (g, K, Comp.ret sv) = Result.done v := by
                    have hs := Config.run_step F' (g, K, Comp.perform (Val.vcap n2 ℓ2) "get" u)
                      (by intro gg vv hc; simp at hc)
                    rw [hstep] at hs; simp only at hs; rw [← hs]; exact hrun
                  refine ⟨1, g, σ, τ, Or.inl ⟨.ret sv, ?_, ?_, ?_, ?_, ?_, F', by omega, ?_⟩⟩
                  · show evalD 1 g σ τ (Comp.perform (Val.vcap n2 ℓ2) "get" u) = _
                    simp only [evalD, if_true]; rw [hg]
                  · rw [ctxNetEffect_self hCtx hTtx]; exact hCtx
                  · rw [ctxNetEffect_self hCtx hTtx]; exact hTtx
                  · rw [ctxNetEffect_self hCtx hTtx]; exact capLabelCoh_step _ _ hFresh hCoh hstep
                  · rw [ctxNetEffect_self hCtx hTtx]; exact freshCfg_step _ _ hFresh hstep
                  · rw [ctxNetEffect_self hCtx hTtx]; exact hrun'
              | none =>
                  -- get-miss: evalD → raised n2 "get" u; NoResume from the state-miss; dispatchRun
                  -- re-performs at the outer K (label-irrel on escape, label-match on resolve).
                  exact perform_miss_raises hCtx hTtx hCoh hFresh hrun
                    (Or.inl (by rw [← hCtx]; exact hg)) (Or.inr (by decide))
                    (by show evalD 1 g σ τ _ = _; simp only [evalD, if_true]; rw [hg])
            · by_cases hop2 : op = "put"
              · subst hop2
                cases hg : σ.get? n2 with
                | some sv =>
                    -- put-hit: evalD → term(ret vunit) with σ.put; kernel → ret vunit, K→updateCtxStates.
                    have hgc : (ctxStates K).get? n2 = some sv := by rw [← hCtx]; exact hg
                    obtain ⟨Kᵢ, ℓ', Kₒ, hsp⟩ := splitAtId_of_ctxStates_get hFresh.2.2.1 hgc
                    have hlab : ℓ' = ℓ2 := by
                      have := capLabelCoh_perform_label hCoh hsp; simpa [Handler.label] using this
                    have hcr : Bang.CapResolves K n2 ℓ2 "put" :=
                      ⟨Kᵢ, Handler.state ℓ' sv, Kₒ, hsp, by subst hlab; simp [Bang.handlesOp]⟩
                    have hstep : Source.step (g, K, Comp.perform (Val.vcap n2 ℓ2) "put" u)
                        = some (g, updateCtxStates K ((ctxStates K).put n2 u), Comp.ret .vunit) := by
                      simp only [Source.step, dispatch_state_put (w := u) hcr hgc, Option.map_some]
                    have hcoh' := capLabelCoh_step _ _ hFresh hCoh hstep
                    have hfr' := freshCfg_step _ _ hFresh hstep
                    have hctxeq : ctxNetEffect K (σ.put n2 u) τ = updateCtxStates K ((ctxStates K).put n2 u) := by
                      rw [hCtx, hTtx]; unfold ctxNetEffect
                      rw [show ctxTxns K = ctxTxns (updateCtxStates K ((ctxStates K).put n2 u)) from
                        (ctxTxns_updateCtxStates K _).symm, updateCtxTxns_self_aux]
                    have hrun' : Config.run F' (g, updateCtxStates K ((ctxStates K).put n2 u), Comp.ret .vunit)
                        = Result.done v := by
                      have hs := Config.run_step F' (g, K, Comp.perform (Val.vcap n2 ℓ2) "put" u)
                        (by intro gg vv hc; simp at hc)
                      rw [hstep] at hs; simp only at hs; rw [← hs]; exact hrun
                    refine ⟨1, g, σ.put n2 u, τ, Or.inl ⟨.ret .vunit, ?_, ?_, ?_, ?_, ?_, F', by omega, ?_⟩⟩
                    · show evalD 1 g σ τ (Comp.perform (Val.vcap n2 ℓ2) "put" u) = _
                      simp only [evalD, if_neg (by decide : ¬ ("put" = "get")), if_true]; rw [hg]
                    · rw [hctxeq, hCtx]; simp only [CtxCorr]; rw [ctxStates_updateCtxStates_put hgc]
                    · rw [hctxeq, hTtx]; simp only [CtxTxnCorr]; rw [ctxTxns_updateCtxStates]
                    · rw [hctxeq]; exact hcoh'
                    · rw [hctxeq]; exact hfr'
                    · rw [hctxeq]; exact hrun'
                | none =>
                    exact perform_miss_raises hCtx hTtx hCoh hFresh hrun
                      (Or.inl (by rw [← hCtx]; exact hg)) (Or.inr (by decide))
                      (by show evalD 1 g σ τ _ = _
                          simp only [evalD, if_neg (by decide : ¬ ("put" = "get")), if_true]; rw [hg])
              · by_cases hopt : isTxnOp op = true
                · cases hgt : τ.get? n2 with
                  | some Θ =>
                      -- txn-hit: evalD → term(ret r) with τ.put; kernel dispatch_txn_service, K→updateCtxTxns.
                      have hgt' : (ctxTxns K).get? n2 = some Θ := by rw [← hTtx]; exact hgt
                      obtain ⟨Kᵢ, ℓ', Kₒ, hsp⟩ := splitAtId_of_ctxTxns_get hFresh.2.2.1 hgt'
                      have hlab : ℓ' = ℓ2 := by
                        have := capLabelCoh_perform_label hCoh hsp; simpa [Handler.label] using this
                      have hcr : Bang.CapResolves K n2 ℓ2 op :=
                        ⟨Kᵢ, Handler.transaction ℓ' Θ, Kₒ, hsp, by
                          subst hlab; rcases isTxnOp_iff.mp hopt with rfl | rfl | rfl <;> simp [Bang.handlesOp]⟩
                      have hstep : Source.step (g, K, Comp.perform (Val.vcap n2 ℓ2) op u)
                          = some (g, updateCtxTxns K ((ctxTxns K).put n2 (txnService op u Θ).2),
                              Comp.ret (txnService op u Θ).1) := by
                        simp only [Source.step, dispatch_txn_service hopt hcr hgt', Option.map_some]
                      have hcoh' := capLabelCoh_step _ _ hFresh hCoh hstep
                      have hfr' := freshCfg_step _ _ hFresh hstep
                      have hctxeq : ctxNetEffect K σ (τ.put n2 (txnService op u Θ).2)
                          = updateCtxTxns K ((ctxTxns K).put n2 (txnService op u Θ).2) := by
                        rw [hCtx, hTtx]; unfold ctxNetEffect; rw [updateCtxStates_self_aux]
                      have hrun' : Config.run F' (g, updateCtxTxns K ((ctxTxns K).put n2 (txnService op u Θ).2),
                          Comp.ret (txnService op u Θ).1) = Result.done v := by
                        have hs := Config.run_step F' (g, K, Comp.perform (Val.vcap n2 ℓ2) op u)
                          (by intro gg vv hc; simp at hc)
                        rw [hstep] at hs; simp only at hs; rw [← hs]; exact hrun
                      refine ⟨1, g, σ, τ.put n2 (txnService op u Θ).2,
                        Or.inl ⟨.ret (txnService op u Θ).1, ?_, ?_, ?_, ?_, ?_, F', by omega, ?_⟩⟩
                      · show evalD 1 g σ τ (Comp.perform (Val.vcap n2 ℓ2) op u) = _
                        simp only [evalD, if_neg hop, if_neg hop2, hopt, if_true]; rw [hgt]
                      · rw [hctxeq, hCtx]; simp only [CtxCorr]; rw [ctxStates_updateCtxTxns]
                      · rw [hctxeq, hTtx]; simp only [CtxTxnCorr]; rw [ctxTxns_updateCtxTxns_service hgt']
                      · rw [hctxeq]; exact hcoh'
                      · rw [hctxeq]; exact hfr'
                      · rw [hctxeq]; exact hrun'
                  | none =>
                      exact perform_miss_raises hCtx hTtx hCoh hFresh hrun
                        (Or.inr ⟨hop, hop2⟩) (Or.inl (by rw [← hTtx]; exact hgt))
                        (by show evalD 1 g σ τ _ = _
                            simp only [evalD, if_neg hop, if_neg hop2, hopt, if_true]; rw [hgt])
                · -- non-resumptive op (not get/put/txn): evalD → raised directly.
                  rw [Bool.not_eq_true] at hopt
                  exact perform_miss_raises hCtx hTtx hCoh hFresh hrun
                    (Or.inr ⟨hop, hop2⟩) (Or.inr hopt)
                    (by show evalD 1 g σ τ _ = _
                        simp only [evalD, if_neg hop, if_neg hop2, hopt, Bool.false_eq_true, if_false])
          | _ =>
              -- non-cap perform: evalD = none, so Config.run is stuck ≠ done (absurd).
              exfalso; cases F' <;> simp_all [Config.run, Source.step]
      | handle h0 M0 =>
          -- MIRROR run_evalD handle arms (state 4268 / throws 4328 / txn 4417). Mint id:=g, install the
          -- handleF g h0 frame, run the substituted body via IH; compose the whole-handle evalD via the
          -- ported U5bPort.*_composes lemmas. The fuel IH lands on `subst (vcap g h.label) M0` directly
          -- (the de-risk's core: mint+subst absorbed by the fuel IH, no congruence).
          cases h0 with
          | custom _ _ _ =>
              -- custom: kernel Source.step mints+installs, but evalD custom = none. The kernel run still
              -- proceeds; the converse can't produce an evalD `some` — this is the ADR-0085 stage-1 gap.
              -- HOWEVER no source/compiled program produces a custom handle (untyped), so this arm is
              -- unreachable for the frozen consumer at K=[]. DRAFT-SORRY: stage-1 custom (out of scope).
              sorry
          | state ℓ0 s0 =>
              -- install handleF g (state ℓ0 s0), push σ.push g s0, run subst body at g+1.
              have hmint : Source.step (g, K, Comp.handle (Handler.state ℓ0 s0) M0)
                  = some (g+1, Frame.handleF g (Handler.state ℓ0 s0) :: K, Comp.subst (Val.vcap g ℓ0) M0) := rfl
              have hCinstall : CtxCorr (σ.push g s0) (Frame.handleF g (Handler.state ℓ0 s0) :: K) :=
                CtxCorr_install hCtx
              have hTinstall : CtxTxnCorr τ (Frame.handleF g (Handler.state ℓ0 s0) :: K) :=
                CtxTxnCorr_cons_nontxn (by intro n ℓ Θ; simp) hTtx
              have hCohInstall := capLabelCoh_step _ _ hFresh hCoh hmint
              have hFreshInstall := freshCfg_step _ _ hFresh hmint
              have hrun' : Config.run F' (g+1, Frame.handleF g (Handler.state ℓ0 s0) :: K,
                  Comp.subst (Val.vcap g ℓ0) M0) = Result.done v := by
                have hs := Config.run_step F' (g, K, Comp.handle (Handler.state ℓ0 s0) M0)
                  (by intro gg vv hc; simp at hc)
                rw [hmint] at hs; simp only at hs; rw [← hs]; exact hrun
              obtain ⟨n, g1, σ1, τ1, hbody⟩ := ih F' (by omega) (Comp.subst (Val.vcap g ℓ0) M0) (g+1)
                (σ.push g s0) τ (Frame.handleF g (Handler.state ℓ0 s0) :: K) v
                hCinstall hTinstall hCohInstall hFreshInstall hrun'
              rcases hbody with ⟨t, hev, hCf, hTf, hCohf, hFf, F1, hF1le, hcont⟩ | ⟨nn, oop, vv, hev, hCf, hTf, hCohf, hFf, hNR, F1, hF1le, hcont⟩
              · -- body terminates: t = ret v0 (evalD_term_shape; lam under handleF is stuck).
                rcases evalD_term_shape _ _ _ _ _ _ _ _ _ hev with ⟨v0, rfl⟩ | ⟨M2, rfl⟩
                · -- POP the state frame: whole handle → term(ret v0), σ1.tail. Compose via handle_state_composes.
                  obtain ⟨⟨hCpop, hTpop⟩, hnetEq⟩ := CtxCorr_ctxNetEffect_pop_state hCf hTf
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
                  refine ⟨n+1, g1, σ1.tail, τ1, Or.inl ⟨.ret v0, ?_, hCpop, hTpop, hCohPop, hFreshPop, Fs, by omega, hFs⟩⟩
                  exact handle_state_composes n g σ τ ℓ0 s0 M0 v0 g1 σ1 τ1 hev
                · -- lam under handleF-state (UNMARK expects ret): stuck ⟹ hcont-absurd.
                  exfalso
                  obtain ⟨⟨_, _⟩, hnetEq⟩ := CtxCorr_ctxNetEffect_pop_state hCf hTf
                  rw [hnetEq] at hcont
                  cases F1 with
                  | zero => simp [Config.run] at hcont
                  | succ F1' =>
                      rw [Config.run_step F1' _ (by intro gg vv hc; simp at hc)] at hcont
                      simp [Source.step, Config.run] at hcont
              · -- body raises: DRAFT-SORRY (state forwards the raise; mirror run_evalD:4325 raised-forward).
                sorry
          | throws ℓ0 =>
              -- throws: no store push; normal return pops; a raise to identity g op "raise" is CAUGHT.
              sorry
          | transaction ℓ0 Θ =>
              -- txn: push τ.push g Θ, pop τ1.tail on return (free rollback). Mirror state on the τ side.
              sorry
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
               refine ⟨1, g, σ, τ, Or.inl ⟨.ret (op.eval x y), by simp [evalD], ?_, ?_, ?_, ?_, F', by omega, ?_⟩⟩
               · rw [ctxNetEffect_self hCtx hTtx]; exact hCtx
               · rw [ctxNetEffect_self hCtx hTtx]; exact hTtx
               · rw [ctxNetEffect_self hCtx hTtx]; exact capLabelCoh_step _ _ hFresh hCoh hstep
               · rw [ctxNetEffect_self hCtx hTtx]; exact freshCfg_step _ _ hFresh hstep
               · rw [ctxNetEffect_self hCtx hTtx]; exact hrun')
            | (exfalso; cases F' <;> simp_all [Config.run, Source.step])

end Bang.CalcVM
