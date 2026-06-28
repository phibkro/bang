import Bang.CalcVM

/-! # U5b-handler refute-watch — Route-1 (fuel induction) DOES absorb mint+subst

## VERDICT: REFUTE-WATCH PASSES. The fuel IH applies directly to the substituted body.

### Background — what died (route-A congruence), and why
The route-A reverse completeness bridge lifted a focus simulation `Sim cx cy` through a
frame stack `K`; its `handleF` case needed
  `Sim.handle : Sim cx cy → Sim (handle hh cx) (handle hh cy)`.
Under route-B (ADR-0052) `evalD (handle hh cy)` MINTS `id := g`, SUBSTITUTES `vcap g ℓ`
into the body, and runs `subst (vcap g ℓ) cy` at `g+1` — so `Sim.handle` would require
SUBSTITUTION-CLOSURE of the black-box relation `Sim`, which it lacks (witness `82cc585`,
`scratch/U5bSimSpike.lean`). The whole `Sim`/`evalD_plug_sim`/`Sim.handle` machinery was
DELETED and STAYS deleted (do NOT resurrect — Route 2 considered + rejected).

### Why Route-1 (fuel induction) dissolves the wall
A fuel induction (mirroring the proven forward `sim`/`run_evalD`, store-threaded) hands its IH
to the body `subst (vcap g ℓ) M` DIRECTLY — there is no black-box relation to substitution-close.
`evalD`'s handle clause (`Bang/CalcVM.lean:245`) IS a `bind` of `evalD f (g+1) (σ.push g s) τ
(subst (vcap g ℓ0) M)`, so a body term-result composes through it by a one-line `simp [evalD]`.

The three lemmas below BUILD-CONFIRM that composition for all three handler kinds (state · txn ·
throws-normal · throws-CAUGHT), and the dispatch note pins the perform arm. This is the exact
dual of `run_evalD`'s handle arm (`Bang/CalcVM.lean:4262`/`4321`/`4410`).
-/

namespace Bang.CalcVM.U5bHandlerSpike
open Bang (Val Comp Frame Config Result Handler)
open Bang.CalcVM
open Bang.CapCoh (CapLabelCoh capLabelCoh_step)
open Bang.Model (FreshCfg freshCfg_step)

/-- **STATE handler — the refute-watch core.** The fuel IH on the SUBSTITUTED body
`subst (vcap g ℓ0) M` (at the minted counter `g+1`, pushed store `σ.push g s0`) composes
through `evalD`'s handle clause to a term-result for the whole `handle (state ℓ0 s0) M` node.
NO substitution-closure of a black-box relation — the precise thing route-A could not do. -/
theorem handle_state_composes
    (f g : Nat) (σ : SStore) (τ : THeap) (ℓ0 : Bang.EffectRow.Label) (s0 : Val) (M : Comp)
    (v0 : Val) (g' : Nat) (σ' : SStore) (τ' : THeap)
    (hbody : evalD f (g+1) (σ.push g s0) τ (Comp.subst (Val.vcap g ℓ0) M)
               = some (.term (.ret v0), g', σ', τ')) :
    evalD (f+1) g σ τ (Comp.handle (Handler.state ℓ0 s0) M)
               = some (.term (.ret v0), g', σ'.tail, τ') := by
  simp only [evalD, Handler.label, hbody, Option.bind_some]

/-- **TRANSACTION handler** — the `τ`-side mirror (`τ.push g Θ`, pop `τ'.tail`). -/
theorem handle_txn_composes
    (f g : Nat) (σ : SStore) (τ : THeap) (ℓ0 : Bang.EffectRow.Label) (Θ : List Val) (M : Comp)
    (v0 : Val) (g' : Nat) (σ' : SStore) (τ' : THeap)
    (hbody : evalD f (g+1) σ (τ.push g Θ) (Comp.subst (Val.vcap g ℓ0) M)
               = some (.term (.ret v0), g', σ', τ')) :
    evalD (f+1) g σ τ (Comp.handle (Handler.transaction ℓ0 Θ) M)
               = some (.term (.ret v0), g', σ', τ'.tail) := by
  simp only [evalD, Handler.label, hbody, Option.bind_some]

/-- **THROWS handler, normal return** — body returns `ret v0`, stores pass through. -/
theorem handle_throws_normal_composes
    (f g : Nat) (σ : SStore) (τ : THeap) (ℓ0 : Bang.EffectRow.Label) (M : Comp)
    (v0 : Val) (g' : Nat) (σ' : SStore) (τ' : THeap)
    (hbody : evalD f (g+1) σ τ (Comp.subst (Val.vcap g ℓ0) M)
               = some (.term (.ret v0), g', σ', τ')) :
    evalD (f+1) g σ τ (Comp.handle (Handler.throws ℓ0) M)
               = some (.term (.ret v0), g', σ', τ') := by
  simp only [evalD, Handler.label, hbody, Option.bind_some]

/-- **THROWS handler, CAUGHT (zero-shot abort)** — body RAISES to THIS handler's identity `g`
with op `"raise"`; the IH's RAISED result aborts to `term (ret w)`. This is the converse's
consumer of the RAISED IH (`ihR`), dual to `run_evalD`:4369. The fuel IH again lands directly
on the substituted body — no congruence. -/
theorem handle_throws_caught_composes
    (f g : Nat) (σ : SStore) (τ : THeap) (ℓ0 : Bang.EffectRow.Label) (M : Comp)
    (w : Val) (g' : Nat) (σ' : SStore) (τ' : THeap)
    (hbody : evalD f (g+1) σ τ (Comp.subst (Val.vcap g ℓ0) M)
               = some (.raised g "raise" w, g', σ', τ')) :
    evalD (f+1) g σ τ (Comp.handle (Handler.throws ℓ0) M)
               = some (.term (.ret w), g', σ', τ') := by
  simp only [evalD, Handler.label, hbody, Option.bind_some, and_self, if_true]

/-- **THROWS handler, FORWARDED** — body raises to a DIFFERENT identity (or non-"raise"); the
raise propagates past this frame. Pins that the catch is identity-AND-op gated. -/
theorem handle_throws_forward_composes
    (f g : Nat) (σ : SStore) (τ : THeap) (ℓ0 : Bang.EffectRow.Label) (M : Comp)
    (n : Nat) (op : Bang.OpId) (w : Val) (g' : Nat) (σ' : SStore) (τ' : THeap)
    (hne : ¬ (n = g ∧ op = "raise"))
    (hbody : evalD f (g+1) σ τ (Comp.subst (Val.vcap g ℓ0) M)
               = some (.raised n op w, g', σ', τ')) :
    evalD (f+1) g σ τ (Comp.handle (Handler.throws ℓ0) M)
               = some (.raised n op w, g', σ', τ') := by
  simp only [evalD, Handler.label, hbody, Option.bind_some, if_neg hne]

/-! ### The dispatch (perform) arm — pinned by `evalD`'s definitional reduction.
The other new arm vs the pure fragment is `perform (vcap n ℓ) op v`. Unlike route-A's
`evalD_plug_dispatch` congruence (also deleted), route-B's `evalD` resolves the op by the
identity-keyed store/heap DIRECTLY (`Bang/CalcVM.lean:223`), so each op is a definitional
`some` — no congruence lift. The `get` shape, build-confirmed: -/
theorem perform_get_resolves
    (f g : Nat) (σ : SStore) (τ : THeap) (n : Nat) (ℓ : Bang.EffectRow.Label) (v sv : Val)
    (hget : σ.get? n = some sv) :
    evalD (f+1) g σ τ (Comp.perform (Val.vcap n ℓ) "get" v)
      = some (.term (.ret sv), g, σ, τ) := by
  simp only [evalD, if_true, hget]

/-! ### Converse-of-`run_evalD` TERM-part — statement shape build-confirmed (trivial arms closed).

The completeness spine's term part, stated as the inverse of `run_evalD`'s term part
(`CalcVM.lean:3994`): from a whole-config `Config.run` to `.done v`, EXTRACT that the focus `M`
runs (via `evalD`) to a term `t`, with `K`'s handlers reflected in σ/τ (`CtxCorr`/`CtxTxnCorr`)
and the continuation `(g', ctxNetEffect K σ' τ', t)` still running to `.done v`. Strong induction
on the Source fuel `F`.

The `ret`/`lam` arms below BUILD-CONFIRM the statement shape (esp. that `ctxNetEffect_self`
discharges the coherence/continuation clauses for a value focus — the same reuse `run_evalD`'s
`ret` arm makes at 4026). The structural/handler/dispatch arms are `sorry` with the
`run_evalD` line to MIRROR (inverted). -/
theorem convTerm : ∀ (F : Nat) (M : Comp) (g : Nat) (σ : SStore) (τ : THeap)
    (K : Bang.EvalCtx) (v : Val),
    CtxCorr σ K → CtxTxnCorr τ K → CapLabelCoh (g, K, M) → FreshCfg (g, K, M) →
    Config.run F (g, K, M) = Result.done v →
    ∃ n g' σ' τ' t,
      evalD n g σ τ M = some (.term t, g', σ', τ') ∧
      CtxCorr σ' (ctxNetEffect K σ' τ') ∧ CtxTxnCorr τ' (ctxNetEffect K σ' τ') ∧
      CapLabelCoh (g', ctxNetEffect K σ' τ', t) ∧ FreshCfg (g', ctxNetEffect K σ' τ', t) ∧
      ∃ F', Config.run F' (g', ctxNetEffect K σ' τ', t) = Result.done v := by
  intro F
  induction F using Nat.strong_induction_on with
  | _ F ih =>
    intro M g σ τ K v hCtx hTtx hCoh hFresh hrun
    cases F with
    | zero => simp [Config.run] at hrun
    | succ F' =>
      cases M with
      | ret w =>
          -- value focus: evalD is immediate; ctxNetEffect_self collapses the net-effect to K, so the
          -- coherence + continuation clauses are exactly the hypotheses (dual of run_evalD:4023).
          refine ⟨1, g, σ, τ, .ret w, by simp [evalD], ?_, ?_, ?_, ?_, F'+1, ?_⟩
          · rw [ctxNetEffect_self hCtx hTtx]; exact hCtx
          · rw [ctxNetEffect_self hCtx hTtx]; exact hTtx
          · rw [ctxNetEffect_self hCtx hTtx]; exact hCoh
          · rw [ctxNetEffect_self hCtx hTtx]; exact hFresh
          · rw [ctxNetEffect_self hCtx hTtx]; exact hrun
      | lam M0 =>
          refine ⟨1, g, σ, τ, .lam M0, by simp [evalD], ?_, ?_, ?_, ?_, F'+1, ?_⟩
          · rw [ctxNetEffect_self hCtx hTtx]; exact hCtx
          · rw [ctxNetEffect_self hCtx hTtx]; exact hTtx
          · rw [ctxNetEffect_self hCtx hTtx]; exact hCoh
          · rw [ctxNetEffect_self hCtx hTtx]; exact hFresh
          · rw [ctxNetEffect_self hCtx hTtx]; exact hrun
      | letC M0 N => sorry   -- MIRROR run_evalD:4033 (two ihT calls; continuation peels SUBST via run_step)
      | force a => sorry     -- MIRROR run_evalD:4085 (vthunk: one ihT, run_step peels force)
      | app M0 u => sorry    -- MIRROR run_evalD:4103
      | handle h0 M0 => sorry -- MIRROR run_evalD:4262/4321/4410; handle arms via the *_composes lemmas above
      | perform cap op u => sorry -- MIRROR run_evalD perform; dispatch via perform_*_resolves above
      | case w N1 N2 => sorry  -- MIRROR run_evalD case arm
      | split w N => sorry     -- MIRROR run_evalD split arm
      | unfold w => sorry      -- MIRROR run_evalD unfold arm
      | oom => sorry           -- absurd: Config.run of oom focus can't be done v
      | wrong a => sorry       -- absurd

end Bang.CalcVM.U5bHandlerSpike

/-! ## The CONVERSE-OF-`run_evalD` completeness spine (the Route-1 architecture)

The full deliverable recasts `evalD_complete_gen` as a STORE-THREADED converse of `run_evalD`
(`Bang/CalcVM.lean:3993`), inducting on the Source `Config.run` fuel. The current
`evalD_complete_gen_pure` (plug-congruence, empty stores) is STRUCTURALLY UNABLE to express the
handler arms — `evalD` realizes handlers via the STORE (`σ.push g s`), not via re-evaluable
`handle` nodes, so a counter/store-uniform plug-congruence cannot bridge the `g → g+1`,
`[] → σ.push g s` shift. The converse keeps the FOCUS form (not `plug K c`) with `K`'s handler
frames reflected into `σ`/`τ` via `CtxCorr`/`CtxTxnCorr` — exactly `run_evalD`'s generalization.

Statement shape (two-part, dual to `run_evalD`'s two-part term/raised):

  TERM:  CtxCorr σ K → CtxTxnCorr τ K → CapLabelCoh (g,K,M) → FreshCfg (g,K,M) →
         Config.run F (g, K, M) = .done v →
         ∃ n g' σ' τ' t, evalD n g σ τ M = some (.term t, g', σ', τ')
           ∧ <coherence/freshness preserved at (g', ctxNetEffect K σ' τ', t)>
           ∧ ∃ F', Config.run F' (g', ctxNetEffect K σ' τ', t) = .done v

  RAISED: <dual, threading `dispatchRun` like run_evalD:4001>

The handle arms of this spine close by the five `*_composes` lemmas above (the IH lands on
`subst (vcap g ℓ0) M` at `(g+1, σ.push g s0, τ)`); the perform arm by `perform_*_resolves`;
the letC/app/force/case/split/unfold arms are the mechanical store-threaded mirror of
`run_evalD`'s same arms (4033–). The frozen `evalD_complete_gen` (`plug K c`, counter 0,
empty stores) then follows at `K = []` for the closed program, via `run_plug_reshape`
(`Bang/LR.lean:402`) to reduce the config-run to a closed-term run.

This is a U2-scale grind (~the size of `run_evalD`, 3993–5037, inverted). The refute-watch
above DE-RISKS its load-bearing question: the mint+subst the congruence approach could not
absorb IS absorbed by the fuel IH, for every handler kind. -/
