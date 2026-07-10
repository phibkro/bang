/-
  scratch/Stage5LRProbe.lean — s5probe: the Stage-5 user-effect binary-LR DESIGN MAP.

  PROBE-FIRST (the s3k pattern). This file is NOT a grind: each of the three
  pre-registered debts is stated so it COMPILES with `sorry` against main, with a
  concrete proof PLAN in the doc-comment. The deliverable is the map in
  docs/notes/stage5-lr-design.md; this file is its build-checked witness.

  CENSUS: this is a SCRATCH probe — it is not imported by `Bang/Audit.lean`, so its
  sorries feed NOTHING in the `just axioms` gate. The three real debts live as the
  four already-flagged `lr_*` stubs in Bang/Meta/BinaryLR.lean (crelK_fund /
  krelS_refl custom arms) + Bang/Meta/LR.lean (dispatchOn_rename custom arm). This
  probe pins the STATEMENT SHAPES those grind commits will fill, standalone.

  Ground: paths/PATH-inc5-lr-reindex.md · ADR-0092 §D3-as-landed (ret-shape) ·
  ADR-0085/0087 (custom rep) · the ◊4.5 answer-typed KrelS/CrelK architecture.
-/
module

public import Bang.Meta.BinaryLR

namespace Bang.Stage5Probe

open Bang
open Bang.EffectRow (Label)

@[expose] public section

variable {Eff  : Type} [Lattice Eff] [OrderBot Eff]
variable {Mult : Type} [CommSemiring Mult] [DecidableEq Mult]
variable [EffSig Eff Mult]

/-! ## The load-bearing tractability fact (ADR-0092 §D3-as-landed ret-shape)

The custom resume focus (`Dispatch.dispatchOn` custom arm) is

  `Comp.subst p (Comp.subst (Val.shift v) clause.2)`

and for a v1 clause `clause.2 = Comp.ret w` (HasClauses.cons). `Comp.substFrom k _ (.ret w)
= .ret (Val.substFrom k _ w)` (Subst.lean), so the focus REDUCES to

  `Comp.ret (Val.subst p (Val.subst (Val.shift v) w))`   -- a `ret` of a CLOSED value.

This is EXACTLY the shape state/txn resume produce (`ret <closed val>`). So the entire
`krelS_append`/`krelS_handleF_intro` resume-conjunct machinery — which demands the
dispatched config be `(Sᵢ, Comp.ret r)` with `r₁ ~ r₂` at the perform's returner type —
applies with NO new convergence infrastructure. THE RET-SHAPE MAKES STAGE 5 TRACTABLE:
the hard "continuation-capture / effectful-clause" case does not arise in v1. -/

/-- PROBE FACT (build-checked): the v1 custom resume focus is a `ret`-of-value. -/
theorem custom_resume_is_ret (p v w : Val) :
    Comp.subst p (Comp.subst (Val.shift v) (Comp.ret w))
      = Comp.ret (Val.subst p (Val.subst (Val.shift v) w)) := by
  simp only [Comp.subst, Comp.substFrom]

/-- The per-clause resume-value relation the grind adds to `HandlerRel`'s custom arm
(currently `False`). `ClauseRel n ℓ P p₁ p₂ cl₁ cl₂`: same label, same clause ops, params
related at `P`, and each clause's resumed VALUE `w` self-relates at `opRes ℓ op` under the
`[arg@0, param@1]` bindings once the (closed) param+arg are filled. This is the custom
analogue of `state`'s `∃ S, VrelK n S s₁ s₂` and `transaction`'s pointwise-heap conjunct.
For the SELF-relation (reinstall diagonal) it collapses to `cl₁ = cl₂ ∧ p₁ = p₂` plus
`vrelK_fund` on each clause value — exactly `krelS_state_reinstall`'s `hsv`. -/
def ClauseRel (n : Nat) (ℓ : Label) (P : VTy Eff Mult) (p₁ p₂ : Val)
    (cl₁ cl₂ : List (OpId × Comp)) : Prop :=
  cl₁ = cl₂ ∧ VrelK (Eff := Eff) (Mult := Mult) n P p₁ p₂ ∧
    HasClauses (Eff := Eff) (Mult := Mult) ℓ P cl₁


/-! ## DEBT 1 — `compatK_handleCustom` (the compat lemma for `HasCTy.handleCustom`)

The `crelK_fund` custom arm (BinaryLR.lean:2089). Direct analogue of `compatK_handleState`
/ `compatK_handleTransaction`: MINT `(g, K, handle (custom ℓ p cl) M) ↦ (g+1, handleF g
(custom ℓ p cl)::K, subst (vcap g ℓ) M)`, run the cap-quantified body through a REINSTALLING
stack (debt 2), tail re-cast `g→g+1` (`KrelS_g_cast`/`KrelS_eff_cast`).

INDUCTION: none of its own — it is a CONGRUENCE that delegates the stack to `krelS_custom_reinstall`
(debt 2) exactly as `compatK_handleState` delegates to `krelS_state_reinstall`.

LEMMAS: `coApproxC_le_reduce` (exists) · `krelS_custom_reinstall` (debt 2, TO BUILD) ·
`KrelS_g_cast`/`KrelS_eff_cast` (exist). The typing premises (`HasClauses`, coverage,
`HasVTy [] [] p P`) thread straight from `HasCTy.handleCustom` — mirror the state arm's
`hgr/hp/hpr/hrestrict/hcs/hsv` threading.

WALL — NONE structural: the ret-shape (above) means the body's returner type `F q A` is the
mint target and the resume conjunct is `ret`-shaped, so this arm is a MECHANICAL transcription
of `compatK_handleState` once debt 2 exists. Risk lives entirely in debt 2. -/
theorem compatK_handleCustom {n : Nat} {q : Mult} {A P : VTy Eff Mult} {e φ : Eff} {ℓ : Label}
    {p : Val} {cl : List (OpId × Comp)} {M₁ M₂ : Comp}
    (hcl : HasClauses (Eff := Eff) (Mult := Mult) ℓ P cl)
    (hcov : ∀ op B, EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ op = some B →
      (cl.find? (·.1 == op)).isSome)
    (hp : HasVTy (Eff := Eff) (Mult := Mult) [] [] p P)
    (hbody : ∀ gid, CrelK n (CTy.F q A) e
      (Comp.subst (Val.vcap gid ℓ) M₁) (Comp.subst (Val.vcap gid ℓ) M₂)) :
    CrelK n (CTy.F q A) φ (Comp.handle (Handler.custom ℓ p cl) M₁)
                          (Comp.handle (Handler.custom ℓ p cl) M₂) := by
  -- PLAN (mirror compatK_handleState BinaryLR.lean:1768):
  --   rw [CrelK]; intro g D K₁ K₂ hK
  --   coApproxC_le_reduce to the minted (g+1, handleF g (custom ℓ p cl)::Kⱼ, subst (vcap g ℓ) Mⱼ)
  --   apply (hbody g) through `krelS_custom_reinstall … (KrelS_g_cast n g (g+1) … (KrelS_eff_cast hK))`.
  sorry

/-! ## DEBT 2 — `krelS_custom_reinstall` (THE RISKIEST ARM — the resumptive heart)

The `krelS_refl` custom arm (BinaryLR.lean:2180) AND the stack the compat lemma runs the body
through. A `custom ℓ p cl` frame over a `KrelS`-related tail self-relates at every index, resume
conjunct supplied by GUARDED RECURSION on the index — the EXACT skeleton of
`krelS_state_reinstall` (BinaryLR.lean:1281) / `krelS_transaction_reinstall`.

INDUCTION: `Nat.strong_induction_on` on the step index (guarded recursion). The resume dispatch
reinstalls `handleF nh (custom ℓ p cl)` (SAME p, SAME cl — v1 READ-ONLY param, so the reinstall
diagonal is `p=p, cl=cl`; contrast state's `put` which reinstalls a DIFFERENT stored value — the
read-only param makes THIS lemma STRICTLY SIMPLER than state) and resumes `ret r` where
`r = Val.subst p (Val.subst (Val.shift w) clause.2's-value)`, then `krelS_append`s it onto the
reinstalled frame at the DROPPED index `m' < m` (the IH).

THE RESUME VALUE relation: dispatch resumes with `clause[param:=p, arg:=w]` = `ret r`. The
perform's returner type is `F q_perf (opRes ℓ op)`; the resumed value `r : opRes ℓ op` must
`VrelK m' (opRes ℓ op) r₁ r₂`. This comes from `HasClauses.cons`'s `HasVTy [qa,qp] [opA,P] w opR`
premise + `vrelK_fund` (specialized to the closed param+arg fillers) — the custom analogue of
state's `hVrel S`/`hsv`. This is the ONE genuinely new sub-proof: a `clause_resume_vrel` helper
turning the clause's `HasVTy` into `VrelK` of the substituted value pair.

LEMMAS: `krelS_handleF_intro` (exists) · `krelS_append` (exists — its custom cases currently
`absurd hHRtop` via `HandlerRel custom = False`; making `HandlerRel` custom REAL, `ClauseRel`
above, un-refutes them and needs the two `dispatchOn_isSome`-style totality arms
`dispatchOn (custom) isSome` — TO BUILD, one-liner like `dispatchOn_state_isSome`) ·
`clause_resume_vrel` (VrelK of the substituted clause value — TO BUILD from HasClauses + vrelK_fund).

WALLS (named honestly):
  (W-a) `HandlerRel` custom arm is `False` (LR.lean:1655). The grind MUST replace it with the
        `ClauseRel` shape. This is a `HandlerRel` DEFN change (LR.lean) — NOT a frozen statement,
        but it ripples: every `HandlerRel` case-split (krelS_append's `| custom => absurd`) must
        gain a real custom arm. ~4 sites (`grep "HandlerRel" | custom`). MECHANICAL but WIDE.
  (W-b) `krelS_append`'s nested-handleF case needs `dispatchOn (custom) isSome` (currently the
        custom branch is `absurd hHRtop`). Two one-liners (`dispatchOn_custom_isSome`).
  (W-c) `clause_resume_vrel`: the substituted-clause-value VrelK. The clause value `w` is typed
        `HasVTy [qa,qp] [opA,P] w opR` (OPEN, two binders); after filling closed param p + closed
        arg, it is CLOSED and `vrelK_fund` applies. The binder-fill commutation (`subst p (subst
        (shift arg) w)`) is the `split`-shape double-subst (idx1-then-idx0) already proven for
        the machine (`Dispatch` custom arm comment). MECHANICAL (closeC_subst_comm-style), NOT a wall.
No continuation-capture wall: the ret-shape (top fact) means resume is `ret r`, never an effectful
clause needing the captured `k` first-class. -/
theorem krelS_custom_reinstall {q : Mult} {A P : VTy Eff Mult} {D : CTy Eff Mult} {φ : Eff}
    {ℓ : Label} {g : Nat} {cl : List (OpId × Comp)}
    (hcl : HasClauses (Eff := Eff) (Mult := Mult) ℓ P cl)
    (hcov : ∀ op B, EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ op = some B →
      (cl.find? (·.1 == op)).isSome) :
    ∀ (nh : Nat) m (p₁ p₂ : Val), Val.Closed p₁ → Val.Closed p₂ →
      VrelK (Eff := Eff) (Mult := Mult) m P p₁ p₂ →
      ∀ (K₁ K₂ : Stack), KrelS m (CTy.F q A) D φ g K₁ K₂ →
      KrelS m (CTy.F q A) D φ g (Frame.handleF nh (Handler.custom ℓ p₁ cl) :: K₁)
                              (Frame.handleF nh (Handler.custom ℓ p₂ cl) :: K₂) := by
  -- PLAN (mirror krelS_state_reinstall BinaryLR.lean:1281):
  --   intro nh m; induction m using Nat.strong_induction_on with | _ m ih =>
  --   intro p₁ p₂ hcp₁ hcp₂ hpv K₁ K₂ hK
  --   krelS_handleF_intro (HandlerRel custom = ClauseRel …) hK ?resume
  --   in resume: `hrestrict`+`hcov` give the clause; `dispatchOn` custom arm computes the reinstall;
  --   `clause_resume_vrel` gives `VrelK m' (opRes ℓ op) r₁ r₂`; `krelS_append` (Dᵢ := F q A) at m'
  --   composes the captured `Kᵢ` with the reinstalled `custom ℓ p cl :: K` (IH at m', SAME p — read-only).
  sorry

/-! ## DEBT 3 — `dispatchOn_rename` custom arm (the rename-commutation debt)

LR.lean:791 — the ONE `sorry` in `dispatchOn_rename`'s custom `some clause` case. `renameH` is
IDENTITY on custom (LR.lean:480), so:
  LHS: `dispatchOn (σn) op (renameV σ v) (renameK σ Kᵢ, custom ℓ p cl, renameK σ Kₒ)`
     = `(renameK σ Kᵢ ++ handleF (σn) (custom ℓ p cl) :: renameK σ Kₒ,
         Comp.subst p (Comp.subst (Val.shift (renameV σ v)) clause.2))`
  RHS: `.map (renameK σ, renameC σ)` of the un-renamed resume
     = `(renameK σ (Kᵢ ++ handleF n (custom ℓ p cl) :: Kₒ),
         renameC σ (Comp.subst p (Comp.subst (Val.shift v) clause.2)))`
The stacks commute (`renameK_append`/`renameK_cons`/`renameF_handleF`). The FOCI agree IFF
  `renameC σ (Comp.subst p (Comp.subst (Val.shift v) clause.2))`
    = `Comp.subst (renameV σ p) (Comp.subst (Val.shift (renameV σ v)) (renameC σ clause.2))`
  AND `renameV σ p = p`, `renameC σ clause.2 = clause.2`
(because `renameH` did NOT rename p/cl). `renameV`/`renameC` are identity on a term with NO
`vcap` (the ONLY thing rename touches, LR.lean:452). So the commutation holds IFF `p` and every
clause body are `vcap`-FREE — which every ELABORATED custom clause IS (params/clauses are closed
source values; caps only enter via `handle`-mint at runtime, never inside a clause literal).

RENAME LEMMA FAMILY: joins `renameV`/`renameC`/`renameH`/`renameK` (LR.lean:452-488) and the
`renameC σ (Comp.subst …) = Comp.subst (renameV σ …) …` commutation family (`renameC_subst`-style).

TWO ROUTES (the grind picks one — this is the ADR-input fork):
  (R-1) VcapFree side condition. Define `Val.VcapFree`/`Comp.VcapFree`; prove `VcapFree t →
        renameV/C σ t = t`; thread `VcapFree p ∧ ∀ c ∈ cl, VcapFree c.2` through `dispatchOn_rename`
        (and its callers `idDispatch_rename`/`step`-rename keystone). SMALL new predicate (~2 defs
        + 2 identity lemmas), but the side condition RIPPLES up to the rename keystone's callers.
  (R-2) Make `renameH` TRAVERSE custom (rename p + map-rename clause bodies). Then the commutation
        is the structural `renameC_subst` twin. Cost = the ~15-lemma renameH/renameCls mutual
        cascade (nested-inductive termination, the `capsCls` twin) the PATH ledger already names
        (line 76-79) as "this path's re-index shape". BIGGER but removes the side condition
        globally and is the honest fix.
RECOMMENDATION: R-1 for Stage 5 (the side condition is TRUE by elaboration and small); R-2 is the
◊5+ clean-up. The PATH already banks R-2 as the eventual shape. -/
example : True := trivial   -- (debt 3 is a source-site sorry in LR.lean; nothing to restate here)

end -- public section
end Bang.Stage5Probe
