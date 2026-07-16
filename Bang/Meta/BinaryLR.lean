-- Compat is a proof module UPSTREAM of Spec (sibling to Metatheory): Spec wires its frozen
-- `lr_fundamental`/`lr_sound` statements to the proofs assembled here (`:= lr_fundamental_proof`,
-- exactly as `preservation := preservation_proof`). So we import the DEFINITION layers, not Spec
-- (importing Spec would cycle once Spec imports Compat). Verified no cycle: Metatheory imports only
-- Core/Syntax/Operational; LR adds the relations; neither imports Spec.
module

public import Bang.Core.IR
public import Bang.Core.Typing
public import Bang.Core.Semantics
public import Bang.Meta.LR
public import Bang.Core.Soundness

/-!
  Compat.lean — the Phase-B target list.
  `lr_fundamental` (Spec.lean) = induction over the typing derivation, one case
  per rule, each discharged by the matching lemma below. Proving all of these
  (in PROOF_ORDER) IS proving the fundamental theorem.

-/

namespace Bang

open Bang.EffectRow (Label)

-- Module reveal (Phase 1a). `@[expose] public section`: Compat's compatibility lemmas
-- (the STD compat block, KrelS/CrelK machinery) are unfolded by downstream Spec, so
-- bodies cross the boundary. Zero-external-ref proof-term lemmas → `private` (deferred).
@[expose] public section

variable {Eff  : Type} [Lattice Eff] [OrderBot Eff]
variable {Mult : Type} [CommSemiring Mult] [DecidableEq Mult]
variable [EffSig Eff Mult]


/-! ## B.0 Convergence anti-reduction infrastructure (the workhorse)

The fundamental theorem proves `Crel n B e c c` — a computation relates to ITSELF, but observed
through `Krel`-RELATED (not equal) stacks `K₁,K₂`. So each compat lemma is a CONGRUENCE: relatedness
of stacks lifts through the same head former. The biorthogonal relations are phrased over
fuel-bounded convergence (`CoApprox`/`Converges`), so the workhorse is a CONFIG-LEVEL anti-reduction:

  shape: pitts-step-indexed-biorthogonality / benton-hur-icfp09 — head-expansion closure.

A *context-independent head step* `c ↦ c'` (one that fires `step (K, c) = some (K, c')` for EVERY
stack `K`, e.g. `force (vthunk M) ↦ M`, `case (inl v) … ↦ N₁[v]`) makes `(K, c)` and `(K, c')`
co-converge with a ±1 fuel offset. The PUSH steps (`letC`/`app`/`handle`) are the other shape: they
move a frame onto the stack (`step (K, letC M N) = (letF N :: K, M)`), so `(K, plug-form)` reduces to
the focused subterm under an extended stack — handled by `Stack.plug` unfolding directly. -/

/-- A returned config converges iff its tail does, after one bind step — but the universal workhorse
is: a config that takes a fixed first step `(K,c) ↦ cfg'` converges iff `cfg'` does. -/
theorem converges_cfg_step (cfg cfg' : Config)
    (hstep : Source.step cfg = some cfg')
    (hne : ∀ g v, cfg ≠ (g, [], Comp.ret v)) :
    (∃ n w, Config.run n cfg = Result.done w) ↔ (∃ n w, Config.run n cfg' = Result.done w) := by
  constructor
  · rintro ⟨n, w, hn⟩
    cases n with
    | zero => simp [Config.run] at hn
    | succ m =>
        rw [Config.run_step m cfg hne, hstep] at hn
        exact ⟨m, w, hn⟩
  · rintro ⟨n, w, hn⟩
    refine ⟨n + 1, w, ?_⟩
    rw [Config.run_step n cfg hne, hstep]
    exact hn

/-- A *context-independent head step*: `c ↦ c'` fires under EVERY stack, and `c` is never a bare
returned focus (`ret v` would be terminal, not a redex). The non-PUSH reductions
(`force (vthunk M) ↦ M`, the ADT eliminators) have this shape: they rewrite the focus in place
without consulting the stack. -/
def CIStep (c c' : Comp) : Prop :=
  (∀ (g : Nat) (K : Stack), Source.step (g, K, c) = some (g, K, c')) ∧ (∀ v, c ≠ Comp.ret v)

-- NOTE (inc-5): the `converges_plug_step`/`converges_letF_ret`/`converges_appF_lam`/
-- `converges_handleF_ret` frame-reduce bridges were DELETED. They bridged through the old
-- `converges_plug_iff` (RHS = the raw `(K, c)` config), which LR rekeyed to the machine-shaped
-- reshape config (`handlerCount K, canonStack K c, capSubstInto K c`, ADR-0054/0055); the bridges had
-- zero consumers (the fundamental theorem now goes through the machine-shaped `KrelS`, not these
-- convergence bridges). `converges_cfg_step` (the general config-level head-step anti-reduction) and
-- `CIStep` (the context-independent head-step predicate, used by `CrelK_head_step`) are retained.

/-! ## B.1 The environment relation `EnvRel` / closing substitutions

`EnvRel`, `closeC`, `closeV` are defined in `Bang/LR.lean` (§5.2b) — they are LR machinery the FROZEN
`lr_fundamental` statement (`Spec.lean`, ADR-0034 env-closed form) references, so they must live in a
module `Spec.lean` imports. The fundamental theorem closes an OPEN sub-term over a pair of
`Vrel`-RELATED substitution environments δ₁,δ₂ (Biernacki/Ahmed `G⟦Γ⟧`): the bare `c c` self-relation
is unprovable for open `c` (a `vvar i` is not `Vrel`-related to itself), so the induction invariant is
`EnvRel n Γ δ₁ δ₂ → Crel n B e (closeC δ₁ c) (closeC δ₂ c)`. -/

/-! ### B.1a–a″ `closeC`/`closeV` calculus — HOISTED to `Bang/Core/Semantics/Subst.lean` §1.3c

`shiftN`, `closeCUnderBinders`, the non-binding `closeC_*`/`closeV_*` distribution lemmas, the
closed-filler shift/subst commutation (`{Val,Comp,Handler}.shiftFrom_substFrom_closed`), `Val.ScopedIn`
+ `closeV_closed_scoped`/`closeV_vvar` are pure de-Bruijn machinery — hoisted (task #15), visible here
via `Core.Semantics` re-import. Only the `EnvRel`/`EnvRelK` accessors below (which consume the LR
relations) stay in this module. -/

/-! ### B.1a′ `EnvRel` accessors (closedness carrier, length, index)

The fundamental induction consumes the `EnvRel` carrier three ways: the fillers' CLOSEDNESS (feeds
`closeC_subst_comm` under binders), the LENGTH match with `Γ` (feeds `closeV_vvar`'s in-range
requirement), and the per-position `Vrel` (feeds the `vvar` leaf). All by induction on `Γ`/the lists. -/

/-- `EnvRel`'s left fillers are all closed (the `Val.Closed v₁` conjunct, harvested). -/
theorem EnvRel.closed_left {n : Nat} : ∀ {Γ : TyCtx Eff Mult} {δ₁ δ₂ : List Val},
    EnvRel n Γ δ₁ δ₂ → ∀ v ∈ δ₁, Val.Closed v
  | [],      [],        [],        _, v, hv => absurd hv (by simp)
  | _ :: Γ', v₁ :: δ₁', v₂ :: δ₂', h, v, hv => by
      rw [EnvRel] at h
      obtain ⟨hc₁, _, _, hrest⟩ := h
      rcases List.mem_cons.mp hv with rfl | hmem
      · exact hc₁
      · exact EnvRel.closed_left hrest v hmem

/-- `EnvRel`'s right fillers are all closed. -/
theorem EnvRel.closed_right {n : Nat} : ∀ {Γ : TyCtx Eff Mult} {δ₁ δ₂ : List Val},
    EnvRel n Γ δ₁ δ₂ → ∀ v ∈ δ₂, Val.Closed v
  | [],      [],        [],        _, v, hv => absurd hv (by simp)
  | _ :: Γ', v₁ :: δ₁', v₂ :: δ₂', h, v, hv => by
      rw [EnvRel] at h
      obtain ⟨_, hc₂, _, hrest⟩ := h
      rcases List.mem_cons.mp hv with rfl | hmem
      · exact hc₂
      · exact EnvRel.closed_right hrest v hmem

/-- `EnvRel` matches lengths: `δ₁.length = Γ.length` (and `δ₂`). -/
theorem EnvRel.length_left {n : Nat} : ∀ {Γ : TyCtx Eff Mult} {δ₁ δ₂ : List Val},
    EnvRel n Γ δ₁ δ₂ → δ₁.length = Γ.length
  | [],      [],        [],        _ => rfl
  | _ :: Γ', v₁ :: δ₁', v₂ :: δ₂', h => by
      rw [EnvRel] at h; simp only [List.length_cons]; rw [EnvRel.length_left h.2.2.2]
theorem EnvRel.length_right {n : Nat} : ∀ {Γ : TyCtx Eff Mult} {δ₁ δ₂ : List Val},
    EnvRel n Γ δ₁ δ₂ → δ₂.length = Γ.length
  | [],      [],        [],        _ => rfl
  | _ :: Γ', v₁ :: δ₁', v₂ :: δ₂', h => by
      rw [EnvRel] at h; simp only [List.length_cons]; rw [EnvRel.length_right h.2.2.2]

/-- The per-position `Vrel`: if `Γ[i]? = some A`, the `i`-th fillers are `Vrel n A`-related. -/
theorem EnvRel.vrel_at {n : Nat} : ∀ {Γ : TyCtx Eff Mult} {δ₁ δ₂ : List Val},
    EnvRel n Γ δ₁ δ₂ → ∀ {i : Nat} {A : VTy Eff Mult}, Γ[i]? = some A →
      ∀ (d₁ d₂ : Val), Vrel n A (δ₁[i]?.getD d₁) (δ₂[i]?.getD d₂)
  | [],      [],        [],        _, i, A, hΓ, _, _ => by simp at hΓ
  | A' :: Γ', v₁ :: δ₁', v₂ :: δ₂', h, i, A, hΓ, d₁, d₂ => by
      rw [EnvRel] at h
      obtain ⟨_, _, hv, hrest⟩ := h
      cases i with
      | zero => simp only [List.getElem?_cons_zero, Option.getD_some]
                simp only [List.getElem?_cons_zero, Option.some.injEq] at hΓ; subst hΓ; exact hv
      | succ k =>
          simp only [List.getElem?_cons_succ]
          simp only [List.getElem?_cons_succ] at hΓ
          exact EnvRel.vrel_at hrest hΓ d₁ d₂

/-! ◊4.5b `EnvRelK` helpers (mirror the `EnvRel` ones; the closed/length proofs are relation-agnostic,
`vrel_at` returns a `VrelK`). For the migrated `crelK_fund`/`vrelK_fund`. -/
theorem EnvRelK.closed_left {n : Nat} : ∀ {Γ : TyCtx Eff Mult} {δ₁ δ₂ : List Val},
    EnvRelK n Γ δ₁ δ₂ → ∀ v ∈ δ₁, Val.Closed v
  | [],      [],        [],        _, v, hv => absurd hv (by simp)
  | _ :: Γ', v₁ :: δ₁', v₂ :: δ₂', h, v, hv => by
      rw [EnvRelK] at h
      obtain ⟨hc₁, _, _, hrest⟩ := h
      rcases List.mem_cons.mp hv with rfl | hmem
      · exact hc₁
      · exact EnvRelK.closed_left hrest v hmem

theorem EnvRelK.closed_right {n : Nat} : ∀ {Γ : TyCtx Eff Mult} {δ₁ δ₂ : List Val},
    EnvRelK n Γ δ₁ δ₂ → ∀ v ∈ δ₂, Val.Closed v
  | [],      [],        [],        _, v, hv => absurd hv (by simp)
  | _ :: Γ', v₁ :: δ₁', v₂ :: δ₂', h, v, hv => by
      rw [EnvRelK] at h
      obtain ⟨_, hc₂, _, hrest⟩ := h
      rcases List.mem_cons.mp hv with rfl | hmem
      · exact hc₂
      · exact EnvRelK.closed_right hrest v hmem

theorem EnvRelK.length_left {n : Nat} : ∀ {Γ : TyCtx Eff Mult} {δ₁ δ₂ : List Val},
    EnvRelK n Γ δ₁ δ₂ → δ₁.length = Γ.length
  | [],      [],        [],        _ => rfl
  | _ :: Γ', v₁ :: δ₁', v₂ :: δ₂', h => by
      rw [EnvRelK] at h; simp only [List.length_cons]; rw [EnvRelK.length_left h.2.2.2]
theorem EnvRelK.length_right {n : Nat} : ∀ {Γ : TyCtx Eff Mult} {δ₁ δ₂ : List Val},
    EnvRelK n Γ δ₁ δ₂ → δ₂.length = Γ.length
  | [],      [],        [],        _ => rfl
  | _ :: Γ', v₁ :: δ₁', v₂ :: δ₂', h => by
      rw [EnvRelK] at h; simp only [List.length_cons]; rw [EnvRelK.length_right h.2.2.2]

theorem EnvRelK.vrel_at {n : Nat} : ∀ {Γ : TyCtx Eff Mult} {δ₁ δ₂ : List Val},
    EnvRelK n Γ δ₁ δ₂ → ∀ {i : Nat} {A : VTy Eff Mult}, Γ[i]? = some A →
      ∀ (d₁ d₂ : Val), VrelK n A (δ₁[i]?.getD d₁) (δ₂[i]?.getD d₂)
  | [],      [],        [],        _, i, A, hΓ, _, _ => by simp at hΓ
  | A' :: Γ', v₁ :: δ₁', v₂ :: δ₂', h, i, A, hΓ, d₁, d₂ => by
      rw [EnvRelK] at h
      obtain ⟨_, _, hv, hrest⟩ := h
      cases i with
      | zero => simp only [List.getElem?_cons_zero, Option.getD_some]
                simp only [List.getElem?_cons_zero, Option.some.injEq] at hΓ; subst hΓ; exact hv
      | succ k =>
          simp only [List.getElem?_cons_succ]
          simp only [List.getElem?_cons_succ] at hΓ
          exact EnvRelK.vrel_at hrest hΓ d₁ d₂


/-! ### B.1b–d Closing-substitution descent — HOISTED to `Bang/Core/Semantics/Subst.lean` §1.3c

The binding-former `closeC` distribution (`closeC_letC`/`closeC_lam`/`closeC_case`/`closeC_split`), the
substitution-swap engines (`{Val,Comp,Handler}.substFrom_swap_closed` + the non-adjacent `_ge` family),
and the substitution-descent crux (`closeC_subst_comm`/`closeCUnderBinders_subst0`/`closeC_subst2_comm`)
are pure de-Bruijn machinery — hoisted to the substitution foundation (task #15). Available here via
`Core.Semantics` re-import. -/

/-! ## B.3′ ◊4.5b sub-block (c) — `CrelK` head-step + value lemmas (the answer-typed migration)

The `CrelK` analogues of `Crel_head_step`/`crel_force`/`crel_unfold`, over the answer-typed `KrelS`.
`CrelK_head_step` is the generic `▷`-anti-reduction: a context-independent `CIStep` on both sides
reduces `CrelK n` to the reducts related at every `m < n` (the metered `▷`). Uses `KrelS_mono` (the
sub-block b downward-closure) where the old one used `Krel_mono`. -/

/-- ◊4.5b `▷`-guarded head-expansion of `CrelK` over the metered observation (the `KrelS` analogue of
`Crel_head_step`). A context-independent head-step on both sides reduces `CrelK n` to the reducts
related at every `m < n`. -/
theorem CrelK_head_step {n : Nat} {B : CTy Eff Mult} {e : Eff} {c₁ c₁' c₂ c₂' : Comp}
    (h₁ : CIStep c₁ c₁') (h₂ : CIStep c₂ c₂')
    (hlater : ∀ m, m < n → CrelK m B e c₁' c₂') : CrelK n B e c₁ c₂ := by
  rw [CrelK]; intro g D K₁ K₂ hK hconv
  have hstep₁ : Source.step (g, K₁, c₁) = some (g, K₁, c₁') :=
    h₁.1 g K₁
  have hne₁ : ∀ g' v, (g, K₁, c₁) ≠ (g', [], Comp.ret v) := by intro g' v; simp [h₁.2 v]
  cases n with
  | zero => exact absurd hconv (not_convergesC_le_zero _)
  | succ k =>
      rw [convergesC_le_step hstep₁ hne₁] at hconv
      have hCk : CrelK k B e c₁' c₂' := hlater k (Nat.lt_succ_self k)
      rw [CrelK] at hCk
      have hKk : KrelS k B D e g K₁ K₂ := KrelS_mono (Nat.le_succ k) hK
      have hstep₂ : Source.step (g, K₂, c₂) = some (g, K₂, c₂') :=
        h₂.1 g K₂
      have hne₂ : ∀ g' v, (g, K₂, c₂) ≠ (g', [], Comp.ret v) := by intro g' v; simp [h₂.2 v]
      exact converges_anti_step hstep₂ hne₂ (hCk g D K₁ K₂ hKk hconv)

/-- ◊4.5b `force` of `VrelK`-related thunks. The U-clause is `∀ j < n, CrelK j` — exactly the `m < n`
reducts `CrelK_head_step` consumes (cleaner than the old `∀ j ≤ n` + `le_of_lt`). -/
theorem crelK_force {n : Nat} {φ : Eff} {B : CTy Eff Mult} {w₁ w₂ : Val}
    (hv : VrelK n (VTy.U φ B) w₁ w₂) : CrelK n B φ (Comp.force w₁) (Comp.force w₂) := by
  rw [VrelK] at hv
  obtain ⟨c₁, c₂, rfl, rfl, hc⟩ := hv
  refine CrelK_head_step (c₁' := c₁) (c₂' := c₂) ?_ ?_ (fun m hm => hc m hm)
  · exact ⟨fun _ _ => rfl, by intro v; simp⟩
  · exact ⟨fun _ _ => rfl, by intro v; simp⟩

/-- ◊4.5b `unfold` of `VrelK`-related μ-values. `unfold (fold u) ↦ ret u` (CIStep); the ▷-head-step
needs `CrelK m (ret u₁) (ret u₂)` at each `m < n`, from `crelK_ret` on the μ-payload. -/
theorem crelK_unfold {n : Nat} {A : VTy Eff Mult} {e : Eff} {w₁ w₂ : Val}
    (hcw₁ : Val.Closed w₁) (hcw₂ : Val.Closed w₂) (hv : VrelK n (VTy.mu A) w₁ w₂) :
    CrelK n (CTy.F 1 (VTy.unrollMu A)) e (Comp.unfold w₁) (Comp.unfold w₂) := by
  rw [VrelK] at hv
  obtain ⟨u₁, u₂, rfl, rfl, hu⟩ := hv
  refine CrelK_head_step (c₁' := Comp.ret u₁) (c₂' := Comp.ret u₂) ?_ ?_ ?_
  · exact ⟨fun _ _ => rfl, by intro v; simp⟩
  · exact ⟨fun _ _ => rfl, by intro v; simp⟩
  · -- ROUTE-1: `crelK_ret` gives the unfolded `CrelK` body at a specific `g`/observation context, so
    -- unfold `CrelK m` and discharge per-config. Hole type `F 1 (unrollMu A)` (q = 1).
    intro m hm
    rw [CrelK]; intro g D K₁ K₂ hK
    exact crelK_ret g D K₁ K₂ hK hcw₁.fold_inv hcw₂.fold_inv (hu m hm)


/-! ### B.3′b `CrelK` frame extensions + `compat` cores (`letC`/`app`)

The answer-typed frame lemmas. `krelS_letF_intro` builds a `KrelS (F q A)` from a `▷`-guarded
continuation relation + a tail `KrelS B` — directly packing the def's letF clause (the tail weakens
from the ambient `ε` to the continuation row `φ` via `KrelS_eff_anti`, `φ ≤ ε`). `compatK_letC`/`_app`
refocus the source redex (`letC`/`app` PUSH) and run the bound computation through the extended stack. -/

/-- ◊4.5b build a letF-extended `KrelS` from a continuation relation (`▷`-guarded, `∀ m < n`) + the
ambient tail. The continuation row `φ ≤ ε`; the tail weakens `ε → φ` via `KrelS_eff_anti`. -/
theorem krelS_letF_intro {n : Nat} {q : Mult} {A : VTy Eff Mult} {B D : CTy Eff Mult} {ε φ : Eff}
    {g : Nat} {N₁ N₂ : Comp} {K₁ K₂ : Stack} (hφε : φ ≤ ε)
    (hN : ∀ m, m < n → ∀ v₁ v₂, Val.Closed v₁ → Val.Closed v₂ →
      VrelK m A v₁ v₂ →
      CrelK m B φ (Comp.subst v₁ N₁) (Comp.subst v₂ N₂))
    (hK : KrelS n B D ε g K₁ K₂) :
    KrelS n (CTy.F q A) D ε g (Frame.letF N₁ :: K₁) (Frame.letF N₂ :: K₂) := by
  rw [krelS_letF]
  exact ⟨q, A, B, φ, rfl, hN, KrelS_eff_anti hφε hK⟩

/-- ◊4.5b the `letC` compat core at `CrelK` (the answer-typed `compat_letC`). REFOCUS
`(K, letC M N) ↦ (letF N::K, M)` (one PUSH step), then run `M` (related at `F q1 A`, row φ₁) through the
letF-extended stack, shown `KrelS`-related by `krelS_letF_intro`. The continuation `hN` is `▷`-guarded
(`∀ m < n`) at row φ₂; the block is at `φ₁ ⊔ φ₂`. -/
theorem compatK_letC {n : Nat} {q1 : Mult} {A : VTy Eff Mult} {B : CTy Eff Mult} {φ₁ φ₂ : Eff}
    {M₁ M₂ N₁' N₂' : Comp}
    (hM : CrelK n (CTy.F q1 A) φ₁ M₁ M₂)
    (hN : ∀ m, m < n → ∀ v₁ v₂, Val.Closed v₁ → Val.Closed v₂ →
      VrelK m A v₁ v₂ →
      CrelK m B φ₂ (Comp.subst v₁ N₁') (Comp.subst v₂ N₂')) :
    CrelK n B (φ₁ ⊔ φ₂) (Comp.letC M₁ N₁') (Comp.letC M₂ N₂') := by
  rw [CrelK]
  intro g D K₁ K₂ hK
  refine coApproxC_le_reduce
    (cfg₁' := (g, Frame.letF N₁' :: K₁, M₁))
    (cfg₂' := (g, Frame.letF N₂' :: K₂, M₂))
    rfl (by intro g' u; simp) rfl (by intro g' u; simp) ?_
  -- the letF-extended stack is `KrelS`-related at `(F q1 A, φ₁)`: tail at the block row φ₁⊔φ₂ weakens
  -- to the continuation row φ₂ (≤ φ₁⊔φ₂); `hM` (related at F q1 A, row φ₁) discharges the reduct.
  have hKletF : KrelS n (CTy.F q1 A) D (φ₁ ⊔ φ₂) g (Frame.letF N₁' :: K₁) (Frame.letF N₂' :: K₂) :=
    krelS_letF_intro le_sup_right hN hK
  rw [CrelK] at hM
  -- `hM` is at row φ₁; the letF-extended stack is at φ₁⊔φ₂. Weaken the stack φ₁⊔φ₂ → φ₁ (antitone).
  exact hM g D (Frame.letF N₁' :: K₁) (Frame.letF N₂' :: K₂) (KrelS_eff_anti le_sup_left hKletF)

/-- ◊4.5b build an appF-extended `KrelS` from a `VrelK`-related closed argument + the codomain tail.
The appF frame doesn't bind a continuation row, so the tail stays at the ambient `ε` (no weakening). -/
theorem krelS_appF_intro {n : Nat} {q : Mult} {A : VTy Eff Mult} {B D : CTy Eff Mult} {ε : Eff}
    {g : Nat} {v₁ v₂ : Val} {K₁ K₂ : Stack} (hcv₁ : Val.Closed v₁) (hcv₂ : Val.Closed v₂)
    (hv : VrelK n A v₁ v₂) (hK : KrelS n B D ε g K₁ K₂) :
    KrelS n (CTy.arr q A B) D ε g (Frame.appF v₁ :: K₁) (Frame.appF v₂ :: K₂) := by
  rw [krelS_appF]
  exact ⟨q, A, B, rfl, hcv₁, hcv₂, hv, hK⟩

/-- ◊4.5b the `app` compat core at `CrelK` (the answer-typed `compat_app`). REFOCUS
`(K, app M v) ↦ (appF v::K, M)`, then run `M` (related at `arr q A B`) through the appF-extended
stack, shown `KrelS`-related by `krelS_appF_intro`. -/
theorem compatK_app {n : Nat} {q : Mult} {A : VTy Eff Mult} {B : CTy Eff Mult} {φ : Eff}
    {M₁ M₂ : Comp} {v₁ v₂ : Val}
    (hM : CrelK n (CTy.arr q A B) φ M₁ M₂)
    (hcv₁ : Val.Closed v₁) (hcv₂ : Val.Closed v₂)
    (hv : VrelK n A v₁ v₂) :
    CrelK n B φ (Comp.app M₁ v₁) (Comp.app M₂ v₂) := by
  rw [CrelK]
  intro g D K₁ K₂ hK
  refine coApproxC_le_reduce
    (cfg₁' := (g, Frame.appF v₁ :: K₁, M₁))
    (cfg₂' := (g, Frame.appF v₂ :: K₂, M₂))
    rfl (by intro g' u; simp) rfl (by intro g' u; simp) ?_
  rw [CrelK] at hM
  exact hM g D (Frame.appF v₁ :: K₁) (Frame.appF v₂ :: K₂) (krelS_appF_intro hcv₁ hcv₂ hv hK)

/-- ◊4.5b the `lam` compat core at `CrelK` (the answer-typed `compat_lam`). A `lam` only β-reduces under
an `appF` frame; other stacks are STUCK on a `lam` (observation vacuous). Stack induction: appF-headed
β-reduces `(appF w::K', lam M') ↦ (K', M'.subst w)`, the body IH discharges; nil/letF are stuck on a
`lam`; handleF passes the lam through (`handleF h::K, lam M` is STUCK too — handleF only reduces a
`ret`). So only the appF case is non-vacuous. -/
theorem compatK_lam {n : Nat} {q : Mult} {A : VTy Eff Mult} {B : CTy Eff Mult} {φ : Eff}
    {M₁' M₂' : Comp}
    (hbody : ∀ w₁ w₂, Val.Closed w₁ → Val.Closed w₂ →
      VrelK n A w₁ w₂ → CrelK n B φ (Comp.subst w₁ M₁') (Comp.subst w₂ M₂')) :
    CrelK n (CTy.arr q A B) φ (Comp.lam M₁') (Comp.lam M₂') := by
  rw [CrelK]
  intro g D K₁ K₂ hK
  cases K₁ with
  | nil =>
      -- nil arrow: `([], lam M)` is STUCK (lam reduces only under appF). Vacuous.
      intro hconv; exact absurd hconv (not_convergesC_le_of_stuck rfl (by intro g' u; simp))
  | cons fr K₁' =>
      cases fr with
      | appF w₁ =>
          cases K₂ with
          | cons fr₂ K₂' =>
              cases fr₂ with
              | appF w₂ =>
                  rw [krelS_appF] at hK
                  obtain ⟨q', A', B', hC, hcw₁, hcw₂, hw, htail⟩ := hK
                  rw [CTy.arr.injEq] at hC; obtain ⟨rfl, rfl, rfl⟩ := hC
                  -- β `(appF w::K', lam M') ↦ (K', M'.subst w)`; body IH at the SAME index, non-dropping.
                  refine coApproxC_le_reduce
                    (cfg₁' := (g, K₁', Comp.subst w₁ M₁'))
                    (cfg₂' := (g, K₂', Comp.subst w₂ M₂'))
                    rfl (by intro g' u; simp) rfl (by intro g' u; simp) ?_
                  have hb := hbody w₁ w₂ hcw₁ hcw₂ hw
                  rw [CrelK] at hb
                  exact hb g D K₁' K₂' htail
              | _ => simp only [KrelS] at hK
          | nil => simp only [KrelS] at hK
      | letF N₁ =>
          -- letF arrow: the clause requires `C = F q A`, but `C = arr q A B` (arr ≠ F) ⇒ False.
          cases K₂ with
          | cons fr₂ K₂' =>
              cases fr₂ with
              | letF N₂ => rw [krelS_letF] at hK; obtain ⟨_, _, _, _, hC, _⟩ := hK; exact absurd hC (by simp)
              | _ => simp only [KrelS] at hK
          | nil => simp only [KrelS] at hK
      | handleF h₁ =>
          -- handleF on a `lam`: `(handleF h::K, lam M)` is STUCK (handleF reduces only a `ret`). Vacuous.
          intro hconv; exact absurd hconv (not_convergesC_le_of_stuck rfl (by intro g' u; simp))

/-- ◊4.5b the `case` (sum elim) compat core at `CrelK`. `case (inl u) ↦ N₁[u]` / `case (inr u) ↦ N₂[u]`
are CISteps; the ▷-head-step needs the chosen branch related at every `m < n`, from the matching branch
IH on the `VrelK m`-related payload (the sum scrutinee gives the tag + payload). -/
theorem compatK_case {n : Nat} {A B : VTy Eff Mult} {C : CTy Eff Mult} {φ : Eff}
    {w₁ w₂ : Val} {N₁₁ N₂₁ N₁₂ N₂₂ : Comp}
    (hw : VrelK n (VTy.sum A B) w₁ w₂) (hcw₁ : Val.Closed w₁) (hcw₂ : Val.Closed w₂)
    (hN₁ : ∀ m, m < n → ∀ v₁ v₂, Val.Closed v₁ → Val.Closed v₂ →
      VrelK m A v₁ v₂ →
      CrelK m C φ (Comp.subst v₁ N₁₁) (Comp.subst v₂ N₁₂))
    (hN₂ : ∀ m, m < n → ∀ v₁ v₂, Val.Closed v₁ → Val.Closed v₂ →
      VrelK m B v₁ v₂ →
      CrelK m C φ (Comp.subst v₁ N₂₁) (Comp.subst v₂ N₂₂)) :
    CrelK n C φ (Comp.case w₁ N₁₁ N₂₁) (Comp.case w₂ N₁₂ N₂₂) := by
  rw [VrelK] at hw
  rcases hw with ⟨u₁, u₂, rfl, rfl, hu⟩ | ⟨u₁, u₂, rfl, rfl, hu⟩
  · refine CrelK_head_step (c₁' := Comp.subst u₁ N₁₁) (c₂' := Comp.subst u₂ N₁₂) ?_ ?_
      (fun m hm => hN₁ m hm u₁ u₂ hcw₁.inl_inv hcw₂.inl_inv (VrelK_mono (le_of_lt hm) hu))
    · exact ⟨fun _ _ => rfl, by intro v; simp⟩
    · exact ⟨fun _ _ => rfl, by intro v; simp⟩
  · refine CrelK_head_step (c₁' := Comp.subst u₁ N₂₁) (c₂' := Comp.subst u₂ N₂₂) ?_ ?_
      (fun m hm => hN₂ m hm u₁ u₂ hcw₁.inr_inv hcw₂.inr_inv (VrelK_mono (le_of_lt hm) hu))
    · exact ⟨fun _ _ => rfl, by intro v; simp⟩
    · exact ⟨fun _ _ => rfl, by intro v; simp⟩

/-- ◊4.5b the `split` (product elim) compat core at `CrelK`. `split (pair a b) N ↦ N[a][shift b]` is a
CIStep; the ▷-head-step needs the two-binder body related at every `m < n`. -/
theorem compatK_split {n : Nat} {A B : VTy Eff Mult} {C : CTy Eff Mult} {φ : Eff}
    {w₁ w₂ : Val} {N₁' N₂' : Comp}
    (hw : VrelK n (VTy.prod A B) w₁ w₂) (hcw₁ : Val.Closed w₁) (hcw₂ : Val.Closed w₂)
    (hN : ∀ m, m < n → ∀ a₁ a₂ b₁ b₂, Val.Closed a₁ → Val.Closed a₂ → Val.Closed b₁ → Val.Closed b₂ →
      VrelK m A a₁ a₂ → VrelK m B b₁ b₂ →
      CrelK m C φ (Comp.subst a₁ (Comp.subst (Val.shift b₁) N₁'))
                  (Comp.subst a₂ (Comp.subst (Val.shift b₂) N₂'))) :
    CrelK n C φ (Comp.split w₁ N₁') (Comp.split w₂ N₂') := by
  rw [VrelK] at hw
  obtain ⟨a₁, a₂, b₁, b₂, rfl, rfl, ha, hb⟩ := hw
  obtain ⟨hca₁, hcb₁⟩ := hcw₁.pair_inv
  obtain ⟨hca₂, hcb₂⟩ := hcw₂.pair_inv
  refine CrelK_head_step
    (c₁' := Comp.subst a₁ (Comp.subst (Val.shift b₁) N₁'))
    (c₂' := Comp.subst a₂ (Comp.subst (Val.shift b₂) N₂')) ?_ ?_
    (fun m hm => hN m hm a₁ a₂ b₁ b₂ hca₁ hca₂ hcb₁ hcb₂
      (VrelK_mono (le_of_lt hm) ha) (VrelK_mono (le_of_lt hm) hb))
  · exact ⟨fun _ _ => rfl, by intro v; simp⟩
  · exact ⟨fun _ _ => rfl, by intro v; simp⟩


/-! ### B.3′c ◊4.5b sub-block (f) — handler-frame `KrelS` intro + `compatK_handle*` cores

The answer-typed analogues of the old `krel_handleF*`/`compat_handle*`. The new `KrelS` has NO stuck-half
(`Srel` is gone — the op-stuck behaviour lives in `CrelK`'s biorthogonality, not the stack relation), so
the handler-frame intro is TRIVIAL: `krelS_handleF` says `KrelS …ε (handleF h::K) ↔ KrelS …ε K`, and the
ROW-DISCHARGE (body row `e` ⊋ discharged row `φ`) is `KrelS_eff_cast` (ε is inert in `KrelS`). This is the
SINGLE-ROW close of the original ◊4.5b wall — no two-row Biernacki `C⟦τ₁/ε₁{τ₂/ε₂⟧` needed (the row only
gated the dropped `Srel`). shape: biernacki-popl18 §5.4 set-row ρ-free collapse. -/

/-- ◊4.5b-append build a handleF-extended `KrelS` from a SELF-`HandlerRel` witness + the discharged-row
tail + the Kᵢ-threading RESUME CONJUNCT. The body row `e` is arbitrary w.r.t. `φ` (`KrelS_eff_cast`).
The conjunct (dispatched-config co-convergence at `m < n`, threading the captured continuation `Kᵢ~Kᵢ'`)
is SUPPLIED by the caller — throws via `crelK_ret` on the tail (zero-shot); state/txn via the resume
relation through `Kᵢ`. -/
theorem krelS_handleF_intro {n : Nat} {nh : Nat} {C D : CTy Eff Mult} {e φ : Eff} {g : Nat} {h₁ h₂ : Handler}
    {K₁ K₂ : Stack} (hHR : HandlerRel Eff Mult n h₁ h₂) (hK : KrelS n C D φ g K₁ K₂)
    (hres : ∀ m, m < n → ∀ (op : OpId) (w₁ w₂ : Val) (Cᵢ : CTy Eff Mult) (εᵢ : Eff)
              (Kᵢ Kᵢ' : Stack) (cfg₁ cfg₂ : EvalCtx × Comp),
        Bang.handlesOp h₁ h₁.label op = true →
        Val.Closed w₁ → Val.Closed w₂ →
        (∀ Aop, EffSig.opArg (Eff := Eff) (Mult := Mult) h₁.label op = some Aop → VrelK m Aop w₁ w₂) →
        KrelS m Cᵢ C εᵢ g Kᵢ Kᵢ' →
        (∀ Aᵣ, EffSig.opRes (Eff := Eff) (Mult := Mult) h₁.label op = some Aᵣ →
          ∃ qᵣ, Cᵢ = CTy.F qᵣ Aᵣ) →
        Bang.dispatchOn nh op w₁ (Kᵢ, h₁, K₁) = some cfg₁ →
        Bang.dispatchOn nh op w₂ (Kᵢ', h₂, K₂) = some cfg₂ →
        (∃ (qᵣ : Mult) (Aᵣ : VTy Eff Mult) (r₁ r₂ : Val) (Sᵢ Sᵢ' : Stack) (eₛ : Eff),
            cfg₁ = (Sᵢ, Comp.ret r₁) ∧ cfg₂ = (Sᵢ', Comp.ret r₂) ∧
            Val.Closed r₁ ∧ Val.Closed r₂ ∧ VrelK m Aᵣ r₁ r₂ ∧
            KrelS m (CTy.F qᵣ Aᵣ) D eₛ g Sᵢ Sᵢ')) :
    KrelS n C D e g (Frame.handleF nh h₁ :: K₁) (Frame.handleF nh h₂ :: K₂) := by
  rw [krelS_handleF]; exact ⟨rfl, hHR, KrelS_eff_cast hK, hres⟩

/-- ◊4.5b-append DISPATCH-APPEND structural fact. `dispatchOn` over an outer stack `Kₒ ++ T` produces
the SAME config as over `Kₒ`, with `T` appended to the result's outer stack. Uniform across all handler
kinds: throws returns `(Kₒ, ret v)` ⇒ `(Kₒ ++ T, ret v)`; state/txn reinstall over `Kᵢ ++ reinstall :: Kₒ`
⇒ `Kᵢ ++ reinstall :: (Kₒ ++ T) = (Kᵢ ++ reinstall :: Kₒ) ++ T`. Proven by `cases` on the handler then
`cases` on the op-string decisions. (Note: this is the structural half; it does NOT make the OPAQUE
`CoApproxC_le` resume conjunct compose under append — see the wall comment at `krelS_append`'s handleF
case.) -/
theorem dispatchOn_append_outer (n : Nat) (op : OpId) (v : Val) (Kᵢ : Stack) (hh : Handler) (Kₒ T : Stack)
    {cfg : EvalCtx × Comp} (hd : Bang.dispatchOn n op v (Kᵢ, hh, Kₒ) = some cfg) :
    Bang.dispatchOn n op v (Kᵢ, hh, Kₒ ++ T) = some (cfg.1 ++ T, cfg.2) := by
  cases hh with
  | throws _ =>
      simp only [dispatchOn] at hd ⊢
      obtain rfl := (Option.some.injEq _ _).mp hd.symm; rfl
  | state ℓ' s =>
      simp only [dispatchOn] at hd ⊢
      by_cases hop : op == "get" <;> simp only [hop, if_true, if_false, Bool.false_eq_true] at hd ⊢ <;>
        (obtain rfl := (Option.some.injEq _ _).mp hd.symm; simp [List.append_assoc])
  | transaction ℓ' Θ =>
      simp only [dispatchOn] at hd ⊢
      by_cases h1 : op == "newTVar"
      · simp only [h1, if_true] at hd ⊢
        obtain rfl := (Option.some.injEq _ _).mp hd.symm; simp [List.append_assoc]
      · by_cases h2 : op == "readTVar"
        · simp only [h1, h2, if_true, if_false, Bool.false_eq_true] at hd ⊢
          obtain rfl := (Option.some.injEq _ _).mp hd.symm; simp [List.append_assoc]
        · simp only [h1, h2, if_false, Bool.false_eq_true] at hd ⊢
          cases v <;>
            (simp only [] at hd ⊢; obtain rfl := (Option.some.injEq _ _).mp hd.symm;
             simp [List.append_assoc])
  | custom ℓ' p cl =>
      -- custom (ADR-0085 stage 2, ADR-0087 finite rep): ONE-SHOT resume reinstalls over `Kᵢ ++ custom :: Kₒ`,
      -- the SAME append shape as state/txn — appending `T` to the outer stack commutes with the reinstall.
      simp only [dispatchOn] at hd ⊢
      cases hcl : cl.find? (·.1 == op) with
      | none => simp only [hcl, reduceCtorEq] at hd
      | some clause =>
          simp only [hcl] at hd ⊢
          obtain rfl := (Option.some.injEq _ _).mp hd.symm; simp [List.append_assoc]

/-- ◊4.5b-strengthen the krel-carrying resume CONCLUSION → `CoApproxC_le`. The strengthened handleF
resume conjunct concludes a DECOMPOSITION `cfgⱼ = (Sᵢ, ret rⱼ)` with `r₁~r₂` (VrelK) + `Sᵢ~Sᵢ'` (KrelS
at a returner hole). `crelK_ret` on the returned values, instantiated at the related stacks, recovers the
plain `CoApproxC_le m cfg₁ cfg₂`. This is the T=[] consumer; the nested case appends a tail to `Sᵢ` first
(via `krelS_append`) then runs the SAME `crelK_ret`. -/
-- ADR-0058 ROUTE-1: the `crelK_ret` consumer, now at the THREADED counter `g`. NO density premises —
-- both resume-decomposition configs observe at the SAME `g` (dispatch/reinstall preserves the counter),
-- so `crelK_ret` (route-1 form) bridges the decomposition directly, no `Canonical`/`CapsBelow`/`run_bump`.
theorem coApproxC_le_of_resumeDecomp {m : Nat} {qᵣ : Mult} {Aᵣ : VTy Eff Mult} {D : CTy Eff Mult}
    {g : Nat} {r₁ r₂ : Val} {Sᵢ Sᵢ' : Stack} {eₛ : Eff}
    (hcr₁ : Val.Closed r₁) (hcr₂ : Val.Closed r₂) (hr : VrelK m Aᵣ r₁ r₂)
    (hS : KrelS m (CTy.F qᵣ Aᵣ) D eₛ g Sᵢ Sᵢ') :
    CoApproxC_le m (g, Sᵢ, Comp.ret r₁) (g, Sᵢ', Comp.ret r₂) :=
  crelK_ret g D Sᵢ Sᵢ' hS hcr₁ hcr₂ hr

/-- ◊4.5b-strengthen `HandlerRel` DOWNWARD-CLOSURE — the relational handler condition is monotone in its
`VrelK`-stored state (state: one cell; transaction: pointwise heap; throws: index-independent label). The
inlined form lives in `KrelS_mono`'s handleF case; extracted here for the `krelS_append` index-drop. -/
theorem HandlerRel_mono {n m : Nat} {h₁ h₂ : Handler} (hmn : m ≤ n)
    (hh : HandlerRel Eff Mult n h₁ h₂) : HandlerRel Eff Mult m h₁ h₂ := by
  cases h₁ <;> cases h₂ <;> simp only [HandlerRel] at hh ⊢
  case state.state => exact ⟨hh.1, hh.2.imp fun _ hv => VrelK_mono hmn hv⟩
  case throws.throws => exact hh
  case transaction.transaction => exact ⟨hh.1, hh.2.1, fun i hi => VrelK_mono hmn (hh.2.2 i hi)⟩
  all_goals exact ⟨hh.1, hh.2.1, hh.2.2.imp fun _ hpv => ⟨VrelK_mono hmn hpv.1, hpv.2⟩⟩

/-- ◊4.5b-append `krelS_append` — the config-level Biernacki Lemma-2 analogue. Compose a related captured
continuation `Kᵢ ~ Kᵢ'` (answer type `Dᵢ`) with a related handleF-extended tail (`handleF h :: K`, hole
`Dᵢ`) into the appended stack `Kᵢ ++ handleF h :: K`. The inner `Kᵢ`'s answer type MUST equal the
reinstalled-handler frame's hole type `Dᵢ` (the resume value flows out of `Kᵢ` into the handler frame).
Proven by induction on `Kᵢ` (structural, like `crelK_ret`/`KrelS_mono`): nil = `krelS_handleF_intro`;
letF/appF peel + reconstruct over the appended tail. The handleF-in-`Kᵢ` sub-case (a handler NESTED in
the captured continuation) needs the resume-conjunct RELOCATED to the appended tail — same as the
decomp-miss-wrap; one documented sorry. shape: biernacki-popl18 §5.4 Lemma 2 (config-level append). -/
theorem krelS_append {m : Nat} {nh : Nat} {Cᵢ Dᵢ D' : CTy Eff Mult} {εᵢ e' : Eff} {g : Nat} {h₁ h₂ : Handler}
    {Kᵢ Kᵢ' K₁ K₂ : Stack}
    (hin : KrelS m Cᵢ Dᵢ εᵢ g Kᵢ Kᵢ')
    (hHR : HandlerRel Eff Mult m h₁ h₂)
    (htail : KrelS m Dᵢ D' e' g K₁ K₂)
    (hres : ∀ k, k < m → ∀ (op : OpId) (w₁ w₂ : Val) (Cⱼ : CTy Eff Mult) (εⱼ : Eff)
              (Kⱼ Kⱼ' : Stack) (cfg₁ cfg₂ : EvalCtx × Comp),
        Bang.handlesOp h₁ h₁.label op = true →
        Val.Closed w₁ → Val.Closed w₂ →
        (∀ Aop, EffSig.opArg (Eff := Eff) (Mult := Mult) h₁.label op = some Aop → VrelK k Aop w₁ w₂) →
        KrelS k Cⱼ Dᵢ εⱼ g Kⱼ Kⱼ' →
        (∀ Aᵣ, EffSig.opRes (Eff := Eff) (Mult := Mult) h₁.label op = some Aᵣ →
          ∃ qᵣ, Cⱼ = CTy.F qᵣ Aᵣ) →
        Bang.dispatchOn nh op w₁ (Kⱼ, h₁, K₁) = some cfg₁ →
        Bang.dispatchOn nh op w₂ (Kⱼ', h₂, K₂) = some cfg₂ →
        (∃ (qᵣ : Mult) (Aᵣ : VTy Eff Mult) (r₁ r₂ : Val) (Sᵢ Sᵢ' : Stack) (eₛ : Eff),
            cfg₁ = (Sᵢ, Comp.ret r₁) ∧ cfg₂ = (Sᵢ', Comp.ret r₂) ∧
            Val.Closed r₁ ∧ Val.Closed r₂ ∧ VrelK k Aᵣ r₁ r₂ ∧
            KrelS k (CTy.F qᵣ Aᵣ) D' eₛ g Sᵢ Sᵢ')) :
    KrelS m Cᵢ D' εᵢ g (Kᵢ ++ Frame.handleF nh h₁ :: K₁) (Kᵢ' ++ Frame.handleF nh h₂ :: K₂) := by
  -- ◊4.5b-strengthen: WELL-FOUNDED recursion on `(m, Kᵢ.length)`. letF/appF recurse on the shorter
  -- `Kᵢ` (second component drops); the NESTED handleF case recurses at the DROPPED index `k < m` (first
  -- component drops) on the dispatched stack `Sᵢ` — which may be LONGER, but the step-index pays for it.
  match Kᵢ, Kᵢ' with
  | [], [] =>
      -- Cᵢ = Dᵢ (nil); the append is `handleF h :: K` — `krelS_handleF_intro`.
      rw [krelS_nil] at hin
      obtain ⟨rfl, _⟩ := hin
      simpa using krelS_handleF_intro (e := εᵢ) hHR htail hres
  | (Frame.letF N₁ :: Kᵢrest), (Frame.letF N₂ :: Kᵢ'rest) =>
      rw [krelS_letF] at hin
      obtain ⟨q, A, B, φ, hC, hbody, htin⟩ := hin
      rw [List.cons_append, List.cons_append, krelS_letF]
      exact ⟨q, A, B, φ, hC, hbody, krelS_append htin hHR htail hres⟩
  | (Frame.appF u₁ :: Kᵢrest), (Frame.appF u₂ :: Kᵢ'rest) =>
      rw [krelS_appF] at hin
      obtain ⟨q, A, B, hC, hcu₁, hcu₂, hu, htin⟩ := hin
      rw [List.cons_append, List.cons_append, krelS_appF]
      exact ⟨q, A, B, hC, hcu₁, hcu₂, hu, krelS_append htin hHR htail hres⟩
  | (Frame.handleF mh₁ hh₁ :: Kᵢrest), (Frame.handleF mh₂ hh₂ :: Kᵢ'rest) =>
      -- ◊4.5b-strengthen CLOSE: a handler NESTED in the captured continuation. The structural shape
      -- closes HandlerRel + the recursive-append tail; the resume conjunct over the APPENDED tail is now
      -- reconstructible. From the inner conjunct `_hres_inner` (krel-carrying): the inner dispatch over
      -- `Kᵢrest` yields a RETURN config `(Sᵢ, ret rⱼ)` with `Sᵢ~Sᵢ'` (KrelS at hole `F qᵣ Aᵣ`, answer `Dᵢ`)
      -- and `r₁~r₂`. `dispatchOn_append_outer` lifts this dispatch over `Kᵢrest ++ handleF nh h₁::K₁` to
      -- `(Sᵢ ++ handleF nh h₁::K₁, ret rⱼ)`. Then `krelS_append` (at the DROPPED index `k`, on the inner `Sᵢ`)
      -- composes `Sᵢ` with `handleF nh h₁::K₁` ⇒ `KrelS k (F qᵣ Aᵣ) D' (Sᵢ++handleF nh h₁::K₁)(Sᵢ'++…)`,
      -- exactly the appended decomposition the goal demands. ADR-0055: the nested frame carries its OWN
      -- identity `mh₁` (= `mh₂` by `krelS_handleF`'s id equality), routed through `dispatchOn mh₁`.
      -- shape: biernacki-popl18 §5.4 Lemma 2 (config append).
      rw [krelS_handleF] at hin
      obtain ⟨hmid, hHRtop, htin, hres_inner⟩ := hin
      subst hmid
      rw [List.cons_append, List.cons_append, krelS_handleF]
      refine ⟨rfl, hHRtop, krelS_append htin hHR htail hres, ?_⟩
      intro k hk op w₁ w₂ Cⱼ εⱼ Kⱼ Kⱼ' cfg₁ cfg₂ hcatch hcw₁ hcw₂ hVrel hKj hCⱼ hd₁ hd₂
      -- recover the INNER dispatch (over `Kᵢrest`) by computing it, then lift via `dispatchOn_append_outer`.
      obtain ⟨cfgᵢ₁, hdi₁⟩ : ∃ c, Bang.dispatchOn mh₁ op w₁ (Kⱼ, hh₁, Kᵢrest) = some c := by
        cases hh₁ with
        | throws _ => exact ⟨_, rfl⟩
        | state _ _ => rw [dispatchOn]; split <;> exact ⟨_, rfl⟩
        | transaction _ _ => unfold dispatchOn; split_ifs <;> first | exact ⟨_, rfl⟩ | (cases w₁ <;> exact ⟨_, rfl⟩)
        -- custom (#44 STAGE 5): `dispatchOn` custom is `some` iff `find? (·.1==op)` is `some`, and that is
        -- INDEPENDENT of the outer stack. The OUTER dispatch `hd₁` already succeeded over `Kᵢrest ++ …`, so
        -- `find?` is `some` — the inner dispatch (over `Kᵢrest`) succeeds by the SAME match. (`dispatchOn`
        -- reinstalls over `Kᵢ ++ custom :: Kₒ`; the `Kₒ` half never gates the `some`/`none` decision.)
        | custom ℓ' p cl =>
            simp only [dispatchOn] at hd₁ ⊢
            cases hf : cl.find? (·.1 == op) with
            | none => simp only [hf, reduceCtorEq] at hd₁
            | some clause => simp only [hf]; exact ⟨_, rfl⟩
      obtain ⟨cfgᵢ₂, hdi₂⟩ : ∃ c, Bang.dispatchOn mh₁ op w₂ (Kⱼ', hh₂, Kᵢ'rest) = some c := by
        cases hh₂ with
        | throws _ => exact ⟨_, rfl⟩
        | state _ _ => rw [dispatchOn]; split <;> exact ⟨_, rfl⟩
        | transaction _ _ => unfold dispatchOn; split_ifs <;> first | exact ⟨_, rfl⟩ | (cases w₂ <;> exact ⟨_, rfl⟩)
        -- custom (symmetric): the RHS outer dispatch `hd₂` forced `find?` some — the inner one succeeds.
        | custom ℓ' p cl =>
            simp only [dispatchOn] at hd₂ ⊢
            cases hf : cl.find? (·.1 == op) with
            | none => simp only [hf, reduceCtorEq] at hd₂
            | some clause => simp only [hf]; exact ⟨_, rfl⟩
      have hlift₁ := dispatchOn_append_outer mh₁ op w₁ Kⱼ hh₁ Kᵢrest (Frame.handleF nh h₁ :: K₁) hdi₁
      have hlift₂ := dispatchOn_append_outer mh₁ op w₂ Kⱼ' hh₂ Kᵢ'rest (Frame.handleF nh h₂ :: K₂) hdi₂
      rw [hd₁] at hlift₁; rw [hd₂] at hlift₂
      obtain rfl := (Option.some.injEq _ _).mp hlift₁.symm
      obtain rfl := (Option.some.injEq _ _).mp hlift₂.symm
      -- apply the inner conjunct to the inner dispatch → the decomposition `cfgᵢⱼ = (Sᵢ, ret rⱼ)`.
      obtain ⟨qᵣ, Aᵣ, r₁, r₂, Sᵢ, Sᵢ', eₛ, hcf₁, hcf₂, hcr₁, hcr₂, hr, hSrel⟩ :=
        hres_inner k hk op w₁ w₂ Cⱼ εⱼ Kⱼ Kⱼ' cfgᵢ₁ cfgᵢ₂ hcatch hcw₁ hcw₂ hVrel hKj hCⱼ hdi₁ hdi₂
      subst hcf₁; subst hcf₂
      -- the appended config is `(Sᵢ ++ handleF nh h₁::K₁, ret rⱼ)`; rebuild the decomposition over the
      -- append by `krelS_append` at the dropped index `k` (the step-index pays for the longer `Sᵢ`).
      refine ⟨qᵣ, Aᵣ, r₁, r₂, Sᵢ ++ Frame.handleF nh h₁ :: K₁, Sᵢ' ++ Frame.handleF nh h₂ :: K₂, eₛ,
        by simp, by simp, hcr₁, hcr₂, hr, ?_⟩
      exact krelS_append (εᵢ := eₛ) hSrel (HandlerRel_mono (le_of_lt hk) hHR)
        (KrelS_mono (le_of_lt hk) htail) (fun k' hk' => hres k' (lt_trans hk' hk))
  | [], (_ :: _) => simp only [KrelS] at hin
  | (fr :: _), [] => exact absurd hin (by simp only [KrelS]; cases fr <;> exact not_false)
  | (Frame.letF _ :: _), (Frame.appF _ :: _) => simp only [KrelS] at hin
  | (Frame.letF _ :: _), (Frame.handleF _ _ :: _) => simp only [KrelS] at hin
  | (Frame.appF _ :: _), (Frame.letF _ :: _) => simp only [KrelS] at hin
  | (Frame.appF _ :: _), (Frame.handleF _ _ :: _) => simp only [KrelS] at hin
  | (Frame.handleF _ _ :: _), (Frame.letF _ :: _) => simp only [KrelS] at hin
  | (Frame.handleF _ _ :: _), (Frame.appF _ :: _) => simp only [KrelS] at hin
termination_by (m, Kᵢ.length)
decreasing_by
  -- letF/appF/handleF structural recursions drop `Kᵢ.length` (m fixed); the nested handleF resume
  -- recursion drops the step-index `m` (to `k`).
  all_goals first
    | exact Prod.Lex.right _ (by simp)
    | exact Prod.Lex.left _ _ hk

/-- ◊4.5b-append the STATE-reinstall lemma — the resumptive heart. A `state ℓ s` handler frame over a
related tail self-relates at every index, with the resume conjunct supplied by GUARDED RECURSION on the
index: the get/put dispatch reinstalls `state ℓ s` and resumes `ret r` (r = s for get, unit for put)
through the captured continuation `Kᵢ`, which `krelS_append`s onto the reinstalled frame + tail at the
DROPPED index `m' < m` (the IH). The stored state `s` self-relates at `S` (hsv, from the caller's typing
via `vrelK_fund`). shape: biernacki-popl18 §5.4 resumptive clause + the ▷-guarded reinstall. -/
theorem krelS_state_reinstall {q : Mult} {A S : VTy Eff Mult} {D : CTy Eff Mult} {φ : Eff} {ℓ : Label}
    {g : Nat}
    (hgr : EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "get" = some S)
    (hp : EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "put" = some S)
    (hpr : EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "put" = some VTy.unit)
    (hrestrict : ∀ op s, Bang.handlesOp (Handler.state ℓ s) ℓ op = true → op = "get" ∨ op = "put") :
    ∀ (nh : Nat) m (s₁ s₂ : Val), Val.Closed s₁ → Val.Closed s₂ →
      VrelK m S s₁ s₂ →
      ∀ (K₁ K₂ : Stack), KrelS m (CTy.F q A) D φ g K₁ K₂ →
      KrelS m (CTy.F q A) D φ g (Frame.handleF nh (Handler.state ℓ s₁) :: K₁)
                              (Frame.handleF nh (Handler.state ℓ s₂) :: K₂) := by
  -- GUARDED RECURSION on the index: the reinstalled handler (over the SAME tail, at the put-updated state
  -- pair) relates at the DROPPED index m' < m (the IH), supplying `krelS_append`'s resume conjunct.
  -- ADR-0055: the frame carries its generative id `nh`; the resume dispatch reinstalls `handleF nh` (same id).
  intro nh m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro s₁ s₂ hcs₁ hcs₂ hsv K₁ K₂ hK
    refine krelS_handleF_intro
      (show HandlerRel Eff Mult m (Handler.state ℓ s₁) (Handler.state ℓ s₂) from ⟨rfl, S, hsv⟩) hK ?_
    intro m' hm' op w₁ w₂ Cᵢ εᵢ Kᵢ Kᵢ' cfg₁ cfg₂ hcatch hcw₁ hcw₂ hVrel hKi hCᵢ hd₁ hd₂
    rcases hrestrict op s₁ hcatch with rfl | rfl
    · -- GET: cfg = (Kᵢ ++ handleF nh (state ℓ sⱼ)::Kⱼ, ret sⱼ); resume value = the stored state (related).
      obtain ⟨qᵣ, rfl⟩ := hCᵢ S (by rw [Handler.label]; exact hgr)
      simp only [Handler.label, dispatchOn] at hd₁ hd₂
      obtain rfl := (Option.some.injEq _ _).mp hd₁.symm
      obtain rfl := (Option.some.injEq _ _).mp hd₂.symm
      -- the reinstalled `state ℓ s₁/s₂` over the tail relates at m' (IH at the SAME state pair, downward).
      have hreinst := ih m' hm' s₁ s₂ hcs₁ hcs₂ (VrelK_mono (le_of_lt hm') hsv) K₁ K₂
        (KrelS_mono (le_of_lt hm') hK)
      rw [krelS_handleF] at hreinst
      have happ := krelS_append (Dᵢ := CTy.F q A) hKi
        (show HandlerRel Eff Mult m' (Handler.state ℓ s₁) (Handler.state ℓ s₂) from
          ⟨rfl, S, VrelK_mono (le_of_lt hm') hsv⟩)
        (KrelS_mono (le_of_lt hm') hK) hreinst.2.2.2
      -- ◊4.5b-strengthen: SUPPLY the decomposition — the dispatched config is `(Kᵢ++reinstall::K, ret sⱼ)`,
      -- the resume value `s₁~s₂` at `S`, the appended stack `KrelS`-related at the returner hole `F qᵣ S`.
      exact ⟨qᵣ, S, s₁, s₂, _, _, εᵢ, rfl, rfl, hcs₁, hcs₂, VrelK_mono (le_of_lt hm') hsv, happ⟩
    · -- PUT: cfg = (Kᵢ ++ handleF nh (state ℓ wⱼ)::Kⱼ, ret unit); reinstalled state = the payload (related at
      -- S via hVrel), resume value = unit (trivially related). The IH at the NEW state pair (w₁,w₂).
      have hwS : VrelK m' S w₁ w₂ := hVrel S (by rw [Handler.label]; exact hp)
      obtain ⟨qᵣ, rfl⟩ := hCᵢ VTy.unit (by rw [Handler.label]; exact hpr)
      simp only [Handler.label, dispatchOn] at hd₁ hd₂
      obtain rfl := (Option.some.injEq _ _).mp hd₁.symm
      obtain rfl := (Option.some.injEq _ _).mp hd₂.symm
      have hreinst := ih m' hm' w₁ w₂ hcw₁ hcw₂ hwS K₁ K₂ (KrelS_mono (le_of_lt hm') hK)
      rw [krelS_handleF] at hreinst
      have happ := krelS_append (Dᵢ := CTy.F q A) hKi
        (show HandlerRel Eff Mult m' (Handler.state ℓ w₁) (Handler.state ℓ w₂) from ⟨rfl, S, hwS⟩)
        (KrelS_mono (le_of_lt hm') hK) hreinst.2.2.2
      -- ◊4.5b-strengthen: PUT resumes `unit` (unit~unit); the appended stack relates at hole `F qᵣ unit`.
      exact ⟨qᵣ, VTy.unit, Val.vunit, Val.vunit, _, _, εᵢ, rfl, rfl, (fun k => rfl), (fun k => rfl),
        (by show VrelK m' VTy.unit Val.vunit Val.vunit; rw [VrelK, BaseRel]; exact ⟨rfl, rfl⟩), happ⟩

/-! ### ◊4.5b-append — heap `getD` facts, proved GetD-IMPORT-FREE (from `List.Basic`'s `getElem?`).
`Mathlib.Data.List.GetD` is deliberately NOT imported (it tips the `crelK_fund` mutual block's
structural-recursion inference past the heartbeat budget). All heap `getD` reasoning routes through
`List.getD_eq_getElem?_getD` (transitively available) + `getElem?` lemmas from `List.Basic`. -/

theorem heap_getD_append_left (l l' : List Val) (d : Val) (n : Nat) (h : n < l.length) :
    (l ++ l').getD n d = l.getD n d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem heap_getD_append_mid (l : List Val) (w : Val) (d : Val) :
    (l ++ [w]).getD l.length d = w := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]; simp

theorem heap_getD_default (l : List Val) (d : Val) (n : Nat) (h : l.length ≤ n) :
    l.getD n d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

theorem heap_getD_get (l : List Val) (d : Val) (n : Nat) (h : n < l.length) :
    l.getD n d = l[n] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

/-- ◊4.5b-append the heap-relation for `transaction` (length-eq + pointwise int). Explicit `Eff Mult`
(Store monomorphic). int cells ⇒ related = equal int. -/
def HeapRel (Eff Mult : Type) [Lattice Eff] [OrderBot Eff] [CommSemiring Mult] [DecidableEq Mult]
    [EffSig Eff Mult] (n : Nat) (Θ₁ Θ₂ : Store) : Prop :=
  Θ₁.length = Θ₂.length ∧
    ∀ i : Nat, i < Θ₁.length →
      VrelK (Eff := Eff) (Mult := Mult) n (VTy.int : VTy Eff Mult)
        (Θ₁.getD i (Val.vint 0)) (Θ₂.getD i (Val.vint 0))

/-- ◊4.5b-append `HeapRel n Θ Θ` from all-cells-`int`, WITHOUT `vrelK_fund` — int is a base type, so each
cell self-relates by `BaseRel` (`HasVTy.vint` is the SOLE `int` constructor ⇒ `cell = vint a`). This MUST
avoid `vrelK_fund`: the `crelK_fund` handleTransaction arm would otherwise call it on `hcells` (a SIDE-
condition, NOT a sub-derivation of the handle node) — breaking the mutual block's structural recursion. -/
theorem heapRel_self_of_cells_int (n : Nat) (Θ : Store)
    (hcells : ∀ cell ∈ Θ, HasVTy (Eff := Eff) (Mult := Mult) [] [] cell VTy.int) :
    HeapRel Eff Mult n Θ Θ := by
  -- canonical form at `int` (its SOLE producer is `HasVTy.vint`): case on the typing with a GENERAL type
  -- `A` (the working codebase pattern) + the `A = int` equation, discharging non-`vint` constructors.
  have hcanon : ∀ {γ : GradeVec Mult} {cell : Val} {A : VTy Eff Mult},
      HasVTy γ ([] : TyCtx Eff Mult) cell A → A = VTy.int → ∃ a : Int, cell = Val.vint a := by
    intro γ cell A ht hA
    cases ht with
    | vint => exact ⟨_, rfl⟩
    | vvar hget => simp at hget
    | _ => exact absurd hA (by simp)
  refine ⟨rfl, fun i hi => ?_⟩
  have hmem : Θ.getD i (Val.vint 0) ∈ Θ := by
    rw [heap_getD_get _ _ _ hi]; exact List.getElem_mem hi
  obtain ⟨a, ha⟩ := hcanon (hcells _ hmem) rfl
  rw [ha, VrelK, BaseRel]; exact ⟨a, rfl, rfl⟩

/-- `dispatchOn (state _)` is total (factored OUT of the mutual block — keeps the producer arms cheap). -/
theorem dispatchOn_state_isSome (n : Nat) (op : OpId) (v : Val) (Kᵢ Kₒ : Stack) (ℓ : Label) (s : Val) :
    ∃ c, Bang.dispatchOn n op v (Kᵢ, Handler.state ℓ s, Kₒ) = some c := by
  rw [dispatchOn]; split <;> exact ⟨_, rfl⟩

/-- `dispatchOn (transaction _)` is total. -/
theorem dispatchOn_transaction_isSome (n : Nat) (op : OpId) (v : Val) (Kᵢ Kₒ : Stack) (ℓ : Label) (Θ : Store) :
    ∃ c, Bang.dispatchOn n op v (Kᵢ, Handler.transaction ℓ Θ, Kₒ) = some c := by
  unfold dispatchOn; split_ifs <;> first | exact ⟨_, rfl⟩ | (cases v <;> exact ⟨_, rfl⟩)

/-- ◊4.5b-append the TRANSACTION-reinstall lemma — the multi-cell resumptive heart (the `state` analogue
with a heap). GUARDED RECURSION on the index; newTVar/readTVar/writeTVar reinstall + resume,
`krelS_append`ed onto the reinstalled frame at the dropped index. Each op preserves `HeapRel` (int cells
related = equal). All heap `getD` via the GetD-free `heap_getD_*`. -/
theorem krelS_transaction_reinstall {q : Mult} {A : VTy Eff Mult} {D : CTy Eff Mult} {φ : Eff}
    {ℓ : Label} {g : Nat}
    (hnewA : EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "newTVar" = some VTy.int)
    (hnewR : EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "newTVar" = some VTy.int)
    (hreadA : EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "readTVar" = some VTy.int)
    (hreadR : EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "readTVar" = some VTy.int)
    (hwriteA : EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "writeTVar"
      = some (VTy.prod (VTy.int : VTy Eff Mult) VTy.int))
    (hwriteR : EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "writeTVar" = some VTy.unit)
    (hrestrict : ∀ op Θ', Bang.handlesOp (Handler.transaction ℓ Θ') ℓ op = true →
      op = "newTVar" ∨ op = "readTVar" ∨ op = "writeTVar") :
    ∀ (nh : Nat) m (Θ₁ Θ₂ : Store), HeapRel Eff Mult m Θ₁ Θ₂ →
      ∀ (K₁ K₂ : Stack), KrelS m (CTy.F q A) D φ g K₁ K₂ →
      KrelS m (CTy.F q A) D φ g (Frame.handleF nh (Handler.transaction ℓ Θ₁) :: K₁)
                              (Frame.handleF nh (Handler.transaction ℓ Θ₂) :: K₂) := by
  intro nh m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro Θ₁ Θ₂ hheap K₁ K₂ hK
    refine krelS_handleF_intro
      (show HandlerRel Eff Mult m (Handler.transaction ℓ Θ₁) (Handler.transaction ℓ Θ₂) from
        ⟨rfl, hheap.1, hheap.2⟩) hK ?_
    intro m' hm' op w₁ w₂ Cᵢ εᵢ Kᵢ Kᵢ' cfg₁ cfg₂ hcatch hcw₁ hcw₂ hVrel hKi hCᵢ hd₁ hd₂
    have hheap' : HeapRel Eff Mult m' Θ₁ Θ₂ := ⟨hheap.1, fun i hi => VrelK_mono (le_of_lt hm') (hheap.2 i hi)⟩
    rcases hrestrict op Θ₁ hcatch with rfl | rfl | rfl
    · -- newTVar: reinstall Θⱼ ++ [wⱼ], resume `vint Θⱼ.length` (same length ⇒ equal int).
      obtain ⟨qᵣ, rfl⟩ := hCᵢ VTy.int (by rw [Handler.label]; exact hnewR)
      have hwint : VrelK m' VTy.int w₁ w₂ := hVrel VTy.int (by rw [Handler.label]; exact hnewA)
      simp only [Handler.label, dispatchOn] at hd₁ hd₂
      obtain rfl := (Option.some.injEq _ _).mp hd₁.symm
      obtain rfl := (Option.some.injEq _ _).mp hd₂.symm
      have happend : HeapRel Eff Mult m' (Θ₁ ++ [w₁]) (Θ₂ ++ [w₂]) := by
        refine ⟨by simp [hheap'.1], fun i hi => ?_⟩
        simp only [List.length_append, List.length_cons, List.length_nil] at hi
        by_cases hlt : i < Θ₁.length
        · rw [heap_getD_append_left _ _ _ _ hlt, heap_getD_append_left _ _ _ _ (hheap'.1 ▸ hlt)]
          exact hheap'.2 i hlt
        · have hi1 : i = Θ₁.length := by omega
          subst hi1
          rw [heap_getD_append_mid, hheap'.1, heap_getD_append_mid]; exact hwint
      have hreinst := ih m' hm' (Θ₁ ++ [w₁]) (Θ₂ ++ [w₂]) happend K₁ K₂ (KrelS_mono (le_of_lt hm') hK)
      rw [krelS_handleF] at hreinst
      have happ := krelS_append (Dᵢ := CTy.F q A) hKi
        (show HandlerRel Eff Mult m' (Handler.transaction ℓ (Θ₁ ++ [w₁])) (Handler.transaction ℓ (Θ₂ ++ [w₂]))
          from ⟨rfl, happend.1, happend.2⟩) (KrelS_mono (le_of_lt hm') hK) hreinst.2.2.2
      -- ◊4.5b-strengthen: SUPPLY the decomposition — resume `vint Θⱼ.length` (related; same length).
      exact ⟨qᵣ, VTy.int, Val.vint Θ₁.length, Val.vint Θ₂.length, _, _, εᵢ, rfl, rfl,
        (fun k => rfl), (fun k => rfl),
        (by show VrelK m' VTy.int (Val.vint Θ₁.length) (Val.vint Θ₂.length)
            rw [VrelK, BaseRel]; exact ⟨Θ₁.length, rfl, by rw [hheap'.1]⟩), happ⟩
    · -- readTVar: heap UNCHANGED, resume the cell (related via hheap', or default both sides).
      obtain ⟨qᵣ, rfl⟩ := hCᵢ VTy.int (by rw [Handler.label]; exact hreadR)
      have hweq : w₁ = w₂ := by
        have := hVrel VTy.int (by rw [Handler.label]; exact hreadA)
        rw [VrelK, BaseRel] at this; obtain ⟨a, rfl, rfl⟩ := this; rfl
      subst hweq
      simp only [Handler.label, dispatchOn] at hd₁ hd₂
      obtain rfl := (Option.some.injEq _ _).mp hd₁.symm
      obtain rfl := (Option.some.injEq _ _).mp hd₂.symm
      set idx := (Bang.tvarIdx w₁).getD 0 with hidx
      have hcellrel : VrelK (Eff := Eff) (Mult := Mult) m' VTy.int
          (Θ₁.getD idx (Val.vint 0)) (Θ₂.getD idx (Val.vint 0)) := by
        by_cases hlt : idx < Θ₁.length
        · exact hheap'.2 idx hlt
        · rw [heap_getD_default _ _ _ (by omega), heap_getD_default _ _ _ (by rw [← hheap'.1]; omega)]
          rw [VrelK, BaseRel]; exact ⟨0, rfl, rfl⟩
      obtain ⟨a, hca₁, hca₂⟩ : ∃ a : Int, Θ₁.getD idx (Val.vint 0) = Val.vint a ∧
          Θ₂.getD idx (Val.vint 0) = Val.vint a := by
        have := hcellrel; rw [VrelK, BaseRel] at this; exact this
      have hreinst := ih m' hm' Θ₁ Θ₂ hheap' K₁ K₂ (KrelS_mono (le_of_lt hm') hK)
      rw [krelS_handleF] at hreinst
      have happ := krelS_append (Dᵢ := CTy.F q A) hKi
        (show HandlerRel Eff Mult m' (Handler.transaction ℓ Θ₁) (Handler.transaction ℓ Θ₂)
          from ⟨rfl, hheap'.1, hheap'.2⟩) (KrelS_mono (le_of_lt hm') hK) hreinst.2.2.2
      -- ◊4.5b-strengthen: SUPPLY the decomposition — resume the read cell (related via `hcellrel`).
      exact ⟨qᵣ, VTy.int, Θ₁.getD idx (Val.vint 0), Θ₂.getD idx (Val.vint 0), _, _, εᵢ, rfl, rfl,
        (by rw [hca₁]; intro k; rfl), (by rw [hca₂]; intro k; rfl), hcellrel, happ⟩
    · -- writeTVar: payload `pair (vint i) (vint b)`; reinstall `storeSet Θⱼ i (vint b)`, resume unit.
      obtain ⟨qᵣ, rfl⟩ := hCᵢ VTy.unit (by rw [Handler.label]; exact hwriteR)
      have hpair := hVrel (VTy.prod VTy.int VTy.int) (by rw [Handler.label]; exact hwriteA)
      rw [VrelK] at hpair
      obtain ⟨a₁, a₂, b₁, b₂, rfl, rfl, hia, hib⟩ := hpair
      rw [VrelK, BaseRel] at hia hib
      obtain ⟨i, rfl, rfl⟩ := hia
      obtain ⟨b, rfl, rfl⟩ := hib
      simp only [Handler.label, dispatchOn] at hd₁ hd₂
      obtain rfl := (Option.some.injEq _ _).mp hd₁.symm
      obtain rfl := (Option.some.injEq _ _).mp hd₂.symm
      set j := (Bang.tvarIdx (Val.vint i)).getD 0 with hj
      have hset : HeapRel Eff Mult m' (Bang.storeSet Θ₁ j (Val.vint b)) (Bang.storeSet Θ₂ j (Val.vint b)) := by
        refine ⟨by simp [Bang.storeSet, hheap'.1], fun kk hk => ?_⟩
        simp only [Bang.storeSet, List.length_set] at hk ⊢
        rw [heap_getD_get _ _ _ (by rw [List.length_set]; exact hk),
            heap_getD_get _ _ _ (by rw [List.length_set, ← hheap'.1]; exact hk)]
        by_cases hkj : kk = j
        · subst hkj
          rw [List.getElem_set_self, List.getElem_set_self]
          rw [VrelK, BaseRel]; exact ⟨b, rfl, rfl⟩
        · rw [List.getElem_set_ne (Ne.symm hkj), List.getElem_set_ne (Ne.symm hkj)]
          have := hheap'.2 kk hk
          rwa [heap_getD_get _ _ _ hk, heap_getD_get _ _ _ (by rw [← hheap'.1]; exact hk)] at this
      have hreinst := ih m' hm' _ _ hset K₁ K₂ (KrelS_mono (le_of_lt hm') hK)
      rw [krelS_handleF] at hreinst
      have happ := krelS_append (Dᵢ := CTy.F q A) hKi
        (show HandlerRel Eff Mult m' (Handler.transaction ℓ (Bang.storeSet Θ₁ j (Val.vint b)))
            (Handler.transaction ℓ (Bang.storeSet Θ₂ j (Val.vint b)))
          from ⟨rfl, hset.1, hset.2⟩) (KrelS_mono (le_of_lt hm') hK) hreinst.2.2.2
      -- ◊4.5b-strengthen: SUPPLY the decomposition — writeTVar resumes `unit`.
      exact ⟨qᵣ, VTy.unit, Val.vunit, Val.vunit, _, _, εᵢ, rfl, rfl, (fun k => rfl), (fun k => rfl),
        (by show VrelK m' VTy.unit Val.vunit Val.vunit; rw [VrelK, BaseRel]; exact ⟨rfl, rfl⟩), happ⟩

/-! ◊4.5b sub-block (f) — `splitAt`-DECOMPOSITION over `KrelS` (the producer-`up` enabler). With the
`h₁ = h₂` handleF clause, `splitAt` fires IDENTICALLY on the two related stacks: the SAME catching
handler `h` at the SAME position, and the OUTER tails `K₁ₒ, K₂ₒ` stay `KrelS`-related. The
`krelS_splitAtId_decomp` (ADR-0054/0055) form below supersedes the legacy `splitAt`-decomp — the
handleF-MISS arm dissolves under IDENTITY dispatch (`splitAtId` matches the cap's generative id, no
`handlesOp` walk-past). -/

/-- ADR-0053: `KrelS`-related stacks have the SAME handler count. `KrelS` forces matching frame KINDS
(`letF::letF`/`appF::appF`/`handleF::handleF`), so the handler skeletons coincide. This is what lets the
ABSOLUTE level→index conversion `handlerCount K - 1 - cap` agree on `K₁` and `K₂` at the dispatch seam. -/
theorem krelS_handlerCount_eq {n : Nat} :
    ∀ {K₁ K₂ : Stack} {C D : CTy Eff Mult} {e : Eff} {g : Nat},
      KrelS n C D e g K₁ K₂ → Bang.handlerCount K₁ = Bang.handlerCount K₂ := by
  intro K₁
  induction K₁ with
  | nil =>
      intro K₂ C D e g hK
      rcases K₂ with _ | ⟨fr, K⟩
      · rfl
      · simp only [KrelS] at hK
  | cons fr K₁' ih =>
      intro K₂ C D e g hK
      rcases K₂ with _ | ⟨fr₂, K₂'⟩
      · cases fr <;> simp only [KrelS] at hK
      · cases fr <;> cases fr₂ <;>
          first
          | (simp only [KrelS] at hK; done)
          | (rw [KrelS] at hK
             obtain ⟨_, _, _, _, _, _, htail⟩ := hK
             simp only [Bang.handlerCount]; exact ih htail)
          | (rw [KrelS] at hK
             obtain ⟨_, _, _, _, _, _, _, htail⟩ := hK
             simp only [Bang.handlerCount]; exact ih htail)
          | (have htail := (krelS_handleF.mp hK).2.2.1
             simp only [Bang.handlerCount]
             have := ih htail; omega)

theorem krelS_splitAtId_decomp {n : Nat} {C D : CTy Eff Mult} {e : Eff} {g : Nat}
    {K₁ K₂ : Stack} {nid : Nat} {K₁ᵢ K₁ₒ : Stack} {h : Handler}
    (hK : KrelS n C D e g K₁ K₂)
    (hsp : Bang.splitAtId K₁ nid = some (K₁ᵢ, h, K₁ₒ)) :
    -- ADR-0055: `splitAtId K₂ nid` fires at the SAME identity `nid` (the stacks share frame KINDS and,
    -- under canonical ids, the matching `handleF` ids — `krelS_handleF` forces `nh₁ = nh₂`) with a
    -- RELATED handler `h'` (`HandlerRel n h h'`). The handleF arm is a PURE ID TEST (`nh = nid` HIT /
    -- `nh ≠ nid` SKIP): the old `splitAt`-decomp's answer-type-determinism MISS wall DISSOLVES because
    -- `splitAtId` never tests `handlesOp` — it locates the catcher by identity, not by walking past
    -- non-catching handlers. (SKIP arm carries ONE documented relocation residual; see the sorry.)
    ∃ (K₂ᵢ K₂ₒ : Stack) (h' : Handler) (Dᵢ : CTy Eff Mult) (C' : CTy Eff Mult) (e' : Eff),
      Bang.splitAtId K₂ nid = some (K₂ᵢ, h', K₂ₒ) ∧ HandlerRel Eff Mult n h h' ∧
      KrelS n C Dᵢ e g K₁ᵢ K₂ᵢ ∧ KrelS n C' D e' g K₁ₒ K₂ₒ
      ∧ (∀ m, m < n → ∀ (op' : OpId) (w₁ w₂ : Val) (Cᵢ' : CTy Eff Mult) (εᵢ' : Eff)
            (Kᵢ Kᵢ' : Stack) (cfg₁ cfg₂ : EvalCtx × Comp),
          Bang.handlesOp h h.label op' = true →
          Val.Closed w₁ → Val.Closed w₂ →
          (∀ Aop, EffSig.opArg (Eff := Eff) (Mult := Mult) h.label op' = some Aop → VrelK m Aop w₁ w₂) →
          KrelS m Cᵢ' Dᵢ εᵢ' g Kᵢ Kᵢ' →
          (∀ Aᵣ, EffSig.opRes (Eff := Eff) (Mult := Mult) h.label op' = some Aᵣ →
            ∃ qᵣ, Cᵢ' = CTy.F qᵣ Aᵣ) →
          Bang.dispatchOn nid op' w₁ (Kᵢ, h, K₁ₒ) = some cfg₁ →
          Bang.dispatchOn nid op' w₂ (Kᵢ', h', K₂ₒ) = some cfg₂ →
          (∃ (qᵣ : Mult) (Aᵣ : VTy Eff Mult) (r₁ r₂ : Val) (Sᵢ Sᵢ' : Stack) (eₛ : Eff),
              cfg₁ = (Sᵢ, Comp.ret r₁) ∧ cfg₂ = (Sᵢ', Comp.ret r₂) ∧
              Val.Closed r₁ ∧ Val.Closed r₂ ∧ VrelK m Aᵣ r₁ r₂ ∧
              KrelS m (CTy.F qᵣ Aᵣ) D eₛ g Sᵢ Sᵢ')) := by
  induction K₁ generalizing K₂ K₁ᵢ K₁ₒ C e with
  | nil => simp [Bang.splitAtId] at hsp
  | cons fr K₁' ih =>
      match K₂ with
      | [] => exact absurd hK (by simp only [KrelS]; cases fr <;> exact not_false)
      | fr₂ :: K₂' =>
          cases fr with
          | letF N₁ =>
              cases fr₂ with
              | letF N₂ =>
                  rw [krelS_letF] at hK
                  obtain ⟨q, A, B, φ, hC, hbody, htail⟩ := hK
                  simp only [splitAtId, Option.map_eq_some_iff] at hsp
                  obtain ⟨⟨Ki', hh, Ko'⟩, hsp', heq⟩ := hsp
                  simp only [Prod.mk.injEq] at heq
                  obtain ⟨rfl, rfl, rfl⟩ := heq
                  obtain ⟨K₂ᵢ, K₂ₒ, h', Dᵢ, C', e', hsp2, hHR, hin, htail2, hres2⟩ := ih htail hsp'
                  refine ⟨Frame.letF N₂ :: K₂ᵢ, K₂ₒ, h', Dᵢ, C', e',
                    by simp only [splitAtId]; rw [hsp2]; rfl, hHR, ?_, htail2, hres2⟩
                  rw [krelS_letF]; exact ⟨q, A, B, φ, hC, hbody, hin⟩
              | _ => simp only [KrelS] at hK
          | appF w₁ =>
              cases fr₂ with
              | appF w₂ =>
                  rw [krelS_appF] at hK
                  obtain ⟨q, A, B, hC, hcw₁, hcw₂, hw, htail⟩ := hK
                  simp only [splitAtId, Option.map_eq_some_iff] at hsp
                  obtain ⟨⟨Ki', hh, Ko'⟩, hsp', heq⟩ := hsp
                  simp only [Prod.mk.injEq] at heq
                  obtain ⟨rfl, rfl, rfl⟩ := heq
                  obtain ⟨K₂ᵢ, K₂ₒ, h', Dᵢ, C', e', hsp2, hHR, hin, htail2, hres2⟩ := ih htail hsp'
                  refine ⟨Frame.appF w₂ :: K₂ᵢ, K₂ₒ, h', Dᵢ, C', e',
                    by simp only [splitAtId]; rw [hsp2]; rfl, hHR, ?_, htail2, hres2⟩
                  rw [krelS_appF]; exact ⟨q, A, B, hC, hcw₁, hcw₂, hw, hin⟩
              | _ => simp only [KrelS] at hK
          | handleF mh₁ hh₁ =>
              cases fr₂ with
              | handleF mh₂ hh₂ =>
                  rw [krelS_handleF] at hK
                  obtain ⟨hmid, hHRtop, htail, hres⟩ := hK
                  subst hmid
                  simp only [splitAtId] at hsp
                  by_cases hmn : mh₁ = nid
                  · -- HIT (`mh₁ = nid`): the split point. Inner prefix `[]` (nil at hole C), outer tail
                    -- K₁'/K₂' (related via `htail`), resume conjunct `hres` is the catching frame's
                    -- Kᵢ-threading one directly (its dispatch id IS `nid` after the `subst`).
                    subst hmn
                    rw [if_pos rfl, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hsp
                    obtain ⟨rfl, rfl, rfl⟩ := hsp
                    refine ⟨[], K₂', hh₂, C, C, e,
                      by simp [splitAtId], hHRtop, ?_, htail, hres⟩
                    rw [krelS_nil]; exact ⟨rfl, fun q A hC v₁ v₂ _ _ _ _ => ⟨1, v₂, rfl⟩⟩
                  · -- SKIP (`mh₁ ≠ nid`): the id test fails — recurse with the SAME `nid` on the tail.
                    -- The skipped handleF wraps the inner prefix. The MISS edge is GONE (identity dispatch
                    -- located the catcher by `nid`, NOT by walking past hh₁ — no answer-type-determinism wall).
                    rw [if_neg hmn, Option.map_eq_some_iff] at hsp
                    obtain ⟨⟨Ki', hh, Ko'⟩, hsp', heq⟩ := hsp
                    simp only [Prod.mk.injEq] at heq
                    obtain ⟨rfl, rfl, rfl⟩ := heq
                    obtain ⟨K₂ᵢ, K₂ₒ, h', Dᵢ, C', e', hsp2, hHR, hin, htail2, hres2⟩ := ih htail hsp'
                    refine ⟨Frame.handleF mh₁ hh₂ :: K₂ᵢ, K₂ₒ, h', Dᵢ, C', e',
                      by simp only [splitAtId]; rw [if_neg hmn, hsp2]; rfl, hHR, ?_, htail2, hres2⟩
                    -- the skipped handleF wraps the inner prefix: `KrelS n C Dᵢ e (handleF mh₁ hh₁::K₁ᵢ)(…)`.
                    -- `krelS_handleF_intro` rebuilds it from `hHRtop` + `hin` (inner relation, hole C,
                    -- answer Dᵢ) + a resume conjunct.
                    refine krelS_handleF_intro (nh := mh₁) hHRtop hin ?_
                    -- ADR-0055 SKIP RESIDUAL (the old 1628 relocation sorry, identity-keyed): `hres` (hh₁'s
                    -- resume over the ORIGINAL tail `K₁'`) must RELOCATE to the recursed inner prefix `Ki'`
                    -- (where `splitAtId` placed the deeper catcher). `K₁' = Ki' ++ handleF nid h' :: Ko'`
                    -- (`splitAtId_decomp hsp'`), so `dispatchOn` over `Ki'` lifts to `K₁'` via
                    -- `dispatchOn_append_outer` — but the conjunct demands the INVERSE (strip the appended
                    -- tail off a decomposition over the longer stack), which `hres` over `K₁'` does not
                    -- factor through in general. The dissolution is REAL (no `handlesOp` wall); the residual
                    -- is this one clean relocation. Scoped here for the SKIP arm. shape: biernacki-popl18 §5.4.
                    sorry
              | _ => simp only [KrelS] at hK

-- ◊inc-5 the op-PRODUCER, re-keyed to ADR-0054/0055 IDENTITY dispatch. The capability is now a VALUE
-- `vcap m ℓ` (VrelK at cap type forces the SAME id `m` both sides, LR:1427); `Source.step` resolves it via
-- `idDispatch K m ℓ op v = (splitAtId K m).bind (handlesOp-guard ∘ dispatchOn m)`. STANDALONE ⇒ a
-- `set_option maxHeartbeats` is safe (no mutual structural-recursion inference).
set_option maxHeartbeats 1000000 in
theorem crelK_fund_up {n : Nat} {m : Nat} {ℓ : Label} {op : OpId} {q : Mult} {A B : VTy Eff Mult} {φ : Eff}
    {v₁ v₂ : Val}
    (hArg : EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ op = some A)
    (hRes : EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ op = some B)
    (hcv₁ : Val.Closed v₁) (hcv₂ : Val.Closed v₂) (hvk : VrelK n A v₁ v₂) :
    CrelK n (CTy.F q B) φ (Comp.perform (Val.vcap m ℓ) op v₁) (Comp.perform (Val.vcap m ℓ) op v₂) := by
  -- ◊inc-5 STOP-AND-SHOW (the FROZEN-lr_sound guard, the value-carried mirror of the old ADR-0043 `:1707`
  -- seam). `Source.step (g, K₁, perform (vcap m ℓ) op v₁) = (idDispatch K₁ m ℓ op v₁).map (g, ·)`. To run
  -- the decomp (`krelS_splitAtId_decomp hK`) we first need `splitAtId K₁ m = some (Kᵢ, h, Kₒ)` AND the
  -- fail-loud guard `handlesOp h ℓ op = true` — i.e. `CapResolves K₁ m ℓ op` (the cap NON-ESCAPES in K₁).
  -- `KrelS` is purely structural + resume; it does NOT carry cap-resolution. And the resume values feed
  -- the guarded `crelK_ret`'s `CapsBelow 0` premise + a counter-bridge (the dispatched `g` vs the canonical
  -- `handlerCount Sᵢ`, `run_bump`). BOTH obligations are NonEscape/cap-scopedness facts about the OBSERVATION
  -- context K₁ — which the FROZEN `lr_sound`/`lr_fundamental` statements (Spec.lean) do not provide. So this
  -- arm PROPAGATES UP to the frozen statement: it is the ADR-0056/0057 escape-discipline question (B-occ,
  -- task #23), not internally dischargeable from `KrelS` alone. Held as a named sorry pending ADR-0057
  -- (the dissolution lemma `HasConfigTy ⟹ NonEscape` + the `CapsBelow` discharge it licenses).
  sorry

/-- ADR-0058 route 1: `KrelS` is INDEPENDENT of the threaded fresh-id counter `g`. The counter only
pins the nil return-half (discharged at ANY `g` by `⟨1,v₂,rfl⟩`, a `ret` converges regardless) and
threads through the resume conjunct (recursively re-cast at `m < n`). MINT advances `g → g+1`, so
running a handle body through the freshly pushed `handleF g` frame needs the ambient observation tail
re-cast from the pre-MINT `g` to the post-MINT `g+1`. Well-founded on `(n, K₁.length)`: tail recursion
drops the length at fixed `n`; the conjunct recursion drops `n` (`m < n`) at an arbitrary `Kᵢ`. -/
theorem KrelS_g_cast : ∀ (n : Nat) {C D : CTy Eff Mult} {ε : Eff} (g g' : Nat) (K₁ K₂ : Stack),
    KrelS n C D ε g K₁ K₂ → KrelS n C D ε g' K₁ K₂
  | _, _, _, _, _, _, [], [], hK => by
      rw [krelS_nil] at hK ⊢
      exact ⟨hK.1, fun q A hC v₁ v₂ _ _ _ _ => ⟨1, v₂, rfl⟩⟩
  | n, _, _, _, g, g', (Frame.letF N₁ :: K₁'), (Frame.letF N₂ :: K₂'), hK => by
      rw [krelS_letF] at hK ⊢
      obtain ⟨q, A, B, φ, hC, hbody, htail⟩ := hK
      exact ⟨q, A, B, φ, hC, hbody, KrelS_g_cast n g g' K₁' K₂' htail⟩
  | n, _, _, _, g, g', (Frame.appF w₁ :: K₁'), (Frame.appF w₂ :: K₂'), hK => by
      rw [krelS_appF] at hK ⊢
      obtain ⟨q, A, B, hC, hcw₁, hcw₂, hw, htail⟩ := hK
      exact ⟨q, A, B, hC, hcw₁, hcw₂, hw, KrelS_g_cast n g g' K₁' K₂' htail⟩
  | n, _, _, _, g, g', (Frame.handleF nh h :: K₁'), (Frame.handleF nh' h' :: K₂'), hK => by
      rw [krelS_handleF] at hK ⊢
      obtain ⟨hid, hh, htail, hres⟩ := hK
      refine ⟨hid, hh, KrelS_g_cast n g g' K₁' K₂' htail, ?_⟩
      intro m hm op w₁ w₂ Cᵢ εᵢ Kᵢ Kᵢ' cfg₁ cfg₂ hcatch hcw₁ hcw₂ hVrel hKi hCᵢ hd₁ hd₂
      obtain ⟨qᵣ, Aᵣ, r₁, r₂, Sᵢ, Sᵢ', eₛ, hcfg1, hcfg2, hcr1, hcr2, hvr, hSk⟩ :=
        hres m hm op w₁ w₂ Cᵢ εᵢ Kᵢ Kᵢ' cfg₁ cfg₂ hcatch hcw₁ hcw₂ hVrel
          (KrelS_g_cast m g' g Kᵢ Kᵢ' hKi) hCᵢ hd₁ hd₂
      exact ⟨qᵣ, Aᵣ, r₁, r₂, Sᵢ, Sᵢ', eₛ, hcfg1, hcfg2, hcr1, hcr2, hvr,
        KrelS_g_cast m g g' Sᵢ Sᵢ' hSk⟩
  | _, _, _, _, _, _, [], (_ :: _), hK => by simp only [KrelS] at hK
  | _, _, _, _, _, _, (_ :: _), [], hK => by simp only [KrelS] at hK
  | _, _, _, _, _, _, (Frame.letF _ :: _), (Frame.appF _ :: _), hK => by simp only [KrelS] at hK
  | _, _, _, _, _, _, (Frame.letF _ :: _), (Frame.handleF _ _ :: _), hK => by simp only [KrelS] at hK
  | _, _, _, _, _, _, (Frame.appF _ :: _), (Frame.letF _ :: _), hK => by simp only [KrelS] at hK
  | _, _, _, _, _, _, (Frame.appF _ :: _), (Frame.handleF _ _ :: _), hK => by simp only [KrelS] at hK
  | _, _, _, _, _, _, (Frame.handleF _ _ :: _), (Frame.letF _ :: _), hK => by simp only [KrelS] at hK
  | _, _, _, _, _, _, (Frame.handleF _ _ :: _), (Frame.appF _ :: _), hK => by simp only [KrelS] at hK
termination_by n _ _ _ _ _ K₁ _ _ => (n, K₁.length)
decreasing_by
  all_goals simp_wf
  · exact Prod.Lex.right _ (by simp)
  · exact Prod.Lex.right _ (by simp)
  · exact Prod.Lex.right _ (by simp)
  · exact Prod.Lex.left _ _ hm
  · exact Prod.Lex.left _ _ hm

/-- ◊4.5b the `handleThrows` compat core at `CrelK`, ADR-0054/0055 cap-binding. MINT
`(g, K, handle (throws ℓ) M) ↦ (g+1, handleF g (throws ℓ)::K, subst (vcap g ℓ) M)` — the handle BINDS
the capability `vcap g ℓ` at body var 0 (the SAME fresh `g` it pushes). So the premise is CAP-QUANTIFIED
`∀ gid, CrelK … (subst (vcap gid ℓ) M₁) (subst (vcap gid ℓ) M₂)` (the body related under the cap binder,
parallel `compatK_lam`); instantiated at the minted `gid := g`. The observation counter advances to
`g+1`, so the ambient tail `hK` is re-cast `g → g+1` via `KrelS_g_cast`. The block discharges `ℓ` from
`e` to `φ`. shape: biernacki-popl18 §5.4 (throws zero-shot arm). -/
theorem compatK_handleThrows {n : Nat} {q : Mult} {A : VTy Eff Mult} {e φ : Eff} {ℓ : Label}
    {M₁ M₂ : Comp}
    (hArg : EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "raise" = some A)
    (hbody : ∀ gid, CrelK n (CTy.F q A) e
      (Comp.subst (Val.vcap gid ℓ) M₁) (Comp.subst (Val.vcap gid ℓ) M₂)) :
    CrelK n (CTy.F q A) φ (Comp.handle (Handler.throws ℓ) M₁) (Comp.handle (Handler.throws ℓ) M₂) := by
  rw [CrelK]
  intro g D K₁ K₂ hK
  refine coApproxC_le_reduce
    (cfg₁' := (g + 1, Frame.handleF g (Handler.throws ℓ) :: K₁, Comp.subst (Val.vcap g ℓ) M₁))
    (cfg₂' := (g + 1, Frame.handleF g (Handler.throws ℓ) :: K₂, Comp.subst (Val.vcap g ℓ) M₂))
    rfl (by intro g' u; simp) rfl (by intro g' u; simp) ?_
  have hb := hbody g
  rw [CrelK] at hb
  refine hb (g + 1) D (Frame.handleF g (Handler.throws ℓ) :: K₁)
    (Frame.handleF g (Handler.throws ℓ) :: K₂)
    (krelS_handleF_intro (nh := g) (by simp only [HandlerRel])
      (KrelS_g_cast n g (g + 1) K₁ K₂ hK) ?_)
  -- THROWS resume supply: `dispatchOn op w (Kᵢ, throws ℓ, Kⱼ) = (Kⱼ, ret w)` (zero-shot abort — Kᵢ
  -- DISCARDED). `handlesOp` forces `op = "raise"`, so `opArg ℓ "raise" = A` (hArg) gives `VrelK m A w`;
  -- the dispatched config IS the tail's return-half on the re-cast (`g+1`) tail at hole `F q A`.
  intro m hm op w₁ w₂ Cᵢ εᵢ Kᵢ Kᵢ' cfg₁ cfg₂ hcatch hcw₁ hcw₂ hVrel _hKi _hCᵢ hd₁ hd₂
  have hop : op = "raise" := by
    simp only [Handler.label, handlesOp, Bool.and_eq_true, beq_iff_eq] at hcatch; exact hcatch.2
  subst hop
  have hw : VrelK m A w₁ w₂ := hVrel A (by rw [Handler.label]; exact hArg)
  simp only [dispatchOn] at hd₁ hd₂
  obtain rfl := (Option.some.injEq _ _).mp hd₁.symm
  obtain rfl := (Option.some.injEq _ _).mp hd₂.symm
  exact ⟨q, A, w₁, w₂, K₁, K₂, φ, rfl, rfl, hcw₁, hcw₂, hw,
    KrelS_mono (le_of_lt hm) (KrelS_g_cast n g (g + 1) K₁ K₂ hK)⟩

/-- ◊4.5b-append the `handleState` compat core at `CrelK`, ADR-0054/0055 cap-binding. MINT
`(g, K, handle (state ℓ s) M) ↦ (g+1, handleF g (state ℓ s)::K, subst (vcap g ℓ) M)`. CAP-QUANTIFIED
premise `hbody` (cap binds body var 0, parallel `compatK_lam`); the reinstalling stack is shown
`KrelS`-related at the minted frame id `g` and post-MINT counter `g+1` by `krelS_state_reinstall` (the
resumptive heart), the ambient tail re-cast `g → g+1` via `KrelS_g_cast`. The interface (get/put sig) +
the stored state's self-relation `hsv` are threaded from the caller's `HasCTy.handleState` typing. -/
theorem compatK_handleState {n : Nat} {q : Mult} {A S : VTy Eff Mult} {e φ : Eff} {ℓ : Label} {s : Val}
    {M₁ M₂ : Comp}
    (hgr : EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "get" = some S)
    (hp : EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "put" = some S)
    (hpr : EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "put" = some VTy.unit)
    (hrestrict : ∀ op s', Bang.handlesOp (Handler.state ℓ s') ℓ op = true → op = "get" ∨ op = "put")
    (hcs : Val.Closed s) (hsv : ∀ k, VrelK k S s s)
    (hbody : ∀ gid, CrelK n (CTy.F q A) e
      (Comp.subst (Val.vcap gid ℓ) M₁) (Comp.subst (Val.vcap gid ℓ) M₂)) :
    CrelK n (CTy.F q A) φ (Comp.handle (Handler.state ℓ s) M₁) (Comp.handle (Handler.state ℓ s) M₂) := by
  rw [CrelK]
  intro g D K₁ K₂ hK
  refine coApproxC_le_reduce
    (cfg₁' := (g + 1, Frame.handleF g (Handler.state ℓ s) :: K₁, Comp.subst (Val.vcap g ℓ) M₁))
    (cfg₂' := (g + 1, Frame.handleF g (Handler.state ℓ s) :: K₂, Comp.subst (Val.vcap g ℓ) M₂))
    rfl (by intro g' u; simp) rfl (by intro g' u; simp) ?_
  have hb := hbody g
  rw [CrelK] at hb
  -- discharge the row `φ → e` (`KrelS_eff_cast`) + counter `g → g+1` (`KrelS_g_cast`) on the tail.
  exact hb (g + 1) D (Frame.handleF g (Handler.state ℓ s) :: K₁)
    (Frame.handleF g (Handler.state ℓ s) :: K₂)
    (krelS_state_reinstall hgr hp hpr hrestrict g n s s hcs hcs (hsv n) K₁ K₂
      (KrelS_g_cast n g (g + 1) K₁ K₂ (KrelS_eff_cast hK)))

/-- ◊4.5b the `handleTransaction` compat core at `CrelK`, ADR-0054/0055 cap-binding. The multi-cell
resumptive analogue — same MINT shape (`handleF g (transaction ℓ Θ)::K`, `subst (vcap g ℓ)`, counter
`g+1`); the cap-QUANTIFIED body runs through the reinstalling stack via `krelS_transaction_reinstall`,
tail re-cast `g → g+1`. The heap `Θ` is arbitrary. -/
theorem compatK_handleTransaction {n : Nat} {q : Mult} {A : VTy Eff Mult} {e φ : Eff} {ℓ : Label}
    {Θ : Store} {M₁ M₂ : Comp}
    (hnewA : EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "newTVar" = some VTy.int)
    (hnewR : EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "newTVar" = some VTy.int)
    (hreadA : EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "readTVar" = some VTy.int)
    (hreadR : EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "readTVar" = some VTy.int)
    (hwriteA : EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "writeTVar"
      = some (VTy.prod (VTy.int : VTy Eff Mult) VTy.int))
    (hwriteR : EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "writeTVar" = some VTy.unit)
    (hrestrict : ∀ op Θ', Bang.handlesOp (Handler.transaction ℓ Θ') ℓ op = true →
      op = "newTVar" ∨ op = "readTVar" ∨ op = "writeTVar")
    (hheap : HeapRel Eff Mult n Θ Θ)
    (hbody : ∀ gid, CrelK n (CTy.F q A) e
      (Comp.subst (Val.vcap gid ℓ) M₁) (Comp.subst (Val.vcap gid ℓ) M₂)) :
    CrelK n (CTy.F q A) φ (Comp.handle (Handler.transaction ℓ Θ) M₁)
                          (Comp.handle (Handler.transaction ℓ Θ) M₂) := by
  rw [CrelK]
  intro g D K₁ K₂ hK
  refine coApproxC_le_reduce
    (cfg₁' := (g + 1, Frame.handleF g (Handler.transaction ℓ Θ) :: K₁, Comp.subst (Val.vcap g ℓ) M₁))
    (cfg₂' := (g + 1, Frame.handleF g (Handler.transaction ℓ Θ) :: K₂, Comp.subst (Val.vcap g ℓ) M₂))
    rfl (by intro g' u; simp) rfl (by intro g' u; simp) ?_
  have hb := hbody g
  rw [CrelK] at hb
  exact hb (g + 1) D (Frame.handleF g (Handler.transaction ℓ Θ) :: K₁)
    (Frame.handleF g (Handler.transaction ℓ Θ) :: K₂)
    (krelS_transaction_reinstall hnewA hnewR hreadA hreadR hwriteA hwriteR hrestrict g n Θ Θ hheap
      K₁ K₂ (KrelS_g_cast n g (g + 1) K₁ K₂ (KrelS_eff_cast hK)))


/-- A well-typed value is `ScopedIn Γ.length` (`HasVTy.shift_closed`: shifting at a cutoff `≥ Γ.length`
is the identity). The bridge from the typing derivation to the syntactic scope bound that
`closeV_closed_scoped` consumes. -/
theorem HasVTy.scopedIn {γ : GradeVec Mult} {Γ : TyCtx Eff Mult} {v : Val} {A : VTy Eff Mult}
    (h : HasVTy γ Γ v A) : Val.ScopedIn Γ.length v := fun k hk => h.shift_closed k hk

/-- #44 STAGE 5: a member clause of a `HasClauses ℓ P cl` list is a typed `ret`-clause — the per-op
inversion (`ret w` shape + arg/res sig + `w`'s open typing). Local public twin of Soundness' private
`HasClauses.mem_typed`. vrelK_fund-free, so before the mutual block. -/
theorem hasClauses_mem_typed {ℓ : Label} {P : VTy Eff Mult} :
    ∀ {cl : List (OpId × Comp)}, HasClauses (Eff := Eff) (Mult := Mult) ℓ P cl →
    ∀ {op' : OpId} {body : Comp}, (op', body) ∈ cl →
    ∃ (opA opR : VTy Eff Mult) (qa qp : Mult) (w : Val),
      body = Comp.ret w
      ∧ EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ op' = some opA
      ∧ EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ op' = some opR
      ∧ HasVTy (qa :: qp :: []) (opA :: P :: []) w opR
  | [], _, _, _, hmem => by simp at hmem
  | (_ :: _), h, op', body, hmem => by
    cases h with
    | @cons _ _ op w rest opA opR qa qp hoa hor hw htail =>
      rcases List.mem_cons.mp hmem with heq | htl
      · obtain ⟨ho, hb⟩ := Prod.mk.injEq .. ▸ heq
        subst ho; subst hb; exact ⟨opA, opR, qa, qp, w, rfl, hoa, hor, hw⟩
      · exact hasClauses_mem_typed htail htl

/-- `find?`-flavoured wrapper of `hasClauses_mem_typed`: a `find? (·.1==op)`-matched clause is typed, and
its op IS `op` (the `find?` predicate). -/
theorem hasClauses_find?_typed {ℓ : Label} {P : VTy Eff Mult} {cl : List (OpId × Comp)}
    (hcl : HasClauses (Eff := Eff) (Mult := Mult) ℓ P cl) {op : OpId} {clause : OpId × Comp}
    (hf : cl.find? (·.1 == op) = some clause) :
    ∃ (opA opR : VTy Eff Mult) (qa qp : Mult) (w : Val),
      clause.2 = Comp.ret w
      ∧ EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ clause.1 = some opA
      ∧ EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ clause.1 = some opR
      ∧ HasVTy (qa :: qp :: []) (opA :: P :: []) w opR := by
  obtain ⟨op', body⟩ := clause
  exact hasClauses_mem_typed hcl (List.mem_of_find?_eq_some hf)

/-- #44 STAGE 5 (debt 2, sub-proof W-c) — the RESUME-VALUE PRODUCER, parameterized by the fundamental
lemma `vf` (= `vrelK_fund`). Taking `vf` as a hypothesis (rather than referencing `vrelK_fund` directly)
lets this live BEFORE the mutual block, so the in-block `crelK_fund` custom arm calls it as a SINGLE thin
application (`vf := @vrelK_fund …`, the recursive self-reference) — keeping the block's heartbeat budget
clean — while `krelS_refl`/`custom_clause_resume` (after the block) pass the same `vf`. From `HasClauses ℓ
P cl` + `HasVTy [] [] p P`: every matched clause's double-`subst` resume focus is a `ret` of related
closed values at the op's result type (`custom_resume_is_ret` + `closeV_closed_scoped` + `vf`). -/
theorem custom_clause_resume_of {ℓ : Label} {P : VTy Eff Mult} {cl : List (OpId × Comp)} {p : Val}
    (vf : ∀ {γ : GradeVec Mult} {Γ : TyCtx Eff Mult} {v : Val} {A : VTy Eff Mult},
      HasVTy γ Γ v A → ∀ (n : Nat) (δ₁ δ₂ : List Val), EnvRelK n Γ δ₁ δ₂ →
        VrelK n A (closeV δ₁ v) (closeV δ₂ v))
    (hcl : HasClauses (Eff := Eff) (Mult := Mult) ℓ P cl)
    (hp : HasVTy (Eff := Eff) (Mult := Mult) [] [] p P) :
    ∀ (k : Nat) (op : OpId) (clause : OpId × Comp) (v₁ v₂ : Val),
      cl.find? (·.1 == op) = some clause → Val.Closed v₁ → Val.Closed v₂ →
      (∀ Aop, EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ op = some Aop → VrelK k Aop v₁ v₂) →
      ∃ (Aᵣ : VTy Eff Mult) (r₁ r₂ : Val),
        EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ op = some Aᵣ ∧
        Comp.subst p (Comp.subst (Val.shift v₁) clause.2) = Comp.ret r₁ ∧
        Comp.subst p (Comp.subst (Val.shift v₂) clause.2) = Comp.ret r₂ ∧
        Val.Closed r₁ ∧ Val.Closed r₂ ∧ VrelK k Aᵣ r₁ r₂ := by
  intro k op clause v₁ v₂ hf hcv₁ hcv₂ hVarg
  obtain ⟨opA, opR, qa, qp, w, hbody, hoa, hor, hw⟩ := hasClauses_find?_typed hcl hf
  have hop : clause.1 = op := by have := List.find?_some hf; simpa using this
  rw [hop] at hoa hor
  have hcp : Val.Closed p := fun j => hp.shift_closed j (Nat.zero_le j)
  have hsv₁ : Val.shift v₁ = v₁ := hcv₁.shift
  have hsv₂ : Val.shift v₂ = v₂ := hcv₂.shift
  have hcsv₁ : Val.Closed (Val.shift v₁) := by rw [hsv₁]; exact hcv₁
  have hcsv₂ : Val.Closed (Val.shift v₂) := by rw [hsv₂]; exact hcv₂
  have hwsc : Val.ScopedIn 2 w := by simpa using hw.scopedIn
  have hclosed : ∀ v', Val.Closed (Val.shift v') →
      Val.Closed (Val.subst p (Val.subst (Val.shift v') w)) := fun v' hcv' => by
    have := closeV_closed_scoped (δ := [Val.shift v', p]) (v := w)
      (by intro u hu; rcases List.mem_cons.mp hu with rfl | hu; exact hcv'
          rcases List.mem_cons.mp hu with rfl | hu; exact hcp; simp at hu)
      (by simpa using hwsc)
    simpa only [closeV, closeV_nil] using this
  refine ⟨opR, Val.subst p (Val.subst (Val.shift v₁) w), Val.subst p (Val.subst (Val.shift v₂) w),
    hor, ?_, ?_, hclosed v₁ hcsv₁, hclosed v₂ hcsv₂, ?_⟩
  · rw [hbody]; simp only [Comp.subst, Comp.substFrom]
  · rw [hbody]; simp only [Comp.subst, Comp.substFrom]
  · have hpv : VrelK (Eff := Eff) (Mult := Mult) k P p p := by
      have := vf hp k [] [] (EnvRelK_nil_iff k [] [] |>.mpr ⟨rfl, rfl⟩)
      rwa [closeV_closed hcp] at this
    have hδ : EnvRelK (Eff := Eff) (Mult := Mult) k (opA :: P :: [])
        [Val.shift v₁, p] [Val.shift v₂, p] := by
      rw [EnvRelK]
      refine ⟨hcsv₁, hcsv₂, ?_, hcp, hcp, hpv, EnvRelK_nil_iff k [] [] |>.mpr ⟨rfl, rfl⟩⟩
      rw [hsv₁, hsv₂]; exact hVarg opA hoa
    have := vf hw k [Val.shift v₁, p] [Val.shift v₂, p] hδ
    simpa only [closeV, closeV_nil] using this

/-- #44 STAGE 5 (debt 2) — the CUSTOM-reinstall lemma, the user-effect resumptive heart. A `custom ℓ p cl`
frame over a `KrelS`-related tail self-relates at every index; the resume conjunct is supplied by GUARDED
RECURSION on the index — the exact skeleton of `krelS_state_reinstall`, STRICTLY SIMPLER (the reinstall
diagonal is `p=p, cl=cl`: v1 is a READ-ONLY param, so the reinstalled frame is the SAME handler, unlike
state's `put`, which reinstalls a *changed* value). The resume value is `subst pⱼ (subst (shift vⱼ)
clause.2)`, a `ret`-of-closed-value by the ADR-0092 §D3 ret-shape; the value relation + ret-decomposition
are supplied by the `hclause` premise (proven at the call site via `clause_resume_vrel` + `custom_resume_is_ret`,
which need `vrelK_fund` — hence threaded IN, mirroring `state`'s `hsv`). shape: biernacki-popl18 §5.4. -/
theorem krelS_custom_reinstall {q : Mult} {A P : VTy Eff Mult} {D : CTy Eff Mult} {φ : Eff}
    {ℓ : Label} {g : Nat} {cl : List (OpId × Comp)}
    (hcl : HasClauses (Eff := Eff) (Mult := Mult) ℓ P cl)
    (hrestrict : ∀ op p', Bang.handlesOp (Handler.custom ℓ p' cl) ℓ op = true →
      (cl.find? (·.1 == op)).isSome) :
    ∀ (nh : Nat) m (p₁ p₂ : Val), Val.Closed p₁ → Val.Closed p₂ →
      VrelK (Eff := Eff) (Mult := Mult) m P p₁ p₂ →
      -- the resume-value producer: for the matched clause + related closed op-args, the double-subst
      -- resume focus is a `ret` of related closed values at the op's result type (ret-shape + clause_resume_vrel).
      (∀ (k : Nat) (op : OpId) (clause : OpId × Comp) (v₁ v₂ : Val),
        cl.find? (·.1 == op) = some clause → Val.Closed v₁ → Val.Closed v₂ →
        (∀ Aop, EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ op = some Aop → VrelK k Aop v₁ v₂) →
        ∃ (Aᵣ : VTy Eff Mult) (r₁ r₂ : Val),
          EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ op = some Aᵣ ∧
          Comp.subst p₁ (Comp.subst (Val.shift v₁) clause.2) = Comp.ret r₁ ∧
          Comp.subst p₂ (Comp.subst (Val.shift v₂) clause.2) = Comp.ret r₂ ∧
          Val.Closed r₁ ∧ Val.Closed r₂ ∧ VrelK k Aᵣ r₁ r₂) →
      ∀ (K₁ K₂ : Stack), KrelS m (CTy.F q A) D φ g K₁ K₂ →
      KrelS m (CTy.F q A) D φ g (Frame.handleF nh (Handler.custom ℓ p₁ cl) :: K₁)
                              (Frame.handleF nh (Handler.custom ℓ p₂ cl) :: K₂) := by
  intro nh m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro p₁ p₂ hcp₁ hcp₂ hpv hclause K₁ K₂ hK
    refine krelS_handleF_intro
      (show HandlerRel Eff Mult m (Handler.custom ℓ p₁ cl) (Handler.custom ℓ p₂ cl) from
        ⟨rfl, rfl, P, hpv, hcl⟩) hK ?_
    intro m' hm' op w₁ w₂ Cᵢ εᵢ Kᵢ Kᵢ' cfg₁ cfg₂ hcatch hcw₁ hcw₂ hVrel hKi hCᵢ hd₁ hd₂
    -- find? some (from hcatch via hrestrict), then the reinstall + resume.
    have hfs : (cl.find? (·.1 == op)).isSome := hrestrict op p₁ hcatch
    obtain ⟨clause, hf⟩ := Option.isSome_iff_exists.mp hfs
    obtain ⟨Aᵣ, r₁, r₂, hRes, hr₁, hr₂, hcr₁, hcr₂, hvr⟩ :=
      hclause m' op clause w₁ w₂ hf hcw₁ hcw₂ hVrel
    obtain ⟨qᵣ, rfl⟩ := hCᵢ Aᵣ (by rw [Handler.label]; exact hRes)
    simp only [Handler.label, dispatchOn, hf] at hd₁ hd₂
    rw [hr₁] at hd₁; rw [hr₂] at hd₂
    obtain rfl := (Option.some.injEq _ _).mp hd₁.symm
    obtain rfl := (Option.some.injEq _ _).mp hd₂.symm
    -- the reinstalled `custom ℓ p₁/p₂ cl` over the tail relates at m' (IH, SAME frame — read-only param).
    have hreinst := ih m' hm' p₁ p₂ hcp₁ hcp₂ (VrelK_mono (le_of_lt hm') hpv)
      (fun k op' clause' v₁' v₂' hf' hcv₁' hcv₂' hVr' =>
        hclause k op' clause' v₁' v₂' hf' hcv₁' hcv₂' hVr') K₁ K₂ (KrelS_mono (le_of_lt hm') hK)
    rw [krelS_handleF] at hreinst
    have happ := krelS_append (Dᵢ := CTy.F q A) hKi
      (show HandlerRel Eff Mult m' (Handler.custom ℓ p₁ cl) (Handler.custom ℓ p₂ cl) from
        ⟨rfl, rfl, P, VrelK_mono (le_of_lt hm') hpv, hcl⟩)
      (KrelS_mono (le_of_lt hm') hK) hreinst.2.2.2
    exact ⟨qᵣ, Aᵣ, r₁, r₂, _, _, εᵢ, rfl, rfl, hcr₁, hcr₂, hvr, happ⟩

/-- #44 STAGE 5 (debt 1) — the `handleCustom` compat core at `CrelK`. The direct analogue of
`compatK_handleState`: MINT `(g, K, handle (custom ℓ p cl) M) ↦ (g+1, handleF g (custom ℓ p cl)::K,
subst (vcap g ℓ) M)`, run the cap-quantified body `hbody` through the reinstalling stack
(`krelS_custom_reinstall`), tail re-cast `g → g+1`. The param self-relation `hpv` + the resume-value
producer `hclause` are threaded from the caller (built via `vrelK_fund`/`clause_resume_vrel` at the
`crelK_fund` call site — inside the mutual block, self-referencing `vrelK_fund`, exactly as the state arm
supplies `hsv`). No induction of its own; risk lives in debt 2. -/
theorem compatK_handleCustom {n : Nat} {q : Mult} {A P : VTy Eff Mult} {e φ : Eff} {ℓ : Label}
    {p : Val} {cl : List (OpId × Comp)} {M₁ M₂ : Comp}
    (hcl : HasClauses (Eff := Eff) (Mult := Mult) ℓ P cl)
    (hrestrict : ∀ op p', Bang.handlesOp (Handler.custom ℓ p' cl) ℓ op = true →
      (cl.find? (·.1 == op)).isSome)
    (hpv : ∀ k, VrelK (Eff := Eff) (Mult := Mult) k P p p)
    (hclause : ∀ (k : Nat) (op : OpId) (clause : OpId × Comp) (v₁ v₂ : Val),
        cl.find? (·.1 == op) = some clause → Val.Closed v₁ → Val.Closed v₂ →
        (∀ Aop, EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ op = some Aop → VrelK k Aop v₁ v₂) →
        ∃ (Aᵣ : VTy Eff Mult) (r₁ r₂ : Val),
          EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ op = some Aᵣ ∧
          Comp.subst p (Comp.subst (Val.shift v₁) clause.2) = Comp.ret r₁ ∧
          Comp.subst p (Comp.subst (Val.shift v₂) clause.2) = Comp.ret r₂ ∧
          Val.Closed r₁ ∧ Val.Closed r₂ ∧ VrelK k Aᵣ r₁ r₂)
    (hcp : Val.Closed p)
    (hbody : ∀ gid, CrelK n (CTy.F q A) e
      (Comp.subst (Val.vcap gid ℓ) M₁) (Comp.subst (Val.vcap gid ℓ) M₂)) :
    CrelK n (CTy.F q A) φ (Comp.handle (Handler.custom ℓ p cl) M₁)
                          (Comp.handle (Handler.custom ℓ p cl) M₂) := by
  rw [CrelK]
  intro g D K₁ K₂ hK
  refine coApproxC_le_reduce
    (cfg₁' := (g + 1, Frame.handleF g (Handler.custom ℓ p cl) :: K₁, Comp.subst (Val.vcap g ℓ) M₁))
    (cfg₂' := (g + 1, Frame.handleF g (Handler.custom ℓ p cl) :: K₂, Comp.subst (Val.vcap g ℓ) M₂))
    rfl (by intro g' u; simp) rfl (by intro g' u; simp) ?_
  have hb := hbody g
  rw [CrelK] at hb
  exact hb (g + 1) D (Frame.handleF g (Handler.custom ℓ p cl) :: K₁)
    (Frame.handleF g (Handler.custom ℓ p cl) :: K₂)
    (krelS_custom_reinstall hcl hrestrict g n p p hcp hcp (hpv n) hclause K₁ K₂
      (KrelS_g_cast n g (g + 1) K₁ K₂ (KrelS_eff_cast hK)))



/-! ### B.5′ ◊4.5b — the migrated fundamental theorem (`vrelK_fund` / `crelK_fund`) over `CrelK`/`KrelS`

The answer-typed migration of `vrel_fund`/`crel_fund`, wiring the `compatK_*` cores (sub-block c) over
`EnvRelK`. The non-handler cases and the 3 handler cases all CLOSE — the absolute-cap representation
dissolved the shift wall (`closeC_handle*` rewrite unshifted), so the arms close on their
`compatK_handle*` cores. The remaining obligations: `crelK_fund_up` holds ONE propagated `sorry` (the
ADR-0056/0057 cap-escape / B-occ question, task #23), plus the `krelS_splitAtId_decomp` SKIP relocation
residual. The Kripke continuation indices use `∀ m < n` at the letC/case/split seams (the `compatK_*`
cores' ▷-guarded shape) and `∀ j ≤ n` would over-supply. -/
mutual
theorem vrelK_fund_at {γ : GradeVec Mult} {Γ : TyCtx Eff Mult} (v : Val) {A : VTy Eff Mult}
    (h : HasVTy γ Γ v A) :
    ∀ (n : Nat) (δ₁ δ₂ : List Val), EnvRelK n Γ δ₁ δ₂ →
      VrelK n A (closeV δ₁ v) (closeV δ₂ v) := by
  match v, h with
  | Val.vunit, HasVTy.vunit => intro n δ₁ δ₂ _; rw [closeV_vunit, closeV_vunit, VrelK]; exact ⟨rfl, rfl⟩
  | Val.vint _, HasVTy.vint => intro n δ₁ δ₂ _; rw [closeV_vint, closeV_vint, VrelK]; exact ⟨_, rfl, rfl⟩
  | Val.vcap nid ℓ, HasVTy.vcap =>
      intro n δ₁ δ₂ _
      have hcap : Val.Closed (Val.vcap nid ℓ) := fun k => rfl
      rw [closeV_closed hcap, closeV_closed hcap, VrelK]
      exact ⟨nid, rfl, rfl⟩
  | Val.vvar i, HasVTy.vvar hget =>
      intro n δ₁ δ₂ hδ
      have hlen₁ := hδ.length_left
      have hlen₂ := hδ.length_right
      have hi : i < Γ.length := by rw [List.getElem?_eq_some_iff] at hget; exact hget.1
      rw [closeV_vvar (hδ.closed_left) (by omega) Val.vunit,
          closeV_vvar (hδ.closed_right) (by omega) Val.vunit]
      exact hδ.vrel_at hget Val.vunit Val.vunit
  | Val.vthunk M, HasVTy.vthunk hM =>
      intro n δ₁ δ₂ hδ
      rw [closeV_vthunk, closeV_vthunk, VrelK]
      exact ⟨closeC δ₁ M, closeC δ₂ M, rfl, rfl,
        fun j hjn => crelK_fund_at M hM j δ₁ δ₂ (EnvRelK_mono (Nat.le_of_lt hjn) hδ)⟩
  | Val.inl w, HasVTy.inl hw =>
      intro n δ₁ δ₂ hδ
      rw [closeV_inl, closeV_inl, VrelK]
      exact Or.inl ⟨_, _, rfl, rfl, vrelK_fund_at w hw n δ₁ δ₂ hδ⟩
  | Val.inr w, HasVTy.inr hw =>
      intro n δ₁ δ₂ hδ
      rw [closeV_inr, closeV_inr, VrelK]
      exact Or.inr ⟨_, _, rfl, rfl, vrelK_fund_at w hw n δ₁ δ₂ hδ⟩
  | Val.pair a b, HasVTy.pair ha hb hgr =>
      intro n δ₁ δ₂ hδ
      rw [closeV_pair, closeV_pair, VrelK]
      exact ⟨_, _, _, _, rfl, rfl, vrelK_fund_at a ha n δ₁ δ₂ hδ, vrelK_fund_at b hb n δ₁ δ₂ hδ⟩
  | Val.fold w, HasVTy.fold hw =>
      intro n δ₁ δ₂ hδ
      rw [closeV_fold, closeV_fold, VrelK]
      exact ⟨_, _, rfl, rfl,
        fun j hjn => vrelK_fund_at w hw j δ₁ δ₂ (EnvRelK_mono (Nat.le_of_lt hjn) hδ)⟩
termination_by sizeOf v
decreasing_by all_goals (simp_wf; try omega)

theorem crelK_fund_at {γ : GradeVec Mult} {Γ : TyCtx Eff Mult} (c : Comp) {e : Eff} {B : CTy Eff Mult}
    (h : HasCTy γ Γ c e B) :
    ∀ (n : Nat) (δ₁ δ₂ : List Val), EnvRelK n Γ δ₁ δ₂ →
      CrelK n B e (closeC δ₁ c) (closeC δ₂ c) := by
  match c, h with
  | Comp.ret v, HasCTy.ret hv _ =>
      intro n δ₁ δ₂ hδ
      rw [closeC_ret, closeC_ret]
      have hsc₁ : Val.Closed (closeV δ₁ v) :=
        closeV_closed_scoped hδ.closed_left (by have := hv.scopedIn; rwa [hδ.length_left])
      have hsc₂ : Val.Closed (closeV δ₂ v) :=
        closeV_closed_scoped hδ.closed_right (by have := hv.scopedIn; rwa [hδ.length_right])
      rw [CrelK]; intro g D K₁ K₂ hK
      exact crelK_ret g D K₁ K₂ hK hsc₁ hsc₂ (vrelK_fund_at v hv n δ₁ δ₂ hδ)
  | Comp.letC M N, HasCTy.letC (A := A) hM hN _ =>
      intro n δ₁ δ₂ hδ
      rw [closeC_letC, closeC_letC]
      refine compatK_letC (crelK_fund_at M hM n δ₁ δ₂ hδ) ?_
      intro m hmn v₁ v₂ hcv₁ hcv₂ hvrel
      rw [closeC_subst_comm hδ.closed_left hcv₁, closeC_subst_comm hδ.closed_right hcv₂]
      have hδ' : EnvRelK m (A :: Γ) (v₁ :: δ₁) (v₂ :: δ₂) := by
        rw [EnvRelK]; exact ⟨hcv₁, hcv₂, hvrel, EnvRelK_mono (Nat.le_of_lt hmn) hδ⟩
      have := crelK_fund_at N hN m (v₁ :: δ₁) (v₂ :: δ₂) hδ'
      rwa [show closeC (v₁ :: δ₁) N = closeC δ₁ (Comp.subst v₁ N) from rfl,
           show closeC (v₂ :: δ₂) N = closeC δ₂ (Comp.subst v₂ N) from rfl] at this
  | Comp.force v, HasCTy.force hv =>
      intro n δ₁ δ₂ hδ
      rw [closeC_force, closeC_force]
      exact crelK_force (vrelK_fund_at v hv n δ₁ δ₂ hδ)
  | Comp.lam M, HasCTy.lam (A := A) hM =>
      intro n δ₁ δ₂ hδ
      rw [closeC_lam, closeC_lam]
      refine compatK_lam ?_
      intro w₁ w₂ hcw₁ hcw₂ hw
      rw [closeC_subst_comm hδ.closed_left hcw₁, closeC_subst_comm hδ.closed_right hcw₂]
      have hδ' : EnvRelK n (A :: Γ) (w₁ :: δ₁) (w₂ :: δ₂) := by
        rw [EnvRelK]; exact ⟨hcw₁, hcw₂, hw, hδ⟩
      have := crelK_fund_at M hM n (w₁ :: δ₁) (w₂ :: δ₂) hδ'
      rwa [show closeC (w₁ :: δ₁) M = closeC δ₁ (Comp.subst w₁ M) from rfl,
           show closeC (w₂ :: δ₂) M = closeC δ₂ (Comp.subst w₂ M) from rfl] at this
  | Comp.app M v, HasCTy.app hM hv _ =>
      intro n δ₁ δ₂ hδ
      rw [closeC_app, closeC_app]
      have hscv₁ : Val.Closed (closeV δ₁ v) :=
        closeV_closed_scoped hδ.closed_left (by have := hv.scopedIn; rwa [hδ.length_left])
      have hscv₂ : Val.Closed (closeV δ₂ v) :=
        closeV_closed_scoped hδ.closed_right (by have := hv.scopedIn; rwa [hδ.length_right])
      exact compatK_app (crelK_fund_at M hM n δ₁ δ₂ hδ) hscv₁ hscv₂ (vrelK_fund_at v hv n δ₁ δ₂ hδ)
  | Comp.case v N₁ N₂, HasCTy.case (A := A) (B := Bc) hv hN₁ hN₂ _ =>
      intro n δ₁ δ₂ hδ
      rw [closeC_case, closeC_case]
      have hscv₁ : Val.Closed (closeV δ₁ v) :=
        closeV_closed_scoped hδ.closed_left (by have := hv.scopedIn; rwa [hδ.length_left])
      have hscv₂ : Val.Closed (closeV δ₂ v) :=
        closeV_closed_scoped hδ.closed_right (by have := hv.scopedIn; rwa [hδ.length_right])
      refine compatK_case (vrelK_fund_at v hv n δ₁ δ₂ hδ) hscv₁ hscv₂ ?_ ?_
      · intro m hm u₁ u₂ hcu₁ hcu₂ hu
        rw [closeC_subst_comm hδ.closed_left hcu₁, closeC_subst_comm hδ.closed_right hcu₂]
        have hδ' : EnvRelK m (A :: Γ) (u₁ :: δ₁) (u₂ :: δ₂) := by
          rw [EnvRelK]; exact ⟨hcu₁, hcu₂, hu, EnvRelK_mono (Nat.le_of_lt hm) hδ⟩
        exact crelK_fund_at N₁ hN₁ m (u₁ :: δ₁) (u₂ :: δ₂) hδ'
      · intro m hm u₁ u₂ hcu₁ hcu₂ hu
        rw [closeC_subst_comm hδ.closed_left hcu₁, closeC_subst_comm hδ.closed_right hcu₂]
        have hδ' : EnvRelK m (Bc :: Γ) (u₁ :: δ₁) (u₂ :: δ₂) := by
          rw [EnvRelK]; exact ⟨hcu₁, hcu₂, hu, EnvRelK_mono (Nat.le_of_lt hm) hδ⟩
        exact crelK_fund_at N₂ hN₂ m (u₁ :: δ₁) (u₂ :: δ₂) hδ'
  | Comp.split v N, HasCTy.split (A := A) (B := Bs) hv hN _ =>
      intro n δ₁ δ₂ hδ
      rw [closeC_split, closeC_split]
      have hscv₁ : Val.Closed (closeV δ₁ v) :=
        closeV_closed_scoped hδ.closed_left (by have := hv.scopedIn; rwa [hδ.length_left])
      have hscv₂ : Val.Closed (closeV δ₂ v) :=
        closeV_closed_scoped hδ.closed_right (by have := hv.scopedIn; rwa [hδ.length_right])
      refine compatK_split (vrelK_fund_at v hv n δ₁ δ₂ hδ) hscv₁ hscv₂ ?_
      intro m hm a₁ a₂ b₁ b₂ hca₁ hca₂ hcb₁ hcb₂ ha hb
      rw [closeC_subst2_comm hδ.closed_left hca₁ hcb₁, closeC_subst2_comm hδ.closed_right hca₂ hcb₂]
      have hδ' : EnvRelK m (Bs :: A :: Γ) (b₁ :: a₁ :: δ₁) (b₂ :: a₂ :: δ₂) := by
        rw [EnvRelK]; refine ⟨hcb₁, hcb₂, hb, ?_⟩; rw [EnvRelK]
        exact ⟨hca₁, hca₂, ha, EnvRelK_mono (Nat.le_of_lt hm) hδ⟩
      have := crelK_fund_at N hN m (b₁ :: a₁ :: δ₁) (b₂ :: a₂ :: δ₂) hδ'
      rwa [show closeC (b₁ :: a₁ :: δ₁) N = closeC δ₁ (Comp.subst a₁ (Comp.subst b₁ N)) from rfl,
           show closeC (b₂ :: a₂ :: δ₂) N = closeC δ₂ (Comp.subst a₂ (Comp.subst b₂ N)) from rfl] at this
  | Comp.unfold v, HasCTy.unfold hv =>
      intro n δ₁ δ₂ hδ
      rw [closeC_unfold, closeC_unfold]
      match v, hv with
      | Val.fold a, HasVTy.fold ha =>
          rw [closeV_fold, closeV_fold]
          have hsa₁ : Val.Closed (closeV δ₁ a) :=
            closeV_closed_scoped hδ.closed_left (by have := ha.scopedIn; rwa [hδ.length_left])
          have hsa₂ : Val.Closed (closeV δ₂ a) :=
            closeV_closed_scoped hδ.closed_right (by have := ha.scopedIn; rwa [hδ.length_right])
          refine CrelK_head_step (c₁' := Comp.ret (closeV δ₁ a)) (c₂' := Comp.ret (closeV δ₂ a))
            ⟨fun _ _ => rfl, by intro u; simp⟩ ⟨fun _ _ => rfl, by intro u; simp⟩ ?_
          intro m hm
          rw [CrelK]; intro g D K₁ K₂ hK
          exact crelK_ret g D K₁ K₂ hK hsa₁ hsa₂ (vrelK_fund_at a ha m δ₁ δ₂ (EnvRelK_mono (le_of_lt hm) hδ))
      | Val.vvar i, HasVTy.vvar hget =>
          have hsc₁ : Val.Closed (closeV δ₁ (Val.vvar i)) :=
            closeV_closed_scoped hδ.closed_left (by
              have := (HasVTy.vvar hget).scopedIn; rwa [hδ.length_left])
          have hsc₂ : Val.Closed (closeV δ₂ (Val.vvar i)) :=
            closeV_closed_scoped hδ.closed_right (by
              have := (HasVTy.vvar hget).scopedIn; rwa [hδ.length_right])
          exact crelK_unfold hsc₁ hsc₂ (vrelK_fund_at (Val.vvar i) (HasVTy.vvar hget) n δ₁ δ₂ hδ)
  | Comp.binop op v w, HasCTy.binop hv hw _ =>
      -- ADR-0065 stage ④ / ctr slice 6 (DEFERRED — the LR obligation is sequenced LAST, off the
      -- soundness critical path; `docs/notes/ctr-design.md` §3 ripple, §4.2 slice 6). The binop δ-step
      -- `binop op (vint a) (vint b) ↦ ret (op.eval a b)` is a pure head-step (the `unfold`-arm shape,
      -- `CrelK_head_step` + `crelK_ret`), BUT it only fires once BOTH operands close to `vint` literals.
      -- Relating the two closings requires `VrelK n int (closeV δ₁ v) (closeV δ₂ v)` to force EQUAL
      -- `vint` literals (int's VrelK is literal-equality), then a `crelK`-step to the equal `op.eval`
      -- results. That is genuine binary-LR work (a new `crelK_binop` step-lemma, the twin of
      -- `crelK_unfold`), and it lives in the already-`sorryAx` `lr_fundamental` cluster — NOT in the
      -- kernel-typing + soundness slice this lane (task #36) discharges. MISSING: a `crelK_binop`
      -- lemma (`VrelK int ⇒ equal vints ⇒ CrelK on the equal δ-reducts). shape: biernacki-popl18 §5.4.
      sorry
  | Comp.perform cc op v, HasCTy.perform hcap _hℓ hArg hRes hv =>
      intro n δ₁ δ₂ hδ
      rw [closeC_perform, closeC_perform]
      have hck : VrelK n (VTy.cap _) (closeV δ₁ cc) (closeV δ₂ cc) := vrelK_fund_at cc hcap n δ₁ δ₂ hδ
      rw [VrelK] at hck
      obtain ⟨mid, hc1, hc2⟩ := hck
      rw [hc1, hc2]
      have hvk : VrelK n _ (closeV δ₁ v) (closeV δ₂ v) := vrelK_fund_at v hv n δ₁ δ₂ hδ
      have hcv₁ : Val.Closed (closeV δ₁ v) :=
        closeV_closed_scoped hδ.closed_left (by have := hv.scopedIn; rwa [hδ.length_left])
      have hcv₂ : Val.Closed (closeV δ₂ v) :=
        closeV_closed_scoped hδ.closed_right (by have := hv.scopedIn; rwa [hδ.length_right])
      exact crelK_fund_up hArg hRes hcv₁ hcv₂ hvk
  | Comp.handle (Handler.throws ℓ) M, HasCTy.handleThrows (e := e) hArg _hIface hM _hsub _hBocc =>
      intro n δ₁ δ₂ hδ
      rw [closeC_handleThrows, closeC_handleThrows]
      refine compatK_handleThrows (e := e) hArg (fun gid => ?_)
      have hclosed : Val.Closed (Val.vcap gid ℓ) := fun k => rfl
      rw [closeC_subst_comm hδ.closed_left hclosed, closeC_subst_comm hδ.closed_right hclosed]
      have hδ' : EnvRelK n (VTy.cap ℓ :: Γ) (Val.vcap gid ℓ :: δ₁) (Val.vcap gid ℓ :: δ₂) := by
        rw [EnvRelK]
        exact ⟨hclosed, hclosed,
          (show VrelK n (VTy.cap ℓ) (Val.vcap gid ℓ) (Val.vcap gid ℓ) by
            rw [VrelK]; exact ⟨gid, rfl, rfl⟩), hδ⟩
      have := crelK_fund_at M hM n (Val.vcap gid ℓ :: δ₁) (Val.vcap gid ℓ :: δ₂) hδ'
      rwa [show closeC (Val.vcap gid ℓ :: δ₁) M = closeC δ₁ (Comp.subst (Val.vcap gid ℓ) M) from rfl,
           show closeC (Val.vcap gid ℓ :: δ₂) M = closeC δ₂ (Comp.subst (Val.vcap gid ℓ) M) from rfl]
        at this
  | Comp.handle (Handler.state ℓ s₀) M, HasCTy.handleState (e := e) _hga hgr hp hpr _hrestrict hs hM _hsub _hBocc =>
      intro n δ₁ δ₂ hδ
      rw [closeC_handleState, closeC_handleState]
      have hcs₀ : Val.Closed s₀ := fun k => hs.shift_closed k (Nat.zero_le k)
      rw [closeV_closed hcs₀, closeV_closed hcs₀]
      have hsv : ∀ k, VrelK k _ s₀ s₀ := fun k => by
        have := vrelK_fund_at s₀ hs k [] [] (EnvRelK_nil_iff k [] [] |>.mpr ⟨rfl, rfl⟩)
        rwa [closeV_closed hcs₀] at this
      have hrestrict' : ∀ op s', Bang.handlesOp (Handler.state ℓ s') ℓ op = true → op = "get" ∨ op = "put" :=
        fun op s' hc => by
          simp only [handlesOp, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc
          rcases hc.2 with rfl | rfl <;> simp
      refine compatK_handleState (e := e) hgr hp hpr hrestrict' hcs₀ hsv (fun gid => ?_)
      have hclosed : Val.Closed (Val.vcap gid ℓ) := fun k => rfl
      rw [closeC_subst_comm hδ.closed_left hclosed, closeC_subst_comm hδ.closed_right hclosed]
      have hδ' : EnvRelK n (VTy.cap ℓ :: Γ) (Val.vcap gid ℓ :: δ₁) (Val.vcap gid ℓ :: δ₂) := by
        rw [EnvRelK]
        exact ⟨hclosed, hclosed,
          (show VrelK n (VTy.cap ℓ) (Val.vcap gid ℓ) (Val.vcap gid ℓ) by
            rw [VrelK]; exact ⟨gid, rfl, rfl⟩), hδ⟩
      have := crelK_fund_at M hM n (Val.vcap gid ℓ :: δ₁) (Val.vcap gid ℓ :: δ₂) hδ'
      rwa [show closeC (Val.vcap gid ℓ :: δ₁) M = closeC δ₁ (Comp.subst (Val.vcap gid ℓ) M) from rfl,
           show closeC (Val.vcap gid ℓ :: δ₂) M = closeC δ₂ (Comp.subst (Val.vcap gid ℓ) M) from rfl]
        at this
  | Comp.handle (Handler.transaction ℓ Θ₀) M, HasCTy.handleTransaction (e := e) hnewA hnewR hreadA hreadR hwriteA hwriteR _hrestrict hcells hM _hsub _hBocc =>
      intro n δ₁ δ₂ hδ
      rw [closeC_handleTransaction, closeC_handleTransaction]
      have hrestrict' : ∀ op Θ', Bang.handlesOp (Handler.transaction ℓ Θ') ℓ op = true →
          op = "newTVar" ∨ op = "readTVar" ∨ op = "writeTVar" := fun op Θ' hc => by
        simp only [handlesOp, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc; tauto
      have hheap : HeapRel Eff Mult n Θ₀ Θ₀ := heapRel_self_of_cells_int n Θ₀ hcells
      refine compatK_handleTransaction (e := e) hnewA hnewR hreadA hreadR hwriteA hwriteR hrestrict' hheap
        (fun gid => ?_)
      have hclosed : Val.Closed (Val.vcap gid ℓ) := fun k => rfl
      rw [closeC_subst_comm hδ.closed_left hclosed, closeC_subst_comm hδ.closed_right hclosed]
      have hδ' : EnvRelK n (VTy.cap ℓ :: Γ) (Val.vcap gid ℓ :: δ₁) (Val.vcap gid ℓ :: δ₂) := by
        rw [EnvRelK]
        exact ⟨hclosed, hclosed,
          (show VrelK n (VTy.cap ℓ) (Val.vcap gid ℓ) (Val.vcap gid ℓ) by
            rw [VrelK]; exact ⟨gid, rfl, rfl⟩), hδ⟩
      have := crelK_fund_at M hM n (Val.vcap gid ℓ :: δ₁) (Val.vcap gid ℓ :: δ₂) hδ'
      rwa [show closeC (Val.vcap gid ℓ :: δ₁) M = closeC δ₁ (Comp.subst (Val.vcap gid ℓ) M) from rfl,
           show closeC (Val.vcap gid ℓ :: δ₂) M = closeC δ₂ (Comp.subst (Val.vcap gid ℓ) M) from rfl]
        at this
  | Comp.handle (Handler.custom ℓ p cl) M, HasCTy.handleCustom (e := e) (P := P) hcl hcov hp hM _hle _hBocc =>
      intro n δ₁ δ₂ hδ
      rw [closeC_handleCustom, closeC_handleCustom]
      have hcp : Val.Closed p := fun k => hp.shift_closed k (Nat.zero_le k)
      -- param self-relation (like state's `hsv`) via the in-block `vrelK_fund_at`
      have hpv : ∀ k, VrelK k P p p := fun k => by
        have := vrelK_fund_at p hp k [] [] (EnvRelK_nil_iff k [] [] |>.mpr ⟨rfl, rfl⟩)
        rwa [closeV_closed hcp] at this
      -- coverage restriction (custom analogue of state's get/put)
      have hrestrict : ∀ op p', Bang.handlesOp (Handler.custom ℓ p' cl) ℓ op = true →
          (cl.find? (·.1 == op)).isSome := fun op p' hc => by
        simp only [handlesOp, Bool.and_eq_true] at hc
        exact hc.2
      -- the resume producer, in-block: vf = vrelK_fund_at (v/A explicit → adapt to implicit)
      have hclause : ∀ (k : Nat) (op : OpId) (clause : OpId × Comp) (v₁ v₂ : Val),
          cl.find? (·.1 == op) = some clause → Val.Closed v₁ → Val.Closed v₂ →
          (∀ Aop, EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ op = some Aop → VrelK k Aop v₁ v₂) →
          ∃ (Aᵣ : VTy Eff Mult) (r₁ r₂ : Val),
            EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ op = some Aᵣ ∧
            Comp.subst p (Comp.subst (Val.shift v₁) clause.2) = Comp.ret r₁ ∧
            Comp.subst p (Comp.subst (Val.shift v₂) clause.2) = Comp.ret r₂ ∧
            Val.Closed r₁ ∧ Val.Closed r₂ ∧ VrelK k Aᵣ r₁ r₂ := by
        intro k op clause v₁ v₂ hf hcv₁ hcv₂ hVarg
        obtain ⟨opA, opR, qa, qp, w, hbodyeq, hoa, hor, hw⟩ := hasClauses_find?_typed hcl hf
        -- the clause value VrelK, via the IN-BLOCK recursion on w:
        have hcp : Val.Closed p := fun j => hp.shift_closed j (Nat.zero_le j)
        have hsv₁ : Val.shift v₁ = v₁ := hcv₁.shift
        have hsv₂ : Val.shift v₂ = v₂ := hcv₂.shift
        have hcsv₁ : Val.Closed (Val.shift v₁) := by rw [hsv₁]; exact hcv₁
        have hcsv₂ : Val.Closed (Val.shift v₂) := by rw [hsv₂]; exact hcv₂
        have hop : clause.1 = op := by have := List.find?_some hf; simpa using this
        rw [hop] at hoa hor
        have hpv : VrelK k P p p := by
          have := vrelK_fund_at p hp k [] [] (EnvRelK_nil_iff k [] [] |>.mpr ⟨rfl, rfl⟩)
          rwa [closeV_closed hcp] at this
        have hδcl : EnvRelK k (opA :: P :: []) [Val.shift v₁, p] [Val.shift v₂, p] := by
          rw [EnvRelK]
          refine ⟨hcsv₁, hcsv₂, ?_, hcp, hcp, hpv, EnvRelK_nil_iff k [] [] |>.mpr ⟨rfl, rfl⟩⟩
          rw [hsv₁, hsv₂]; exact hVarg opA hoa
        have hmem : clause ∈ cl := List.mem_of_find?_eq_some hf
        have hszcl : sizeOf clause < sizeOf cl := List.sizeOf_lt_of_mem hmem
        have hszw : sizeOf w < sizeOf clause := by
          calc sizeOf w < sizeOf clause.2 := by rw [hbodyeq]; simp only [Comp.ret.sizeOf_spec]; omega
            _ ≤ sizeOf clause := by
                obtain ⟨c1, c2⟩ := clause; simp only [Prod.mk.sizeOf_spec]; omega
        have hwv : VrelK k opR (Val.subst p (Val.subst (Val.shift v₁) w))
                              (Val.subst p (Val.subst (Val.shift v₂) w)) := by
          have := vrelK_fund_at w hw k [Val.shift v₁, p] [Val.shift v₂, p] hδcl
          simpa only [closeV, closeV_nil] using this
        have hclosed : ∀ v', Val.Closed (Val.shift v') →
            Val.Closed (Val.subst p (Val.subst (Val.shift v') w)) := fun v' hcv' => by
          have := closeV_closed_scoped (δ := [Val.shift v', p]) (v := w)
            (by intro u hu; rcases List.mem_cons.mp hu with rfl | hu; exact hcv'
                rcases List.mem_cons.mp hu with rfl | hu; exact hcp; simp at hu)
            (by simpa using hw.scopedIn)
          simpa only [closeV, closeV_nil] using this
        refine ⟨opR, Val.subst p (Val.subst (Val.shift v₁) w), Val.subst p (Val.subst (Val.shift v₂) w),
          hor, ?_, ?_, hclosed v₁ hcsv₁, hclosed v₂ hcsv₂, hwv⟩
        · rw [hbodyeq]; simp only [Comp.subst, Comp.substFrom]
        · rw [hbodyeq]; simp only [Comp.subst, Comp.substFrom]
      refine compatK_handleCustom (e := e) hcl hrestrict hpv hclause hcp (fun gid => ?_)
      have hclosed : Val.Closed (Val.vcap gid ℓ) := fun k => rfl
      rw [closeC_subst_comm hδ.closed_left hclosed, closeC_subst_comm hδ.closed_right hclosed]
      have hδ' : EnvRelK n (VTy.cap ℓ :: Γ) (Val.vcap gid ℓ :: δ₁) (Val.vcap gid ℓ :: δ₂) := by
        rw [EnvRelK]
        exact ⟨hclosed, hclosed,
          (show VrelK n (VTy.cap ℓ) (Val.vcap gid ℓ) (Val.vcap gid ℓ) by
            rw [VrelK]; exact ⟨gid, rfl, rfl⟩), hδ⟩
      have := crelK_fund_at M hM n (Val.vcap gid ℓ :: δ₁) (Val.vcap gid ℓ :: δ₂) hδ'
      rwa [show closeC (Val.vcap gid ℓ :: δ₁) M = closeC δ₁ (Comp.subst (Val.vcap gid ℓ) M) from rfl,
           show closeC (Val.vcap gid ℓ :: δ₂) M = closeC δ₂ (Comp.subst (Val.vcap gid ℓ) M) from rfl]
        at this
termination_by sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals omega
end

/-- ◊4.5b fundamental theorem (value), frozen-signature wrapper over the term-measured
`vrelK_fund_at`. Byte-identical type to the pre-Fix-2b `vrelK_fund` (implicit `v`), so all
callers + `krelS_refl`/`custom_clause_resume` are untouched. -/
theorem vrelK_fund {γ : GradeVec Mult} {Γ : TyCtx Eff Mult} {v : Val} {A : VTy Eff Mult}
    (h : HasVTy γ Γ v A) :
    ∀ (n : Nat) (δ₁ δ₂ : List Val), EnvRelK n Γ δ₁ δ₂ →
      VrelK n A (closeV δ₁ v) (closeV δ₂ v) :=
  vrelK_fund_at v h

/-- ◊4.5b fundamental theorem (computation), frozen-signature wrapper over `crelK_fund_at`.
Byte-identical type to the pre-Fix-2b `crelK_fund` (implicit `c`), so `Spec.lean` (`lr_fundamental
:= fun h => crelK_fund h`), `krelS_refl`, and `custom_clause_resume` are all untouched. -/
theorem crelK_fund {γ : GradeVec Mult} {Γ : TyCtx Eff Mult} {c : Comp} {e : Eff} {B : CTy Eff Mult}
    (h : HasCTy γ Γ c e B) :
    ∀ (n : Nat) (δ₁ δ₂ : List Val), EnvRelK n Γ δ₁ δ₂ →
      CrelK n B e (closeC δ₁ c) (closeC δ₂ c) :=
  crelK_fund_at c h

/-- #44 STAGE 5 (debt 2, sub-proof W-c) — the RESUME-VALUE PRODUCER for `krelS_custom_reinstall`/
`compatK_handleCustom`. From `HasClauses ℓ P cl` + the param typing `HasVTy [] [] p P`, build the
`hclause` premise: for every matched clause + related closed op-args, the double-`subst` resume focus is a
`ret` of related closed values at the op's result type. Uses `custom_resume_is_ret` (ret-shape),
`closeV_closed_scoped` (closedness), and `vrelK_fund` on the clause value + param (via `EnvRelK k [opA, P]
[shift v₁, p] [shift v₂, p]`) — hence AFTER the mutual block. -/
theorem custom_clause_resume {ℓ : Label} {P : VTy Eff Mult} {cl : List (OpId × Comp)} {p : Val}
    (hcl : HasClauses (Eff := Eff) (Mult := Mult) ℓ P cl)
    (hp : HasVTy (Eff := Eff) (Mult := Mult) [] [] p P) :
    ∀ (k : Nat) (op : OpId) (clause : OpId × Comp) (v₁ v₂ : Val),
      cl.find? (·.1 == op) = some clause → Val.Closed v₁ → Val.Closed v₂ →
      (∀ Aop, EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ op = some Aop → VrelK k Aop v₁ v₂) →
      ∃ (Aᵣ : VTy Eff Mult) (r₁ r₂ : Val),
        EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ op = some Aᵣ ∧
        Comp.subst p (Comp.subst (Val.shift v₁) clause.2) = Comp.ret r₁ ∧
        Comp.subst p (Comp.subst (Val.shift v₂) clause.2) = Comp.ret r₂ ∧
        Val.Closed r₁ ∧ Val.Closed r₂ ∧ VrelK k Aᵣ r₁ r₂ :=
  custom_clause_resume_of (vf := vrelK_fund) hcl hp

/-! ### B.6′ ◊4.5b — `krelS_refl` (the answer-typed `lr_sound` capstone)

A well-typed stack is `KrelS`-self-related at answer type `Co` (the whole-program returner type, the
`D` parameter). Induction over `HasStack`: nil = `krelS_nil_succ`; letF/appF reuse the frame intros +
`crelK_fund`/`vrelK_fund` for the continuation/arg self-relation; the handler arms reuse the closed
`crelK_fund` handler cases (ADR-0053 5→2 — no handler-arm sorry here). -/
theorem krelS_refl {n : Nat} {C : Stack} {e eo : Eff} {B Co : CTy Eff Mult} {qo : Mult}
    {Ao : VTy Eff Mult} {g : Nat} (hCo : Co = CTy.F qo Ao)
    (hC : HasStack C e B eo Co) : KrelS n B Co e g C C := by
  induction hC with
  | @nil e' C' =>
      -- `B = C' = Co = F qo Ao` (`hCo`): the returner empty stack is `krelS_nil_succ`.
      subst hCo; exact krelS_nil_succ n _ _ _ _
  | @letF K N e₁ e₂ eo q qk A B Co hN hK ihK =>
      -- HasStack.letF: tail `K` at the JOINED row `e₁⊔e₂` (ihK), continuation `N` at `e₂`, frame hole
      -- at `e₁`. Build the letF-extended `KrelS` at the joined row `e₁⊔e₂` (continuation row e₂ ≤ e₁⊔e₂),
      -- then WEAKEN the whole frame down to the goal's hole row `e₁` (`e₁ ≤ e₁⊔e₂`, antitone). The frame
      -- body self-relates the continuation `N` via `crelK_fund` (▷-guarded, ∀ m < n).
      have hframe : KrelS n (CTy.F q A) Co (e₁ ⊔ e₂) g (Frame.letF N :: K) (Frame.letF N :: K) := by
        refine krelS_letF_intro (φ := e₂) le_sup_right ?_ (ihK hCo)
        intro m _hm v₁ v₂ hcv₁ hcv₂ hv
        have hδ' : EnvRelK m [A] [v₁] [v₂] := by
          rw [EnvRelK]; exact ⟨hcv₁, hcv₂, hv, EnvRelK_nil_iff m [] [] |>.mpr ⟨rfl, rfl⟩⟩
        have := crelK_fund hN m [v₁] [v₂] hδ'
        rwa [show closeC [v₁] N = Comp.subst v₁ N from rfl,
             show closeC [v₂] N = Comp.subst v₂ N from rfl] at this
      exact KrelS_eff_anti le_sup_left hframe
  | @appF K v e eo q A B Co hv hK ihK =>
      have hcv : Val.Closed v := fun k => hv.shift_closed k (Nat.zero_le k)
      have hvr : VrelK n A v v := by
        have := vrelK_fund hv n [] [] (EnvRelK_nil_iff n [] [] |>.mpr ⟨rfl, rfl⟩)
        rwa [closeV_closed hcv] at this
      exact krelS_appF_intro hcv hcv hvr (ihK hCo)
  | @handleF K nh ℓ e φ eo q A Co hArg hIface hsub _hBocc hK ihK =>
      -- ◊4.5b sub-block f: the handler-frame self-relation = the ROW-DISCHARGE. `krelS_handleF` reduces the
      -- goal `KrelS …e (handleF::K)` to `KrelS …e K`; the IH gives the tail at the DISCHARGED row `φ`
      -- (`HasStack.handleF`: `K` is typed at `φ`, the frame at `e ≤ ℓ⊔φ`). `KrelS_eff_cast` bridges
      -- `φ → e` with no ordering — the SINGLE-ROW `KrelS` expresses the discharge (no two-row needed)
      -- because ε is inert in the answer-typed core (no `Srel` stuck-half gates on it). [decision: single-row]
      -- ◊4.5b sub-block f: the self-relation makes EQUAL handlers (same `h` both sides) ⇒ `h = h` by `rfl`.
      -- THROWS resume supply: dispatch aborts to `(K, ret w)` (ANY op, zero-shot) — `crelK_ret` on the
      -- self-related tail `ihK` closes it (the `hVrel` premise at `C = F q A` gives `VrelK m A w`).
      -- ◊4.5b-append: throws self-relation. HandlerRel n (throws ℓ) (throws ℓ) = (ℓ=ℓ) = rfl. The
      -- Kᵢ-threading resume conjunct: dispatch aborts to (K, ret w) (zero-shot, Kᵢ discarded) — `crelK_ret`
      -- on the self-related tail `ihK` closes it (the hVrel premise at C = F q A gives VrelK m A w).
      rw [krelS_handleF]
      refine ⟨rfl, by simp only [HandlerRel], KrelS_eff_cast (ihK hCo), ?_⟩
      intro m hm op w₁ w₂ Cᵢ εᵢ Kᵢ Kᵢ' cfg₁ cfg₂ hcatch hcw₁ hcw₂ hVrel _hKi _hCᵢ hd₁ hd₂
      have hop : op = "raise" := by
        simp only [Handler.label, handlesOp, Bool.and_eq_true, beq_iff_eq] at hcatch; exact hcatch.2
      subst hop
      have hw : VrelK m A w₁ w₂ := hVrel A (by rw [Handler.label]; exact hArg)
      simp only [dispatchOn] at hd₁ hd₂
      obtain rfl := (Option.some.injEq _ _).mp hd₁.symm
      obtain rfl := (Option.some.injEq _ _).mp hd₂.symm
      -- ◊4.5b-strengthen: SUPPLY the decomposition — throws aborts to `(K, ret w)`, `w₁~w₂` at `A`, the
      -- self-related tail `K~K` at returner hole `F q A` (the discharged-row, downward-closed).
      exact ⟨q, A, w₁, w₂, K, K, φ, rfl, rfl, hcw₁, hcw₂, hw,
        KrelS_mono (le_of_lt hm) (KrelS_eff_cast (ihK hCo))⟩
  | @stateF K nh ℓ s e φ eo q A S Co hg hgr hp hpr hIface hcs hsub _hBocc hK ihK =>
      -- ◊4.5b-append: the state-frame self-relation IS `krelS_state_reinstall` at `s = s` (the same stored
      -- state both sides). The tail self-relates via `ihK` (cast `φ → e`); the interface + state typing come
      -- from the `stateF` binder. `hcs : HasVTy [] [] s S` ⇒ closed + `VrelK k S s s` (`vrelK_fund`).
      have hcss : Val.Closed s := fun k => hcs.shift_closed k (Nat.zero_le k)
      have hsv : ∀ k, VrelK k S s s := fun k => by
        have := vrelK_fund hcs k [] [] (EnvRelK_nil_iff k [] [] |>.mpr ⟨rfl, rfl⟩)
        rwa [closeV_closed hcss] at this
      have hrestrict' : ∀ op s', Bang.handlesOp (Handler.state ℓ s') ℓ op = true → op = "get" ∨ op = "put" :=
        fun op s' hc => by
          simp only [handlesOp, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc
          rcases hc.2 with rfl | rfl <;> simp
      exact krelS_state_reinstall hgr hp hpr hrestrict' nh n s s hcss hcss (hsv n) K K
        (KrelS_eff_cast (ihK hCo))
  | @transactionF K nh ℓ Θ e φ eo q A Co hnewA hnewR hreadA hreadR hwriteA hwriteR _ hcells hsub _hBocc hK ihK =>
      -- ◊4.5b-append: transaction-frame self-relation IS `krelS_transaction_reinstall` at Θ=Θ; tail via
      -- `ihK` (cast φ→e); heap self-relation `HeapRel n Θ Θ` from `hcells` (all cells closed int).
      have hrestrict' : ∀ op Θ', Bang.handlesOp (Handler.transaction ℓ Θ') ℓ op = true →
          op = "newTVar" ∨ op = "readTVar" ∨ op = "writeTVar" := fun op Θ' hc => by
        simp only [handlesOp, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc; tauto
      exact krelS_transaction_reinstall hnewA hnewR hreadA hreadR hwriteA hwriteR hrestrict' nh n Θ Θ
        (heapRel_self_of_cells_int n Θ hcells) K K (KrelS_eff_cast (ihK hCo))
  | @customF K nh ℓ p cl e φ eo q P A Co _hcl _hcov _hp _hle _hBocc hK ihK =>
      -- ◊4.5b-append #44 STAGE 5 (debt 2): the custom-frame self-relation IS `krelS_custom_reinstall` at
      -- `p = p` (the SAME read-only param both sides — strictly simpler than state's `put`). The tail
      -- self-relates via `ihK` (cast `φ → e`); the interface + clause typing come from the `customF` binder;
      -- the resume-value producer `hclause` from `custom_clause_resume` (`vrelK_fund` on each clause value).
      have hcpp : Val.Closed p := fun k => _hp.shift_closed k (Nat.zero_le k)
      have hpv : VrelK n P p p := by
        have := vrelK_fund _hp n [] [] (EnvRelK_nil_iff n [] [] |>.mpr ⟨rfl, rfl⟩)
        rwa [closeV_closed hcpp] at this
      have hrestrict' : ∀ op p', Bang.handlesOp (Handler.custom ℓ p' cl) ℓ op = true →
          (cl.find? (·.1 == op)).isSome := fun op p' hc => by
        simp only [handlesOp, Bool.and_eq_true, beq_iff_eq] at hc; exact hc.2
      exact krelS_custom_reinstall _hcl hrestrict' nh n p p hcpp hcpp hpv
        (custom_clause_resume _hcl _hp) K K (KrelS_eff_cast (ihK hCo))

end -- public section
end Bang
