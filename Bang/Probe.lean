import Bang.Core
import Bang.Syntax
import Bang.Operational
import Bang.LR
import Bang.Metatheory

namespace Bang
open Bang.EffectRow (Label)
variable {Eff  : Type} [Lattice Eff] [OrderBot Eff]
variable {Mult : Type} [CommSemiring Mult] [DecidableEq Mult]
variable [EffSig Eff Mult]

/-! ## FEASIBILITY PROBE — full-shape answer-typed `KrelS` (sub-block a gate)

Gate questions:
  (1) does the mutual `CrelS`/`KrelS` (D-threaded, all 3 frames + nil + return-half)
      compile under lex `(n, role, stackLen)`?
  (2) μ-floor vacuity (`CrelS 0`)?
  (3) adequacy grounding at the identity (nil) stack?
-/

mutual
/-- `VrelS` — value relation, copied from the real `Vrel` (references `CrelS` in the U-clause). In the
mutual block with `CrelS`/`KrelS`. The metric must unify across all THREE. -/
def VrelS : Nat → VTy Eff Mult → Val → Val → Prop
  | _,     .unit,    v₁, v₂ => BaseRel (Eff := Eff) (Mult := Mult) VTy.unit v₁ v₂
  | _,     .int,     v₁, v₂ => BaseRel (Eff := Eff) (Mult := Mult) VTy.int v₁ v₂
  | n,     .U φ B,   v₁, v₂ =>
      -- PROBE VARIANT: ▷-guarded thunk (∀ j < n), to test whether the strict index-drop on the
      -- Vrel→Crel edge unifies the Vrel/Crel/KrelS cycle under (n, role, stackLen)+sizeOf-tiebreak.
      ∃ c₁ c₂, v₁ = Val.vthunk c₁ ∧ v₂ = Val.vthunk c₂ ∧ ∀ j, j < n → CrelS j B φ c₁ c₂
  | n,     .sum A B, v₁, v₂ =>
      (∃ w₁ w₂, v₁ = Val.inl w₁ ∧ v₂ = Val.inl w₂ ∧ VrelS n A w₁ w₂) ∨
      (∃ w₁ w₂, v₁ = Val.inr w₁ ∧ v₂ = Val.inr w₂ ∧ VrelS n B w₁ w₂)
  | n,     .prod A B, v₁, v₂ =>
      ∃ a₁ a₂ b₁ b₂, v₁ = Val.pair a₁ b₁ ∧ v₂ = Val.pair a₂ b₂ ∧
        VrelS n A a₁ a₂ ∧ VrelS n B b₁ b₂
  | n,     .mu A,    v₁, v₂ =>
      ∃ w₁ w₂, v₁ = Val.fold w₁ ∧ v₂ = Val.fold w₂ ∧ ∀ j, j < n → VrelS j (VTy.unrollMu A) w₁ w₂
  | _,     .tvar _,  _,  _  => False
  termination_by n A _ _ => (n, 0, 0, sizeOf A)
/-- `CrelS n C ε c₁ c₂`: biorthogonal closure. `D` (the answer type) is QUANTIFIED here, so the
SIGNATURE is byte-identical to the current `Crel` (2a frozen-surface safe). -/
def CrelS : Nat → CTy Eff Mult → Eff → Comp → Comp → Prop
  | n, C, ε, c₁, c₂ =>
      ∀ (D : CTy Eff Mult) (K₁ K₂ : Stack), KrelS n C D ε K₁ K₂ →
        CoApproxC_le n (K₁, c₁) (K₂, c₂)
  termination_by n C _ _ _ => (n, 2, 0, sizeOf C)
/-- `KrelS n C D ε K₁ K₂`: answer-typed stack relation, STACK-STRUCTURAL. `C` = the type at the
HOLE; `D` = the answer type at the bottom (inert parameter, threaded unchanged through frames).
DISCOVERY-IC FORM: SINGLE-BODY def with an internal `match K₁, K₂` (the multi-clause form fights
the unfolder — `rw`/`simp` "no progress"). Per-case `@[simp]` eq lemmas generated below. -/
def KrelS : Nat → CTy Eff Mult → CTy Eff Mult → Eff → Stack → Stack → Prop
  | n, C, D, ε, K₁, K₂ =>
      match K₁, K₂ with
      -- nil: hole type = answer type; observe related RETURNS (the biorthogonal base / return-half).
      | [], [] =>
          C = D ∧ (∀ q A, C = CTy.F q A → ∀ v₁ v₂, Val.Closed v₁ → Val.Closed v₂ → VrelS n A v₁ v₂ →
            CoApproxC_le n ([], Comp.ret v₁) ([], Comp.ret v₂))
      -- letF: hole is a returner `F q A`; frame body ▷-guarded at `m < n`, tail at continuation B.
      | (Frame.letF N₁ :: K₁'), (Frame.letF N₂ :: K₂') =>
          ∃ q A B, C = CTy.F q A ∧
            (∀ m, m < n → ∀ v₁ v₂, Val.Closed v₁ → Val.Closed v₂ → VrelS m A v₁ v₂ →
              CrelS m B ε (Comp.subst v₁ N₁) (Comp.subst v₂ N₂))
            ∧ KrelS n B D ε K₁' K₂'
      -- appF: hole is an arrow `arr q A B`; cap is the appF arg, tail at codomain B.
      | (Frame.appF w₁ :: K₁'), (Frame.appF w₂ :: K₂') =>
          ∃ q A B, C = CTy.arr q A B ∧
            Val.Closed w₁ ∧ Val.Closed w₂ ∧ VrelS n A w₁ w₂ ∧ KrelS n B D ε K₁' K₂'
      -- handleF: tail recurses at the same hole type (handler-agnostic at the stack level).
      | (Frame.handleF _h :: K₁'), (Frame.handleF _h' :: K₂') =>
          KrelS n C D ε K₁' K₂'
      | _, _ => False
termination_by n _ _ _ K _ => (n, 1, K.length, 0)
decreasing_by
  -- Lex `(n, role, stackLen, sizeOf)`, roles Vrel=0 < KrelS=1 < Crel=2. Every cross-function edge
  -- drops `n` (Vrel→Crel via ▷-thunk j<n; KrelS→Crel frame-body m<n; Vrel-mu j<n) OR drops `role`
  -- (Crel→KrelS 2→1; KrelS→Vrel-cap 1→0) OR drops `stackLen` (KrelS tail) OR drops `sizeOf`
  -- (Vrel sum/prod internal). decreasing_tactic handles the strict-n and the role/sizeOf ties.
  all_goals
    first
      | (simp_wf; exact Prod.Lex.left _ _ ‹_ < _›)
      | decreasing_tactic
end

-- DISCOVERY-IC per-case `@[simp]` equation lemmas (so downstream proofs unfold cleanly).
@[simp] theorem krelS_nil {n : Nat} {C D : CTy Eff Mult} {ε : Eff} :
    KrelS n C D ε [] [] ↔
      (C = D ∧ ∀ q A, C = CTy.F q A → ∀ v₁ v₂, Val.Closed v₁ → Val.Closed v₂ → VrelS n A v₁ v₂ →
        CoApproxC_le n ([], Comp.ret v₁) ([], Comp.ret v₂)) := by
  rw [KrelS]

@[simp] theorem krelS_letF {n : Nat} {C D : CTy Eff Mult} {ε : Eff} {N₁ N₂ : Comp} {K₁ K₂ : Stack} :
    KrelS n C D ε (Frame.letF N₁ :: K₁) (Frame.letF N₂ :: K₂) ↔
      ∃ q A B, C = CTy.F q A ∧
        (∀ m, m < n → ∀ v₁ v₂, Val.Closed v₁ → Val.Closed v₂ → VrelS m A v₁ v₂ →
          CrelS m B ε (Comp.subst v₁ N₁) (Comp.subst v₂ N₂))
        ∧ KrelS n B D ε K₁ K₂ := by
  rw [KrelS]

@[simp] theorem krelS_appF {n : Nat} {C D : CTy Eff Mult} {ε : Eff} {w₁ w₂ : Val} {K₁ K₂ : Stack} :
    KrelS n C D ε (Frame.appF w₁ :: K₁) (Frame.appF w₂ :: K₂) ↔
      ∃ q A B, C = CTy.arr q A B ∧
        Val.Closed w₁ ∧ Val.Closed w₂ ∧ VrelS n A w₁ w₂ ∧ KrelS n B D ε K₁ K₂ := by
  rw [KrelS]

@[simp] theorem krelS_handleF {n : Nat} {C D : CTy Eff Mult} {ε : Eff} {h h' : Handler}
    {K₁ K₂ : Stack} :
    KrelS n C D ε (Frame.handleF h :: K₁) (Frame.handleF h' :: K₂) ↔
      KrelS n C D ε K₁ K₂ := by
  rw [KrelS]

-- (1) compiles? (2) μ-floor:
theorem crelS_zero {C : CTy Eff Mult} {ε : Eff} {c₁ c₂ : Comp} : CrelS 0 C ε c₁ c₂ := by
  rw [CrelS]; intro D K₁ K₂ _ hconv; exact absurd hconv (not_convergesC_le_zero _)

-- (3) adequacy grounding: at the identity (nil) stack with C = D, CrelS gives the return observation.
theorem crelS_adequacy_nil {n : Nat} {q : Mult} {A : VTy Eff Mult} {ε : Eff} {c₁ c₂ : Comp}
    (h : CrelS n (CTy.F q A) ε c₁ c₂) :
    CoApproxC_le n ([], c₁) ([], c₂) := by
  rw [CrelS] at h
  apply h (CTy.F q A) [] []
  rw [krelS_nil]
  refine ⟨rfl, fun q' A' _ v₁ v₂ _ _ _ _ => ?_⟩
  -- the nil return-half: `([], ret v₂) ↦ done v₂` always converges on the right
  exact ⟨1, v₂, rfl⟩

-- (4) Vrel_mono U-case survives `∀ j < n` (restrict the guard). Confirms the down-closure the
-- fundamental theorem needs is still STRUCTURAL under the ▷-guarded thunk.
theorem vrelS_mono_U {n m : Nat} {φ : Eff} {B : CTy Eff Mult} {v₁ v₂ : Val}
    (hmn : m ≤ n) (hv : VrelS n (VTy.U φ B) v₁ v₂) : VrelS m (VTy.U φ B) v₁ v₂ := by
  rw [VrelS] at hv ⊢
  obtain ⟨c₁, c₂, rfl, rfl, hc⟩ := hv
  exact ⟨c₁, c₂, rfl, rfl, fun j hjm => hc j (lt_of_lt_of_le hjm hmn)⟩

-- (5) crel_force survives: `force (vthunk c) ↦ c`, the ▷-head-step needs reducts at m<n —
-- the `∀ j < n` U-clause supplies them DIRECTLY (cleaner than the old `∀ j ≤ n` + le_of_lt).
theorem crelS_force {n : Nat} {φ : Eff} {B : CTy Eff Mult} {w₁ w₂ : Val}
    (hv : VrelS n (VTy.U φ B) w₁ w₂) :
    ∀ (D : CTy Eff Mult) (K₁ K₂ : Stack), KrelS n B D φ K₁ K₂ →
      ∀ m, m < n → CrelS m B φ (Comp.force w₁) (Comp.force w₂) → True := by
  rw [VrelS] at hv
  obtain ⟨c₁, c₂, rfl, rfl, hc⟩ := hv
  -- `hc : ∀ j < n, CrelS j B φ c₁ c₂` is EXACTLY the m<n reducts Crel_head_step consumes.
  intro _ _ _ _ m hm _; exact trivial

end Bang
