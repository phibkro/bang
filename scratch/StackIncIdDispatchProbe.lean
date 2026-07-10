import Bang.Meta.BinaryLR
import Bang.Core.Semantics.Invariants
import Bang.Core.Soundness

/-! # StackIncIdDispatchProbe — the idDispatch resume arm preserves StackInc (the machine step's
hard case). Mirrors stackBelow_idDispatch: split, then per-handler reinstall/abort. -/

namespace Bang
open Bang.EffectRow (Label)
variable {Eff  : Type} [Lattice Eff] [OrderBot Eff]
variable {Mult : Type} [CommSemiring Mult] [DecidableEq Mult]
variable [EffSig Eff Mult]

def StackAbove (nid : Nat) : EvalCtx → Prop
  | [] => True
  | .handleF n _ :: K => nid < n ∧ StackAbove nid K
  | .letF _ :: K => StackAbove nid K
  | .appF _ :: K => StackAbove nid K

def StackInc : EvalCtx → Prop
  | [] => True
  | .handleF n _ :: K => StackInc K ∧ Bang.StackBelow n K
  | .letF _ :: K => StackInc K
  | .appF _ :: K => StackInc K

theorem stackBelow_append_local (g : Nat) : ∀ (K1 K2 : EvalCtx),
    Bang.StackBelow g (K1 ++ K2) ↔ (Bang.StackBelow g K1 ∧ Bang.StackBelow g K2) := by
  intro K1 K2; induction K1 with
  | nil => simp only [List.nil_append, StackBelow, true_and]
  | cons fr K1 ih => cases fr with
    | handleF n hd => simp only [List.cons_append, StackBelow, ih]; tauto
    | letF N => simp only [List.cons_append, StackBelow]; exact ih
    | appF w => simp only [List.cons_append, StackBelow]; exact ih

/-- StackInc splits: a split at `n` gives StackInc on both sides (and the reinstall re-composes it). -/
theorem stackInc_split {n : Nat} {K Kᵢ Kₒ : EvalCtx} {h : Handler}
    (hinc : StackInc K) (hsp : splitAtId K n = some (Kᵢ, h, Kₒ)) :
    StackInc Kᵢ ∧ StackInc Kₒ ∧ StackInc (Kᵢ ++ Frame.handleF n h :: Kₒ) := by
  -- K = Kᵢ ++ handleF n h :: Kₒ by splitAtId_decomp, so the third is just `hinc` re-cast.
  have hdec : K = Kᵢ ++ Frame.handleF n h :: Kₒ := splitAtId_decomp K n hsp
  subst hdec
  refine ⟨?_, ?_, hinc⟩
  · -- StackInc Kᵢ from StackInc (Kᵢ ++ handleF n h :: Kₒ)
    clear hsp; induction Kᵢ with
    | nil => trivial
    | cons fr Kᵢ' ih => cases fr with
      | handleF m hd => simp only [List.cons_append, StackInc] at hinc ⊢
                        exact ⟨ih hinc.1, (stackBelow_append_local m Kᵢ' _).mp hinc.2 |>.1⟩
      | letF N => simp only [List.cons_append, StackInc] at hinc ⊢; exact ih hinc
      | appF w => simp only [List.cons_append, StackInc] at hinc ⊢; exact ih hinc
  · -- StackInc Kₒ
    clear hsp; induction Kᵢ with
    | nil => simp only [List.nil_append, StackInc] at hinc; exact hinc.1
    | cons fr Kᵢ' ih => cases fr with
      | handleF m hd => simp only [List.cons_append, StackInc] at hinc; exact ih hinc.1
      | letF N => simp only [List.cons_append, StackInc] at hinc; exact ih hinc
      | appF w => simp only [List.cons_append, StackInc] at hinc; exact ih hinc

/-- reinstall (same id n, payload changed) preserves StackInc. -/
theorem stackInc_reinstall {n : Nat} {Kᵢ Kₒ : EvalCtx} {h reinstall : Handler}
    (h0 : StackInc (Kᵢ ++ Frame.handleF n h :: Kₒ)) :
    StackInc (Kᵢ ++ Frame.handleF n reinstall :: Kₒ) := by
  induction Kᵢ with
  | nil => simp only [List.nil_append, StackInc] at h0 ⊢; exact h0
  | cons fr Kᵢ' ih => cases fr with
    | handleF m hd =>
      simp only [List.cons_append, StackInc] at h0 ⊢
      refine ⟨ih h0.1, ?_⟩
      rw [stackBelow_append_local] at h0 ⊢; simp only [StackBelow] at h0 ⊢; exact h0.2
    | letF N => simp only [List.cons_append, StackInc] at h0 ⊢; exact ih h0
    | appF w => simp only [List.cons_append, StackInc] at h0 ⊢; exact ih h0

/-- THE idDispatch ARM: resume/abort preserves StackInc. -/
theorem stackInc_idDispatch {K K' : EvalCtx} {n : Nat} {ℓ : Label} {op : OpId}
    {v : Val} {c' : Comp} (hinc : StackInc K)
    (hd : idDispatch K n ℓ op v = some (K', c')) : StackInc K' := by
  unfold idDispatch at hd
  obtain ⟨⟨Kᵢ, h, Kₒ⟩, hsplit, hd2⟩ := Option.bind_eq_some_iff.mp hd
  obtain ⟨hinci, hinco, hincfull⟩ := stackInc_split hinc hsplit
  dsimp only at hd2
  by_cases hk : handlesOp h ℓ op = true
  · rw [if_pos hk] at hd2
    cases h with
    | throws ℓ' =>
      simp only [dispatchOn, Option.some.injEq, Prod.mk.injEq] at hd2
      obtain ⟨rfl, _⟩ := hd2; exact hinco
    | state ℓ' s =>
      simp only [dispatchOn] at hd2
      split at hd2 <;>
        · simp only [Option.some.injEq, Prod.mk.injEq] at hd2
          obtain ⟨rfl, _⟩ := hd2; exact stackInc_reinstall hincfull
    | transaction ℓ' Θ =>
      simp only [dispatchOn] at hd2
      (repeat' split at hd2) <;>
        · simp only [Option.some.injEq, Prod.mk.injEq] at hd2
          obtain ⟨rfl, _⟩ := hd2; exact stackInc_reinstall hincfull
    | custom ℓ' p cl =>
      simp only [handlesOp, Bool.and_eq_true, decide_eq_true_eq] at hk
      obtain ⟨_, hsome⟩ := hk
      obtain ⟨clause, hcl⟩ := Option.isSome_iff_exists.mp hsome
      simp only [dispatchOn, hcl, Option.some.injEq, Prod.mk.injEq] at hd2
      obtain ⟨rfl, _⟩ := hd2; exact stackInc_reinstall hincfull
  · rw [if_neg hk] at hd2; exact absurd hd2 (by simp)

end Bang
#print axioms Bang.stackInc_idDispatch

-- === machine step preservation (combined StackInc ∧ WellCounted, since mint needs StackBelow g) ===
namespace Bang
variable {Eff  : Type} [Lattice Eff] [OrderBot Eff]
variable {Mult : Type} [CommSemiring Mult] [DecidableEq Mult]
variable [EffSig Eff Mult]

/-- StackInc ∧ WellCounted co-travel and are jointly preserved by Source.step. -/
theorem stackIncWC_step {cfg cfg' : Config}
    (hinc : StackInc cfg.2.1) (hwc : WellCounted cfg)
    (hstep : Source.step cfg = some cfg') :
    StackInc cfg'.2.1 ∧ WellCounted cfg' := by
  obtain ⟨g, K, c⟩ := cfg
  have hwc' : StackBelow g K := hwc
  have hwcstep : WellCounted cfg' := wellCounted_reachable hwc (StepStar.tail StepStar.refl hstep)
  refine ⟨?_, hwcstep⟩
  cases c with
  | letC M N => simp only [Source.step, Option.some.injEq] at hstep; subst hstep; exact hinc
  | app M v => simp only [Source.step, Option.some.injEq] at hstep; subst hstep; exact hinc
  | handle h M =>
    simp only [Source.step, Option.some.injEq] at hstep; subst hstep
    exact ⟨hinc, hwc'⟩
  | force w =>
    cases w <;>
      first
        | (simp only [Source.step, Option.some.injEq] at hstep; subst hstep; exact hinc)
        | (simp [Source.step] at hstep)
  | ret v =>
    cases K with
    | nil => simp [Source.step] at hstep
    | cons fr K' => cases fr with
      | letF N => simp only [Source.step, Option.some.injEq] at hstep; subst hstep; exact hinc
      | appF w => simp [Source.step] at hstep
      | handleF n h => simp only [Source.step, Option.some.injEq] at hstep; subst hstep
                       exact hinc.1
  | lam M =>
    cases K with
    | nil => simp [Source.step] at hstep
    | cons fr K' => cases fr with
      | appF w => simp only [Source.step, Option.some.injEq] at hstep; subst hstep; exact hinc
      | letF N => simp [Source.step] at hstep
      | handleF n h => simp [Source.step] at hstep
  | perform cap op v =>
    cases cap with
    | vcap n ℓ =>
      simp only [Source.step, Option.map_eq_some_iff] at hstep
      obtain ⟨⟨K', c'⟩, hd, hcfg⟩ := hstep; subst hcfg
      exact stackInc_idDispatch hinc hd
    | _ => simp [Source.step] at hstep
  | case v N₁ N₂ =>
    cases v <;> first
      | (simp only [Source.step, Option.some.injEq] at hstep; subst hstep; exact hinc)
      | (simp [Source.step] at hstep)
  | split v N =>
    cases v <;> first
      | (simp only [Source.step, Option.some.injEq] at hstep; subst hstep; exact hinc)
      | (simp [Source.step] at hstep)
  | unfold v =>
    cases v <;> first
      | (simp only [Source.step, Option.some.injEq] at hstep; subst hstep; exact hinc)
      | (simp [Source.step] at hstep)
  | binop op v₁ v₂ =>
    cases v₁ <;> cases v₂ <;> first
      | (simp only [Source.step, Option.some.injEq] at hstep; subst hstep; exact hinc)
      | (simp [Source.step] at hstep)
  | oom => simp [Source.step] at hstep
  | wrong s => simp [Source.step] at hstep

/-- StackInc propagates along reachability (co-traveling with WellCounted). -/
theorem stackInc_reachable {cfg cfg' : Config}
    (hinc : StackInc cfg.2.1) (hwc : WellCounted cfg) (hreach : StepStar cfg cfg') :
    StackInc cfg'.2.1 := by
  induction hreach with
  | refl => exact hinc
  | tail hpath hstep ih =>
    exact (stackIncWC_step ih (wellCounted_reachable hwc hpath) hstep).1

end Bang
#print axioms Bang.stackInc_reachable
