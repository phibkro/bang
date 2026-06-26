/-
  scratch/RunRenameProbe.lean — inc-5 Phase-1, the DYNAMIC renaming keystone.
  ─────────────────────────────────────────────────────────────────────────────
  Mirror of `runplug`'s STATIC work (`plug`/`splitAtId` ignore frame ids). This file
  proves the DYNAMIC half: **`Source.step` / `Config.run` commute with an injective
  renaming of handler ids** (the frame ids AND the `vcap`s referencing them), provided
  the renaming acts as a *shift* on the fresh-id region `[g, ∞)` (the gensym source).

  WHY the shift condition. `Source.step`'s ONLY id-minting arm is `handle`: it mints the
  counter `g`, pushes `handleF g h`, and advances `g ↦ g+1`. For a renaming to commute,
  the renamed counter `σ g` must mint `σ g` and advance to `σ g + 1`, i.e. `σ (g+1) = σ g + 1`.
  Every other arm threads `g` unchanged (dispatch reuses an EXISTING id), so it needs only
  that `σ` is INJECTIVE (`splitAtId` finds the same frame under `σ`). The counter is monotone,
  so the per-step `σ(g+1)=σg+1` is supplied by a single `∀ k ≥ g, σ(k+1)=σ k+1` invariant.

  This is the general `Config.run`-renaming-invariance the inc-5 LR consumes at THREE sites
  (`crelK_ret` handleF arm, `crelK_fund` up/perform arm, the `converges_plug_iff → krelS_refl`
  bridge in `lr_sound`): a permutation of the canonical ids `0,1,2,…` onto the LR's original
  ids, extended by the shift on the tail, is exactly such a `σ` — so the machine image of the
  canonical config and of the original-id config run to renamed-equal results.

  HARD boundary: writes ONLY this scratch file. READS Bang.Operational + (for context) the
  §2/§3 renaming primitives of `RenameInvarianceProbe`, re-derived here (a scratch file cannot
  import another across the build graph). NO frozen-def edits.

  Run: `nix develop -c lake env lean scratch/RunRenameProbe.lean`.
-/
import Bang.Operational
namespace Bang.RunRename
open Bang
open Bang.EffectRow (Label)

/-! ## 1. Renaming `σ : Nat → Nat` over values / comps / handlers / frames / stacks.
(`RenameInvarianceProbe §1`, re-derived on this base.) -/

mutual
def renameV (σ : Nat → Nat) : Val → Val
  | .vcap n ℓ   => .vcap (σ n) ℓ
  | .vthunk c   => .vthunk (renameC σ c)
  | .inl v      => .inl (renameV σ v)
  | .inr v      => .inr (renameV σ v)
  | .pair a b   => .pair (renameV σ a) (renameV σ b)
  | .fold v     => .fold (renameV σ v)
  | v           => v
def renameC (σ : Nat → Nat) : Comp → Comp
  | .ret v        => .ret (renameV σ v)
  | .letC M N     => .letC (renameC σ M) (renameC σ N)
  | .force v      => .force (renameV σ v)
  | .lam M        => .lam (renameC σ M)
  | .app M v      => .app (renameC σ M) (renameV σ v)
  | .perform c op v => .perform (renameV σ c) op (renameV σ v)
  | .handle h M   => .handle (renameH σ h) (renameC σ M)
  | .case v N₁ N₂ => .case (renameV σ v) (renameC σ N₁) (renameC σ N₂)
  | .split v N    => .split (renameV σ v) (renameC σ N)
  | .unfold v     => .unfold (renameV σ v)
  | c             => c
def renameH (σ : Nat → Nat) : Handler → Handler
  | .state ℓ s  => .state ℓ (renameV σ s)
  | .throws ℓ   => .throws ℓ
  | .transaction ℓ Θ => .transaction ℓ (Θ.map (renameV σ))
end

/-- rename a frame: `handleF` carries the id; `letF`/`appF` only carry sub-terms. -/
def renameF (σ : Nat → Nat) : Frame → Frame
  | .letF N      => .letF (renameC σ N)
  | .appF v      => .appF (renameV σ v)
  | .handleF n h => .handleF (σ n) (renameH σ h)

def renameK (σ : Nat → Nat) : EvalCtx → EvalCtx := List.map (renameF σ)

@[simp] theorem renameK_nil (σ : Nat → Nat) : renameK σ [] = [] := rfl
@[simp] theorem renameK_cons (σ : Nat → Nat) (fr : Frame) (K : EvalCtx) :
    renameK σ (fr :: K) = renameF σ fr :: renameK σ K := rfl
theorem renameK_append (σ : Nat → Nat) (K K' : EvalCtx) :
    renameK σ (K ++ K') = renameK σ K ++ renameK σ K' := by
  simp only [renameK, List.map_append]

/-! ### Per-constructor reduction lemmas (the catch-all patterns make `renameV`/`renameC`/`renameH`
themselves poor `simp` lemmas; these `rfl`-equations let `simp only` reduce cleanly). -/

@[simp] theorem renameV_vunit (σ : Nat → Nat) : renameV σ .vunit = .vunit := by simp only [renameV]
@[simp] theorem renameV_vint (σ : Nat → Nat) (n : Int) : renameV σ (.vint n) = .vint n := by
  simp only [renameV]
@[simp] theorem renameV_vvar (σ : Nat → Nat) (i : Nat) : renameV σ (.vvar i) = .vvar i := by
  simp only [renameV]
@[simp] theorem renameV_vcap (σ : Nat → Nat) (n : Nat) (ℓ : Label) :
    renameV σ (.vcap n ℓ) = .vcap (σ n) ℓ := by simp only [renameV]
@[simp] theorem renameV_vthunk (σ : Nat → Nat) (c : Comp) :
    renameV σ (.vthunk c) = .vthunk (renameC σ c) := by simp only [renameV]
@[simp] theorem renameV_inl (σ : Nat → Nat) (v : Val) : renameV σ (.inl v) = .inl (renameV σ v) := by
  simp only [renameV]
@[simp] theorem renameV_inr (σ : Nat → Nat) (v : Val) : renameV σ (.inr v) = .inr (renameV σ v) := by
  simp only [renameV]
@[simp] theorem renameV_pair (σ : Nat → Nat) (a b : Val) :
    renameV σ (.pair a b) = .pair (renameV σ a) (renameV σ b) := by simp only [renameV]
@[simp] theorem renameV_fold (σ : Nat → Nat) (v : Val) : renameV σ (.fold v) = .fold (renameV σ v) := by
  simp only [renameV]

@[simp] theorem renameC_ret (σ : Nat → Nat) (v : Val) : renameC σ (.ret v) = .ret (renameV σ v) := by
  simp only [renameC]
@[simp] theorem renameC_letC (σ : Nat → Nat) (M N : Comp) :
    renameC σ (.letC M N) = .letC (renameC σ M) (renameC σ N) := by simp only [renameC]
@[simp] theorem renameC_force (σ : Nat → Nat) (v : Val) : renameC σ (.force v) = .force (renameV σ v) := by
  simp only [renameC]
@[simp] theorem renameC_lam (σ : Nat → Nat) (M : Comp) : renameC σ (.lam M) = .lam (renameC σ M) := by
  simp only [renameC]
@[simp] theorem renameC_app (σ : Nat → Nat) (M : Comp) (v : Val) :
    renameC σ (.app M v) = .app (renameC σ M) (renameV σ v) := by simp only [renameC]
@[simp] theorem renameC_perform (σ : Nat → Nat) (c : Val) (op : OpId) (v : Val) :
    renameC σ (.perform c op v) = .perform (renameV σ c) op (renameV σ v) := by simp only [renameC]
@[simp] theorem renameC_handle (σ : Nat → Nat) (h : Handler) (M : Comp) :
    renameC σ (.handle h M) = .handle (renameH σ h) (renameC σ M) := by simp only [renameC]
@[simp] theorem renameC_case (σ : Nat → Nat) (v : Val) (N₁ N₂ : Comp) :
    renameC σ (.case v N₁ N₂) = .case (renameV σ v) (renameC σ N₁) (renameC σ N₂) := by simp only [renameC]
@[simp] theorem renameC_split (σ : Nat → Nat) (v : Val) (N : Comp) :
    renameC σ (.split v N) = .split (renameV σ v) (renameC σ N) := by simp only [renameC]
@[simp] theorem renameC_unfold (σ : Nat → Nat) (v : Val) :
    renameC σ (.unfold v) = .unfold (renameV σ v) := by simp only [renameC]
@[simp] theorem renameC_oom (σ : Nat → Nat) : renameC σ .oom = .oom := by simp only [renameC]
@[simp] theorem renameC_wrong (σ : Nat → Nat) (s : String) : renameC σ (.wrong s) = .wrong s := by
  simp only [renameC]

@[simp] theorem renameH_state (σ : Nat → Nat) (ℓ : Label) (s : Val) :
    renameH σ (.state ℓ s) = .state ℓ (renameV σ s) := by simp only [renameH]
@[simp] theorem renameH_throws (σ : Nat → Nat) (ℓ : Label) : renameH σ (.throws ℓ) = .throws ℓ := by
  simp only [renameH]
@[simp] theorem renameH_transaction (σ : Nat → Nat) (ℓ : Label) (Θ : List Val) :
    renameH σ (.transaction ℓ Θ) = .transaction ℓ (Θ.map (renameV σ)) := by simp only [renameH]

@[simp] theorem renameF_letF (σ : Nat → Nat) (N : Comp) : renameF σ (.letF N) = .letF (renameC σ N) := rfl
@[simp] theorem renameF_appF (σ : Nat → Nat) (v : Val) : renameF σ (.appF v) = .appF (renameV σ v) := rfl
@[simp] theorem renameF_handleF (σ : Nat → Nat) (n : Nat) (h : Handler) :
    renameF σ (.handleF n h) = .handleF (σ n) (renameH σ h) := rfl

/-- renaming preserves a handler's label (touches only stored values + ids). -/
@[simp] theorem renameH_label (σ : Nat → Nat) (h : Handler) : (renameH σ h).label = h.label := by
  cases h <;> simp only [renameH, Handler.label]

/-- `handlesOp` is invariant under `renameH` (it reads only the label + op-kind, not payloads/ids). -/
@[simp] theorem handlesOp_renameH (σ : Nat → Nat) (h : Handler) (ℓ : Label) (op : OpId) :
    handlesOp (renameH σ h) ℓ op = handlesOp h ℓ op := by
  cases h <;> simp only [renameH_state, renameH_throws, renameH_transaction, handlesOp]

/-! ## 2. Renaming COMMUTES with `shiftFrom` and `substFrom`.

Renaming relabels only `vcap` ids; shift/subst touch only de Bruijn indices (and leave `vcap`
closed). They never overlap, so they commute — proved by the standard mutual structural
induction (mirrors `Comp.substFrom_shiftFrom`'s shape). -/

mutual
theorem renameV_shiftFrom (σ : Nat → Nat) (c : Nat) :
    ∀ t : Val, renameV σ (Val.shiftFrom c t) = Val.shiftFrom c (renameV σ t)
  | .vunit       => by simp only [Val.shiftFrom, renameV_vunit]
  | .vint _      => by simp only [Val.shiftFrom, renameV_vint]
  | .vcap _ _    => by simp only [Val.shiftFrom, renameV_vcap]
  | .vvar i      => by
      rw [renameV_vvar]
      by_cases h : i < c
      · rw [show Val.shiftFrom c (Val.vvar i) = Val.vvar i from by simp only [Val.shiftFrom, if_pos h],
            renameV_vvar]
      · rw [show Val.shiftFrom c (Val.vvar i) = Val.vvar (i + 1) from by
              simp only [Val.shiftFrom, if_neg h], renameV_vvar]
  | .vthunk M    => by simp only [Val.shiftFrom, renameV_vthunk, renameC_shiftFrom σ c M]
  | .inl w       => by simp only [Val.shiftFrom, renameV_inl, renameV_shiftFrom σ c w]
  | .inr w       => by simp only [Val.shiftFrom, renameV_inr, renameV_shiftFrom σ c w]
  | .pair w₁ w₂  => by
      simp only [Val.shiftFrom, renameV_pair, renameV_shiftFrom σ c w₁, renameV_shiftFrom σ c w₂]
  | .fold w      => by simp only [Val.shiftFrom, renameV_fold, renameV_shiftFrom σ c w]
theorem renameC_shiftFrom (σ : Nat → Nat) (c : Nat) :
    ∀ t : Comp, renameC σ (Comp.shiftFrom c t) = Comp.shiftFrom c (renameC σ t)
  | .ret w       => by simp only [Comp.shiftFrom, renameC_ret, renameV_shiftFrom σ c w]
  | .letC M N    => by
      simp only [Comp.shiftFrom, renameC_letC, renameC_shiftFrom σ c M, renameC_shiftFrom σ (c + 1) N]
  | .force w     => by simp only [Comp.shiftFrom, renameC_force, renameV_shiftFrom σ c w]
  | .lam M       => by simp only [Comp.shiftFrom, renameC_lam, renameC_shiftFrom σ (c + 1) M]
  | .app M w     => by
      simp only [Comp.shiftFrom, renameC_app, renameC_shiftFrom σ c M, renameV_shiftFrom σ c w]
  | .perform cp op w => by
      simp only [Comp.shiftFrom, renameC_perform, renameV_shiftFrom σ c cp, renameV_shiftFrom σ c w]
  | .handle h M  => by
      simp only [Comp.shiftFrom, renameC_handle, renameH_shiftFrom σ c h, renameC_shiftFrom σ (c + 1) M]
  | .case w N₁ N₂ => by
      simp only [Comp.shiftFrom, renameC_case, renameV_shiftFrom σ c w,
        renameC_shiftFrom σ (c + 1) N₁, renameC_shiftFrom σ (c + 1) N₂]
  | .split w N   => by
      simp only [Comp.shiftFrom, renameC_split, renameV_shiftFrom σ c w, renameC_shiftFrom σ (c + 2) N]
  | .unfold w    => by simp only [Comp.shiftFrom, renameC_unfold, renameV_shiftFrom σ c w]
  | .oom         => by simp only [Comp.shiftFrom, renameC_oom]
  | .wrong _     => by simp only [Comp.shiftFrom, renameC_wrong]
theorem renameH_shiftFrom (σ : Nat → Nat) (c : Nat) :
    ∀ h : Handler, renameH σ (Handler.shiftFrom c h) = Handler.shiftFrom c (renameH σ h)
  | .state ℓ s       => by simp only [Handler.shiftFrom, renameH_state, renameV_shiftFrom σ c s]
  | .throws _        => by simp only [Handler.shiftFrom, renameH_throws]
  | .transaction _ _ => by simp only [Handler.shiftFrom, renameH_transaction]
end

/-- renaming commutes with the cutoff-0 `shift`. -/
theorem renameV_shift (σ : Nat → Nat) (v : Val) : renameV σ (Val.shift v) = Val.shift (renameV σ v) :=
  renameV_shiftFrom σ 0 v

mutual
theorem renameV_substFrom (σ : Nat → Nat) (k : Nat) (v : Val) :
    ∀ t : Val, renameV σ (Val.substFrom k v t) = Val.substFrom k (renameV σ v) (renameV σ t)
  | .vunit       => by simp only [Val.substFrom, renameV_vunit]
  | .vint _      => by simp only [Val.substFrom, renameV_vint]
  | .vcap _ _    => by simp only [Val.substFrom, renameV_vcap]
  | .vvar i      => by
      rw [renameV_vvar]
      by_cases h1 : i = k
      · rw [show Val.substFrom k v (Val.vvar i) = v from by simp only [Val.substFrom, if_pos h1],
            show Val.substFrom k (renameV σ v) (Val.vvar i) = renameV σ v from by
              simp only [Val.substFrom, if_pos h1]]
      · by_cases h2 : i > k
        · rw [show Val.substFrom k v (Val.vvar i) = Val.vvar (i - 1) from by
                simp only [Val.substFrom, if_neg h1, if_pos h2],
              show Val.substFrom k (renameV σ v) (Val.vvar i) = Val.vvar (i - 1) from by
                simp only [Val.substFrom, if_neg h1, if_pos h2], renameV_vvar]
        · rw [show Val.substFrom k v (Val.vvar i) = Val.vvar i from by
                simp only [Val.substFrom, if_neg h1, if_neg h2],
              show Val.substFrom k (renameV σ v) (Val.vvar i) = Val.vvar i from by
                simp only [Val.substFrom, if_neg h1, if_neg h2], renameV_vvar]
  | .vthunk M    => by simp only [Val.substFrom, renameV_vthunk, renameC_substFrom σ k v M]
  | .inl w       => by simp only [Val.substFrom, renameV_inl, renameV_substFrom σ k v w]
  | .inr w       => by simp only [Val.substFrom, renameV_inr, renameV_substFrom σ k v w]
  | .pair w₁ w₂  => by
      simp only [Val.substFrom, renameV_pair, renameV_substFrom σ k v w₁, renameV_substFrom σ k v w₂]
  | .fold w      => by simp only [Val.substFrom, renameV_fold, renameV_substFrom σ k v w]
theorem renameC_substFrom (σ : Nat → Nat) (k : Nat) (v : Val) :
    ∀ t : Comp, renameC σ (Comp.substFrom k v t) = Comp.substFrom k (renameV σ v) (renameC σ t)
  | .ret w       => by simp only [Comp.substFrom, renameC_ret, renameV_substFrom σ k v w]
  | .letC M N    => by
      simp only [Comp.substFrom, renameC_letC, renameC_substFrom σ k v M,
        renameC_substFrom σ (k + 1) (Val.shift v) N, renameV_shift]
  | .force w     => by simp only [Comp.substFrom, renameC_force, renameV_substFrom σ k v w]
  | .lam M       => by
      simp only [Comp.substFrom, renameC_lam, renameC_substFrom σ (k + 1) (Val.shift v) M, renameV_shift]
  | .app M w     => by
      simp only [Comp.substFrom, renameC_app, renameC_substFrom σ k v M, renameV_substFrom σ k v w]
  | .perform cp op w => by
      simp only [Comp.substFrom, renameC_perform, renameV_substFrom σ k v cp, renameV_substFrom σ k v w]
  | .handle h M  => by
      simp only [Comp.substFrom, renameC_handle, renameH_substFrom σ k v h,
        renameC_substFrom σ (k + 1) (Val.shift v) M, renameV_shift]
  | .case w N₁ N₂ => by
      simp only [Comp.substFrom, renameC_case, renameV_substFrom σ k v w,
        renameC_substFrom σ (k + 1) (Val.shift v) N₁,
        renameC_substFrom σ (k + 1) (Val.shift v) N₂, renameV_shift]
  | .split w N   => by
      simp only [Comp.substFrom, renameC_split, renameV_substFrom σ k v w,
        renameC_substFrom σ (k + 2) (Val.shift (Val.shift v)) N, renameV_shift]
  | .unfold w    => by simp only [Comp.substFrom, renameC_unfold, renameV_substFrom σ k v w]
  | .oom         => by simp only [Comp.substFrom, renameC_oom]
  | .wrong _     => by simp only [Comp.substFrom, renameC_wrong]
theorem renameH_substFrom (σ : Nat → Nat) (k : Nat) (v : Val) :
    ∀ h : Handler, renameH σ (Handler.substFrom k v h) = Handler.substFrom k (renameV σ v) (renameH σ h)
  | .state ℓ s       => by simp only [Handler.substFrom, renameH_state, renameV_substFrom σ k v s]
  | .throws _        => by simp only [Handler.substFrom, renameH_throws]
  | .transaction _ _ => by simp only [Handler.substFrom, renameH_transaction]
end

/-- renaming commutes with the head-redex `subst`. -/
theorem renameC_subst (σ : Nat → Nat) (v : Val) (t : Comp) :
    renameC σ (Comp.subst v t) = Comp.subst (renameV σ v) (renameC σ t) :=
  renameC_substFrom σ 0 v t

/-! ## 3. DISPATCH commutes with an injective renaming.

`splitAtId_rename` (`RenameInvarianceProbe §3`, re-derived) → `dispatchOn`/`idDispatch` commute. -/

theorem splitAtId_rename (σ : Nat → Nat) (hσ : Function.Injective σ) (n : Nat) :
    ∀ K : EvalCtx,
      splitAtId (renameK σ K) (σ n)
        = (splitAtId K n).map (fun x => (renameK σ x.1, renameH σ x.2.1, renameK σ x.2.2)) := by
  intro K
  induction K with
  | nil => rfl
  | cons fr K ih =>
    cases fr with
    | handleF m h =>
      simp only [renameK_cons, renameF, splitAtId]
      by_cases hmn : m = n
      · subst hmn; rw [if_pos rfl, if_pos rfl]; rfl
      · rw [if_neg hmn, if_neg (fun h => hmn (hσ h)), ih]
        cases splitAtId K n <;> rfl
    | letF N =>
      simp only [renameK_cons, renameF, splitAtId, ih]
      cases splitAtId K n <;> rfl
    | appF v =>
      simp only [renameK_cons, renameF, splitAtId, ih]
      cases splitAtId K n <;> rfl

/-- `List.getD` of a `map` with a FIXED-POINT default: `(Θ.map f).getD i d = f (Θ.getD i d)` when
`f d = d`. (Used for `readTVar`, where `f = renameV σ` and `d = vint 0` is a fixed point.) -/
theorem getD_map_fixed {α : Type} (f : α → α) (Θ : List α) (i : Nat) (d : α) (hd : f d = d) :
    (Θ.map f).getD i d = f (Θ.getD i d) := by
  simp only [List.getD, List.getElem?_map]
  cases Θ[i]? with
  | none => simpa using hd.symm
  | some x => rfl

/-- `List.set` of a `map` = `map` of the `set`. (Used for `writeTVar`/`storeSet`.) -/
theorem storeSet_map (f : Val → Val) (Θ : List Val) (i : Nat) (w : Val) :
    (storeSet Θ i w).map f = storeSet (Θ.map f) i (f w) := by
  unfold storeSet
  induction Θ generalizing i with
  | nil => cases i <;> rfl
  | cons x Θ ih => cases i with
    | zero => rfl
    | succ j => simp only [List.set_cons_succ, List.map_cons, ih]

/-- `tvarIdx` is invariant under renaming (it reads only a `vint` payload, untouched by `renameV`). -/
@[simp] theorem tvarIdx_renameV (σ : Nat → Nat) (v : Val) : tvarIdx (renameV σ v) = tvarIdx v := by
  cases v <;> simp only [renameV_vunit, renameV_vint, renameV_vvar, renameV_vcap, renameV_vthunk,
    renameV_inl, renameV_inr, renameV_pair, renameV_fold, tvarIdx]

/-- **`dispatchOn` commutes with renaming.** The reinstalled `handleF n` becomes `handleF (σ n)`, the
stored payloads/heap are renamed, and the returned focus is renamed — all consistently. -/
theorem dispatchOn_rename (σ : Nat → Nat) (n : Nat) (op : OpId) (v : Val)
    (Kᵢ : EvalCtx) (h : Handler) (Kₒ : EvalCtx) :
    dispatchOn (σ n) op (renameV σ v) (renameK σ Kᵢ, renameH σ h, renameK σ Kₒ)
      = (dispatchOn n op v (Kᵢ, h, Kₒ)).map (fun x => (renameK σ x.1, renameC σ x.2)) := by
  cases h with
  | throws ℓ => simp only [renameH_throws, dispatchOn, Option.map_some, renameC_ret]
  | state ℓ s =>
    by_cases hget : op == "get"
    · simp only [renameH_state, dispatchOn, if_pos hget, Option.map_some, renameK_append,
        renameK_cons, renameF_handleF, renameH_state, renameC_ret]
    · simp only [renameH_state, dispatchOn, if_neg hget, Option.map_some, renameK_append,
        renameK_cons, renameF_handleF, renameH_state, renameC_ret, renameV_vunit]
  | transaction ℓ Θ =>
    by_cases hnew : op == "newTVar"
    · simp only [renameH_transaction, dispatchOn, if_pos hnew, Option.map_some, renameK_append,
        renameK_cons, renameF_handleF, renameH_transaction, renameC_ret, renameV_vint,
        List.map_append, List.map_cons, List.map_nil, List.length_map]
    · by_cases hread : op == "readTVar"
      · simp only [renameH_transaction, dispatchOn, if_neg hnew, if_pos hread, Option.map_some,
          renameK_append, renameK_cons, renameF_handleF, renameH_transaction, renameC_ret,
          tvarIdx_renameV, getD_map_fixed (renameV σ) Θ ((tvarIdx v).getD 0) (.vint 0) (renameV_vint σ 0)]
      · cases v <;>
          simp only [renameV_vunit, renameV_vint, renameV_vvar, renameV_vcap, renameV_vthunk,
            renameV_inl, renameV_inr, renameV_pair, renameV_fold, renameH_transaction, dispatchOn,
            if_neg hnew, if_neg hread, Option.map_some, renameK_append, renameK_cons,
            renameF_handleF, renameH_transaction, renameC_ret, tvarIdx_renameV, storeSet_map]

/-- **`idDispatch` commutes with an injective renaming.** -/
theorem idDispatch_rename (σ : Nat → Nat) (hσ : Function.Injective σ)
    (K : EvalCtx) (n : Nat) (ℓ : Label) (op : OpId) (v : Val) :
    idDispatch (renameK σ K) (σ n) ℓ op (renameV σ v)
      = (idDispatch K n ℓ op v).map (fun x => (renameK σ x.1, renameC σ x.2)) := by
  unfold idDispatch
  rw [splitAtId_rename σ hσ n K]
  cases hsplit : splitAtId K n with
  | none => rfl
  | some x =>
    obtain ⟨Kᵢ, h, Kₒ⟩ := x
    simp only [Option.map_some, Option.bind_some, handlesOp_renameH]
    by_cases hh : handlesOp h ℓ op
    · rw [if_pos hh, if_pos hh, dispatchOn_rename]
    · rw [if_neg hh, if_neg hh]; rfl

/-! ## 4. THE KEYSTONE — `Source.step` / `Config.run` commute with the renaming.

`renameCfg σ (g, K, c) := (σ g, renameK σ K, renameC σ c)` renames the WHOLE config (counter, stack
ids + stored caps, focus caps). `renameR` renames a `Result Val`. -/

def renameCfg (σ : Nat → Nat) : Config → Config
  | (g, K, c) => (σ g, renameK σ K, renameC σ c)

@[simp] theorem renameCfg_eq (σ : Nat → Nat) (g : Nat) (K : EvalCtx) (c : Comp) :
    renameCfg σ (g, K, c) = (σ g, renameK σ K, renameC σ c) := rfl

def renameR (σ : Nat → Nat) : Result Val → Result Val
  | .done v => .done (renameV σ v)
  | .oom    => .oom
  | .stuck  => .stuck

/-- The machine counter is MONOTONE: a step never decreases it (the only counter-touching arm,
`handle`, increments by one; every other arm threads it unchanged). This is what lets the `shift`
hypothesis `∀ k ≥ g, σ(k+1)=σk+1` weaken correctly down the run (newly-minted ids stay `≥ g`). -/
theorem step_counter_le {cfg cfg' : Config} (h : Source.step cfg = some cfg') : cfg.1 ≤ cfg'.1 := by
  obtain ⟨g, K, c⟩ := cfg
  cases c with
  | letC M N => simp only [Source.step, Option.some.injEq] at h; subst h; exact Nat.le_refl _
  | app M v => simp only [Source.step, Option.some.injEq] at h; subst h; exact Nat.le_refl _
  | handle hh M => simp only [Source.step, Option.some.injEq] at h; subst h; exact Nat.le_succ _
  | force w =>
    cases w <;> simp only [Source.step, Option.some.injEq, reduceCtorEq] at h <;>
      (try (subst h; exact Nat.le_refl _))
  | ret v =>
    cases K with
    | nil => simp only [Source.step, reduceCtorEq] at h
    | cons fr K' =>
      cases fr <;> simp only [Source.step, Option.some.injEq, reduceCtorEq] at h <;>
        (try (subst h; exact Nat.le_refl _))
  | lam M =>
    cases K with
    | nil => simp only [Source.step, reduceCtorEq] at h
    | cons fr K' =>
      cases fr <;> simp only [Source.step, Option.some.injEq, reduceCtorEq] at h <;>
        (try (subst h; exact Nat.le_refl _))
  | case w N₁ N₂ =>
    cases w <;> simp only [Source.step, Option.some.injEq, reduceCtorEq] at h <;>
      (try (subst h; exact Nat.le_refl _))
  | split w N =>
    cases w <;> simp only [Source.step, Option.some.injEq, reduceCtorEq] at h <;>
      (try (subst h; exact Nat.le_refl _))
  | unfold w =>
    cases w <;> simp only [Source.step, Option.some.injEq, reduceCtorEq] at h <;>
      (try (subst h; exact Nat.le_refl _))
  | perform cp op v =>
    cases cp with
    | vcap n ℓ =>
      simp only [Source.step] at h
      cases hd : idDispatch K n ℓ op v with
      | none => simp only [hd, Option.map_none, reduceCtorEq] at h
      | some y =>
        simp only [hd, Option.map_some, Option.some.injEq] at h; subst h; exact Nat.le_refl _
    | vunit => simp only [Source.step, reduceCtorEq] at h
    | vint _ => simp only [Source.step, reduceCtorEq] at h
    | vvar _ => simp only [Source.step, reduceCtorEq] at h
    | vthunk _ => simp only [Source.step, reduceCtorEq] at h
    | inl _ => simp only [Source.step, reduceCtorEq] at h
    | inr _ => simp only [Source.step, reduceCtorEq] at h
    | pair _ _ => simp only [Source.step, reduceCtorEq] at h
    | fold _ => simp only [Source.step, reduceCtorEq] at h
  | oom => simp only [Source.step, reduceCtorEq] at h
  | wrong s => simp only [Source.step, reduceCtorEq] at h


/-- **`Source.step` commutes with the renaming.** The only arm needing the shift hypothesis is `handle`
(the MINT): it mints `g`, which the renamed machine mints as `σ g`, advancing to `σ g + 1 = σ (g+1)`. -/
theorem step_rename (σ : Nat → Nat) (hσ : Function.Injective σ) (g : Nat) (K : EvalCtx) (c : Comp)
    (hsucc : σ (g + 1) = σ g + 1) :
    Source.step (renameCfg σ (g, K, c)) = (Source.step (g, K, c)).map (renameCfg σ) := by
  cases c with
  | letC M N =>
    simp only [renameCfg_eq, renameC_letC, Source.step, Option.map_some, renameK_cons, renameF_letF]
  | app M v =>
    simp only [renameCfg_eq, renameC_app, Source.step, Option.map_some, renameK_cons, renameF_appF]
  | handle hh M =>
    simp only [renameCfg_eq, renameC_handle, Source.step, Option.map_some, renameK_cons,
      renameF_handleF, renameC_subst, renameV_vcap, renameH_label, hsucc]
  | force w =>
    cases w <;> simp only [renameCfg_eq, renameC_force, renameV_vthunk, renameV_vunit, renameV_vint,
      renameV_vvar, renameV_vcap, renameV_inl, renameV_inr, renameV_pair, renameV_fold, Source.step,
      Option.map_some, Option.map_none]
  | ret v =>
    cases K with
    | nil => simp only [renameCfg_eq, renameC_ret, renameK_nil, Source.step, Option.map_none]
    | cons fr K' =>
      cases fr <;> simp only [renameCfg_eq, renameC_ret, renameK_cons, renameF_letF, renameF_appF,
        renameF_handleF, Source.step, Option.map_some, Option.map_none, renameC_subst]
  | lam M =>
    cases K with
    | nil => simp only [renameCfg_eq, renameC_lam, renameK_nil, Source.step, Option.map_none]
    | cons fr K' =>
      cases fr <;> simp only [renameCfg_eq, renameC_lam, renameK_cons, renameF_letF, renameF_appF,
        renameF_handleF, Source.step, Option.map_some, Option.map_none, renameC_subst]
  | case w N₁ N₂ =>
    cases w <;> simp only [renameCfg_eq, renameC_case, renameV_inl, renameV_inr, renameV_vunit,
      renameV_vint, renameV_vvar, renameV_vcap, renameV_vthunk, renameV_pair, renameV_fold,
      Source.step, Option.map_some, Option.map_none, renameC_subst]
  | split w N =>
    cases w <;> simp only [renameCfg_eq, renameC_split, renameV_pair, renameV_vunit, renameV_vint,
      renameV_vvar, renameV_vcap, renameV_vthunk, renameV_inl, renameV_inr, renameV_fold, Source.step,
      Option.map_some, Option.map_none, renameC_subst, renameV_shift]
  | unfold w =>
    cases w <;> simp only [renameCfg_eq, renameC_unfold, renameC_ret, renameV_fold, renameV_vunit,
      renameV_vint, renameV_vvar, renameV_vcap, renameV_vthunk, renameV_inl, renameV_inr, renameV_pair,
      Source.step, Option.map_some, Option.map_none]
  | perform cp op v =>
    cases cp with
    | vcap n ℓ =>
      simp only [renameCfg_eq, renameC_perform, renameV_vcap, Source.step]
      rw [idDispatch_rename σ hσ K n ℓ op v]
      cases idDispatch K n ℓ op v with
      | none => rfl
      | some y => rfl
    | vunit => simp only [renameCfg_eq, renameC_perform, renameV_vunit, Source.step, Option.map_none]
    | vint _ => simp only [renameCfg_eq, renameC_perform, renameV_vint, Source.step, Option.map_none]
    | vvar _ => simp only [renameCfg_eq, renameC_perform, renameV_vvar, Source.step, Option.map_none]
    | vthunk _ => simp only [renameCfg_eq, renameC_perform, renameV_vthunk, Source.step, Option.map_none]
    | inl _ => simp only [renameCfg_eq, renameC_perform, renameV_inl, Source.step, Option.map_none]
    | inr _ => simp only [renameCfg_eq, renameC_perform, renameV_inr, Source.step, Option.map_none]
    | pair _ _ => simp only [renameCfg_eq, renameC_perform, renameV_pair, Source.step, Option.map_none]
    | fold _ => simp only [renameCfg_eq, renameC_perform, renameV_fold, Source.step, Option.map_none]
  | oom => simp only [renameCfg_eq, renameC_oom, Source.step, Option.map_none]
  | wrong s => simp only [renameCfg_eq, renameC_wrong, Source.step, Option.map_none]

/-- A renamed config is terminal `(_, [], ret _)` exactly when the original is — so `Config.run_step`'s
non-returning side condition transfers across the renaming. -/
theorem renameCfg_ne_ret {cfg : Config} (hne : ∀ g v, cfg ≠ (g, [], Comp.ret v)) :
    ∀ g v, renameCfg σ cfg ≠ (g, [], Comp.ret v) := by
  obtain ⟨gc, Kc, cc⟩ := cfg
  intro g v hc
  simp only [renameCfg_eq, Prod.mk.injEq] at hc
  obtain ⟨_, hK, hcc⟩ := hc
  have hKnil : Kc = [] := by
    cases Kc with
    | nil => rfl
    | cons fr K => simp only [renameK_cons, reduceCtorEq] at hK
  cases cc with
  | ret w => exact hne gc w (by rw [hKnil])
  | letC _ _ => simp only [renameC_letC, reduceCtorEq] at hcc
  | force _ => simp only [renameC_force, reduceCtorEq] at hcc
  | lam _ => simp only [renameC_lam, reduceCtorEq] at hcc
  | app _ _ => simp only [renameC_app, reduceCtorEq] at hcc
  | perform _ _ _ => simp only [renameC_perform, reduceCtorEq] at hcc
  | handle _ _ => simp only [renameC_handle, reduceCtorEq] at hcc
  | case _ _ _ => simp only [renameC_case, reduceCtorEq] at hcc
  | split _ _ => simp only [renameC_split, reduceCtorEq] at hcc
  | unfold _ => simp only [renameC_unfold, reduceCtorEq] at hcc
  | oom => simp only [renameC_oom, reduceCtorEq] at hcc
  | wrong _ => simp only [renameC_wrong, reduceCtorEq] at hcc

/-- **THE KEYSTONE** — `Config.run` commutes with an injective renaming `σ` that acts as a SHIFT on the
fresh-id region `[g, ∞)` (`∀ k ≥ g, σ(k+1) = σ k + 1`). The renamed run produces the renamed result.

This is the general `Config.run`-renaming-invariance the inc-5 LR consumes: a permutation of the
canonical ids onto the original ids, extended by the shift on the tail, is exactly such a `σ`. -/
theorem run_rename (σ : Nat → Nat) (hσ : Function.Injective σ) :
    ∀ (n : Nat) (cfg : Config), (∀ k, cfg.1 ≤ k → σ (k + 1) = σ k + 1) →
      Config.run n (renameCfg σ cfg) = renameR σ (Config.run n cfg) := by
  intro n
  induction n with
  | zero => intro cfg _; rfl
  | succ m ih =>
    intro cfg hshift
    by_cases hterm : ∃ g v, cfg = (g, [], Comp.ret v)
    · obtain ⟨g, v, rfl⟩ := hterm
      simp only [renameCfg_eq, renameK_nil, renameC_ret]
      rfl
    · simp only [not_exists] at hterm
      have hne : ∀ g v, cfg ≠ (g, [], Comp.ret v) := hterm
      rw [Config.run_step m cfg hne, Config.run_step m (renameCfg σ cfg) (renameCfg_ne_ret hne)]
      obtain ⟨g, K, c⟩ := cfg
      have hsucc : σ (g + 1) = σ g + 1 := hshift g (Nat.le_refl _)
      rw [step_rename σ hσ g K c hsucc]
      cases hstep : Source.step (g, K, c) with
      | none => simp only [Option.map_none]; rfl
      | some cfg' =>
        simp only [Option.map_some]
        apply ih cfg'
        intro k hk
        exact hshift k (Nat.le_trans (step_counter_le hstep) hk)

/-! ## 5. SANITY + the corollaries the LR consumes. -/

/-- SANITY: the renamed config of the §4 witness mints the renamed id. -/
example (σ : Nat → Nat) (s : Val) (M : Comp) :
    renameCfg σ (7, [], Comp.handle (Handler.state 1 s) M)
      = (σ 7, [], Comp.handle (Handler.state 1 (renameV σ s)) (renameC σ M)) := by
  simp only [renameCfg_eq, renameK_nil, renameC_handle, renameH_state]

/-- **Convergence-invariance** (the form `converges_plug_iff`/`crelK`/`ConvergesC_le` read off): under
such a `σ`, the renamed config converges (to SOME value) iff the original does. This is the corollary the
inc-5 LR consumes at its three sites — the machine image of the canonical config and of the original-id
config co-converge. -/
theorem run_rename_converges (σ : Nat → Nat) (hσ : Function.Injective σ) (n : Nat) (cfg : Config)
    (hshift : ∀ k, cfg.1 ≤ k → σ (k + 1) = σ k + 1) :
    (∃ w, Config.run n (renameCfg σ cfg) = Result.done w)
      ↔ (∃ w, Config.run n cfg = Result.done w) := by
  rw [run_rename σ hσ n cfg hshift]
  cases Config.run n cfg <;> simp only [renameR, reduceCtorEq, Result.done.injEq, exists_eq']

#print axioms run_rename
#print axioms run_rename_converges
#print axioms step_rename
#print axioms idDispatch_rename
