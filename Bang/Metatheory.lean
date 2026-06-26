/-
  Bang/Metatheory.lean — syntactic metatheory (RESET for de Bruijn — ADR-0020).
  ──────────────────────────────────────────────────────────────────────────────
  The NAMED metatheory that used to live here (weakening, `grade_support`, the
  Finsupp grade-arithmetic lemmas, `subst_gen`, `subst_value_proof`) is DEAD
  under the de Bruijn representation: every lemma was named-encoding-specific
  (Finsupp `single`/`erase`, `(x,A) ∈ Γ` membership, the five binder
  side-conditions). It is preserved in git history (pre-ADR-0020).

  This file is intentionally a clean stub. A fresh proof-engineer pass rebuilds
  the metatheory directly on the de Bruijn base, porting Torczon's
  `resource/CBPV/renaming.v` + `substitution`:

    - `shiftFrom`/`substFrom` lemmas (Operational.lean) — the shift/subst
      interaction laws (autosubst's `compRenRen`/`compSubstSubst` analogues).
    - graded weakening = a *renaming* lemma (insert a 0-graded slot).
    - `subst_value` (Spec.lean) — the side-condition-free graded substitution
      lemma, the ADR-0020 payoff. Its statement is now honest; the proof is the
      next target.

  The grade-arithmetic *ideas* (read the bound multiplicity off the cons head,
  thread `+`/`•` through the rules) carry over; the lemmas do not. Build it
  fresh on `GradeVec.add`/`GradeVec.smul`/`GradeVec.basis` (List, positional).
-/

import Bang.Core
import Bang.Syntax
import Bang.Operational

namespace Bang

open Bang.EffectRow (Label)

variable {Eff  : Type} [Lattice Eff] [OrderBot Eff]
variable {Mult : Type} [CommSemiring Mult] [DecidableEq Mult]
variable [EffSig Eff Mult]

/-- Unfold the `HSMul`/`HAdd` notation on grade vectors to the underlying
`GradeVec.smul`/`GradeVec.add` (so the rewrite lemmas below fire on `•`/`+`). -/
@[simp] theorem hsmul_eq_smul (ρ : Mult) (γ : GradeVec Mult) :
    ρ • γ = GradeVec.smul ρ γ := rfl

@[simp] theorem hadd_eq_add (γ₁ γ₂ : GradeVec Mult) :
    γ₁ + γ₂ = GradeVec.add γ₁ γ₂ := rfl

/-! ## A. Grade-arithmetic lemmas over `List Mult`

`GradeVec.add = zipWith (·+·)`, `GradeVec.smul = map (ρ * ·)`. Ported shape from
`common/coeffects.v` (Torczon's `gradeVecAdd*`/`gradeVecScale*`), but over `List`
instead of `fin n → Q`. Length is NOT structural here, so several of these carry
a length-equality hypothesis or hold up-to-length. -/

namespace GradeVec

variable {M : Type}

@[simp] theorem add_nil_left [Add M] (γ : GradeVec M) :
    GradeVec.add [] γ = [] := rfl

@[simp] theorem add_nil_right [Add M] (γ : GradeVec M) :
    GradeVec.add γ [] = [] := by
  cases γ <;> rfl

@[simp] theorem add_cons [Add M] (a b : M) (γ₁ γ₂ : GradeVec M) :
    GradeVec.add (a :: γ₁) (b :: γ₂) = (a + b) :: GradeVec.add γ₁ γ₂ := rfl

@[simp] theorem smul_nil [Mul M] (ρ : M) :
    GradeVec.smul ρ ([] : GradeVec M) = [] := rfl

@[simp] theorem smul_cons [Mul M] (ρ a : M) (γ : GradeVec M) :
    GradeVec.smul ρ (a :: γ) = (ρ * a) :: GradeVec.smul ρ γ := rfl

@[simp] theorem smul_length [Mul M] (ρ : M) (γ : GradeVec M) :
    (GradeVec.smul ρ γ).length = γ.length := by
  simp [GradeVec.smul]

@[simp] theorem add_length [Add M] (γ₁ γ₂ : GradeVec M) :
    (GradeVec.add γ₁ γ₂).length = min γ₁.length γ₂.length := by
  simp [GradeVec.add]

@[simp] theorem zeros_length [Zero M] (n : Nat) :
    (GradeVec.zeros n : GradeVec M).length = n := by
  simp [GradeVec.zeros]

@[simp] theorem basis_length [Zero M] [One M] (n i : Nat) :
    (GradeVec.basis n i : GradeVec M).length = n := by
  simp [GradeVec.basis]

/-- `ρ • (a + b) = ρ•a + ρ•b` — scalar distributes over zipWith-add.
Holds unconditionally: both sides truncate to `min`. -/
theorem smul_add [Mul M] [Add M] [LeftDistribClass M] (ρ : M) (γ₁ γ₂ : GradeVec M) :
    GradeVec.smul ρ (GradeVec.add γ₁ γ₂)
      = GradeVec.add (GradeVec.smul ρ γ₁) (GradeVec.smul ρ γ₂) := by
  induction γ₁ generalizing γ₂ with
  | nil => rfl
  | cons a γ₁ ih =>
    cases γ₂ with
    | nil => rfl
    | cons b γ₂ => simp [GradeVec.add, GradeVec.smul, mul_add, ih]

/-- `ρ • zeros n = zeros n`. -/
@[simp] theorem smul_zeros [MulZeroClass M] (ρ : M) (n : Nat) :
    GradeVec.smul ρ (GradeVec.zeros n) = GradeVec.zeros n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show GradeVec.smul ρ (List.replicate (n + 1) 0) = List.replicate (n + 1) 0
    rw [List.replicate_succ]
    show GradeVec.smul ρ ((0 : M) :: GradeVec.zeros n) = (0 : M) :: GradeVec.zeros n
    rw [smul_cons, mul_zero, ih]

/-- `zeros n + γ = γ` when `γ` has length `n`. -/
theorem zeros_add [AddZeroClass M] (γ : GradeVec M) :
    GradeVec.add (GradeVec.zeros γ.length) γ = γ := by
  induction γ with
  | nil => rfl
  | cons a γ ih =>
    show GradeVec.add (List.replicate (γ.length + 1) 0) (a :: γ) = a :: γ
    rw [List.replicate_succ]
    show GradeVec.add ((0 : M) :: GradeVec.zeros γ.length) (a :: γ) = a :: γ
    rw [add_cons, zero_add, ih]

/-- `γ + zeros n = γ` when `γ` has length `n`. -/
theorem add_zeros [AddZeroClass M] (γ : GradeVec M) :
    GradeVec.add γ (GradeVec.zeros γ.length) = γ := by
  induction γ with
  | nil => rfl
  | cons a γ ih =>
    show GradeVec.add (a :: γ) (List.replicate (γ.length + 1) 0) = a :: γ
    rw [List.replicate_succ]
    show GradeVec.add (a :: γ) ((0 : M) :: GradeVec.zeros γ.length) = a :: γ
    rw [add_cons, add_zero, ih]

/-! ### A.2 `basis` / `zeros` under a prefix split (de Bruijn index shift)

These describe how a grade vector behaves when a fresh slot is inserted at
position `k = |prefix|`. They are the arithmetic core of the `vvar`/`vunit`
cases of the weakening lemma. -/

/-- `zeros (a+b) = zeros a ++ zeros b`. -/
theorem zeros_append [Zero M] (a b : Nat) :
    (GradeVec.zeros (a + b) : GradeVec M) = GradeVec.zeros a ++ GradeVec.zeros b := by
  rw [GradeVec.zeros, GradeVec.zeros, GradeVec.zeros, List.replicate_add]

/-- Uniform `getElem?` description of a basis vector. The single source of truth
for all the pointwise (`ext_getElem?`) basis proofs below. -/
theorem basis_get [Zero M] [One M] (n i j : Nat) :
    (GradeVec.basis n i : GradeVec M)[j]?
      = if j < n then some (if j = i then (1 : M) else 0) else none := by
  rw [GradeVec.basis, List.getElem?_map]
  by_cases h : j < n
  · rw [List.getElem?_range h]; simp [h]
  · rw [List.getElem?_eq_none (by simp; omega)]; simp [h]

/-- Uniform `getElem?` description of a zeros vector. -/
theorem zeros_get [Zero M] (n j : Nat) :
    (GradeVec.zeros n : GradeVec M)[j]? = if j < n then some (0 : M) else none := by
  rw [GradeVec.zeros, List.getElem?_replicate]

/-- Congruence for the basis cell value under equivalent index conditions. -/
theorem cell_congr {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q)
    [Zero M] [One M] :
    (if p then (1 : M) else 0) = if q then (1 : M) else 0 := by
  simp only [h]

/-- Generic getElem? of an inserted-at-`k` list (`k ≤ |l|`). -/
theorem insert_get {α : Type} (l : List α) (k : Nat) (x : α) (j : Nat) (hk : k ≤ l.length) :
    (l.take k ++ x :: l.drop k)[j]?
      = if j < k then l[j]? else if j = k then some x else l[j - 1]? := by
  rw [List.getElem?_append, List.length_take, min_eq_left hk]
  by_cases hjk : j < k
  · rw [if_pos hjk, if_pos hjk, List.getElem?_take_of_lt hjk]
  · rw [if_neg hjk, if_neg hjk]
    by_cases hjeq : j = k
    · subst hjeq; simp
    · have hpos : 0 < j - k := by omega
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j - k ≠ 0)
      rw [if_neg hjeq, hm, List.getElem?_cons_succ, List.getElem?_drop]
      congr 1; omega

/-- `basis n i` split at a prefix of length `k` (`k ≤ n`), inserting a 0 slot:
the entry stays at `i` if `i < k`, else shifts to `i+1`. -/
theorem basis_insert [Zero M] [One M] (n k i : Nat) (hk : k ≤ n) :
    (GradeVec.basis n i : GradeVec M).take k ++ (0 : M)
        :: (GradeVec.basis n i : GradeVec M).drop k
      = GradeVec.basis (n + 1) (if i < k then i else i + 1) := by
  apply List.ext_getElem?
  intro j
  rw [insert_get _ _ _ _ (by rw [basis_length]; exact hk)]
  simp only [basis_get]
  -- discharge every `if` simultaneously, then settle the value via omega
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 <;>
    first
      | rfl
      | (exfalso; omega)
      | (exact absurd rfl (by omega))
      | (symm; exact absurd rfl (by omega))

/-- The `k`-th entry of `basis n i`: `1` if `k = i` (and in range), else `0`. -/
theorem basis_getElem [Zero M] [One M] (n i k : Nat) (hk : k < n) :
    (GradeVec.basis n i : GradeVec M)[k]? = some (if k = i then (1 : M) else 0) := by
  rw [basis_get, if_pos hk]

/-- `zeros n` entries are all `0`. -/
theorem zeros_getElem [Zero M] (n k : Nat) (hk : k < n) :
    (GradeVec.zeros n : GradeVec M)[k]? = some (0 : M) := by
  rw [zeros_get, if_pos hk]

/-- Erasing position `k` from `basis n i` when the hot index is NOT at `k`
(`i ≠ k`, `k < n`): another basis vector of length `n-1`, hot index shifted down
if it was above `k`. (At `i = k` the result is the zero vector; that case is
handled directly in the `vvar` proof, which substitutes `v` there.) -/
theorem basis_eraseIdx [Zero M] [One M] (n i k : Nat) (hk : k < n) (hik : i ≠ k) :
    (GradeVec.basis n i : GradeVec M).eraseIdx k
      = GradeVec.basis (n - 1) (if i < k then i else i - 1) := by
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_eraseIdx]
  by_cases hjk : j < k <;> simp only [hjk, if_true, if_false, basis_get] <;>
    split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 <;>
    first
      | rfl
      | (exfalso; omega)
      | (exact absurd rfl (by omega))
      | (symm; exact absurd rfl (by omega))

/-- Erasing any position from `zeros n` gives `zeros (n-1)` (for `k < n`). -/
theorem zeros_eraseIdx [Zero M] (n k : Nat) (hk : k < n) :
    (GradeVec.zeros n : GradeVec M).eraseIdx k = GradeVec.zeros (n - 1) := by
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_eraseIdx, zeros_get, zeros_get, zeros_get]
  by_cases hjk : j < k <;> simp only [hjk, if_true, if_false] <;>
    split_ifs with h1 h2 h3 h4 <;> first | rfl | (exfalso; omega)

end GradeVec

/-! ## B. Length invariant: every derivation has `γ.length = Γ.length`

This is the structural fact that the ADR-0020 `List` carrier needs as a *theorem*
(it is "by construction" but not type-enforced). With it in hand, `zipWith`
truncation never bites — `γ + γ_v` is always full-length because both summands
match `Γ.length`. Proved by mutual induction; the grade-arithmetic length simp
lemmas above discharge each case. -/

/-- Mutual length invariant. Rewritten to `induction … using ….rec` with NAMED
cases (ADR-0029 added ADT constructors; positional `.rec` arms were brittle). Each
arm is a mechanical grade-length fact. -/
theorem HasCTy.length_eq {γ : GradeVec Mult} {Γ : TyCtx Eff Mult}
    {c : Comp} {e : Eff} {B : CTy Eff Mult} :
    HasCTy γ Γ c e B → γ.length = Γ.length := by
  intro h
  refine HasCTy.rec
    (motive_1 := fun γ Γ _ _ _ => γ.length = Γ.length)
    (motive_2 := fun γ Γ _ _ _ _ => γ.length = Γ.length)
    ?vunit ?vint ?vvar ?vcap ?vthunk ?inl ?inr ?pair ?fold
    ?ret ?letC ?force ?lam ?app ?case ?split ?unfold ?perform ?handleThrows ?handleState
    ?handleTransaction h
  case vunit => intro Γ; simp
  case vint => intro Γ n; simp
  case vvar => intro Γ i A hget; simp
  case vcap => intro Γ n ℓ; simp
  case vthunk => intro γ Γ M φ B _ ih; exact ih
  case inl => intro γ Γ w A B _ ih; exact ih
  case inr => intro γ Γ w A B _ ih; exact ih
  case pair => intro γ γ_v γ_w Γ w₁ w₂ A B _ _ hγ ihv ihw; subst hγ
               simp only [hadd_eq_add, GradeVec.add_length, ihv, ihw, Nat.min_self]
  case fold => intro γ Γ w A _ ih; exact ih
  case ret => intro γ γ' Γ w A q _ hγ ih; subst hγ
              simp only [hsmul_eq_smul, GradeVec.smul_length]; exact ih
  case letC => intro γ γ₁ γ₂ Γ M N φ₁ φ₂ q1 q2 A B _ _ hγ ihM ihN; subst hγ
               simp only [List.length_cons] at ihN
               simp only [hsmul_eq_smul, hadd_eq_add, GradeVec.add_length, GradeVec.smul_length,
                 ihM, Nat.succ.inj ihN, Nat.min_self]
  case force => intro γ Γ w φ B _ ih; exact ih
  case lam => intro γ Γ M φ q A B _ ih; simp only [List.length_cons] at ih; exact Nat.succ.inj ih
  case app => intro γ γ₁ γ₂ Γ M w φ q A B _ _ hγ ihM ihV; subst hγ
              simp only [hsmul_eq_smul, hadd_eq_add, GradeVec.add_length, GradeVec.smul_length,
                ihM, ihV, Nat.min_self]
  case case => intro γ γ_v γ_N Γ v N₁ N₂ φ q A B C _ _ _ hγ ihv ih₁ _; subst hγ
               simp only [List.length_cons] at ih₁
               simp only [hsmul_eq_smul, hadd_eq_add, GradeVec.add_length, GradeVec.smul_length,
                 ihv, Nat.succ.inj ih₁, Nat.min_self]
  case split => intro γ γ_v γ_N Γ v N φ q A B C _ _ hγ ihv ihN; subst hγ
                simp only [List.length_cons] at ihN
                simp only [hsmul_eq_smul, hadd_eq_add, GradeVec.add_length, GradeVec.smul_length,
                  ihv, Nat.succ.inj (Nat.succ.inj ihN), Nat.min_self]
  case unfold => intro γ Γ v A _ ih; exact ih
  case perform => intro γ_c γ_v Γ _c ℓ op w φ q A B _hcap _hle _harg _hres _hv ih_cap ih_v
                  -- ADR-0054: perform now carries the cap derivation (grade γ_c) alongside the arg (γ_v):
                  -- grade `(q • γ_v) + γ_c`. Both IHs give `_.length = Γ.length`.
                  simp only [hsmul_eq_smul, hadd_eq_add, GradeVec.add_length, GradeVec.smul_length,
                    ih_v, ih_cap, Nat.min_self]
  -- ADR-0054: handle BINDS the cap (mult `qc`), so the body grade is `qc :: γ` ⇒ the IH gives
  -- `(qc::γ).length = (cap ℓ::Γ).length`; strip the cons (`Nat.succ.inj`) for `γ.length = Γ.length`.
  case handleThrows => intro γ Γ ℓ M e φ q qc A _ _ _ _ _ ih
                       simp only [List.length_cons] at ih; exact Nat.succ.inj ih
  case handleState => intro γ Γ ℓ s₀ M e φ q qc S A _ _ _ _ _ _ _ _ _ _ ihM
                      simp only [List.length_cons] at ihM; exact Nat.succ.inj ihM
  case handleTransaction =>
    intro γ Γ ℓ Θ₀ M e φ q qc A _ _ _ _ _ _ _ _ _ _ _ _ ihM
    simp only [List.length_cons] at ihM; exact Nat.succ.inj ihM

theorem HasVTy.length_eq {γ : GradeVec Mult} {Γ : TyCtx Eff Mult}
    {v : Val} {A : VTy Eff Mult} :
    HasVTy γ Γ v A → γ.length = Γ.length := by
  intro h
  refine HasVTy.rec
    (motive_1 := fun γ Γ _ _ _ => γ.length = Γ.length)
    (motive_2 := fun γ Γ _ _ _ _ => γ.length = Γ.length)
    ?vunit ?vint ?vvar ?vcap ?vthunk ?inl ?inr ?pair ?fold
    ?ret ?letC ?force ?lam ?app ?case ?split ?unfold ?perform ?handleThrows ?handleState
    ?handleTransaction h
  case vunit => intro Γ; simp
  case vint => intro Γ n; simp
  case vvar => intro Γ i A hget; simp
  case vcap => intro Γ n ℓ; simp
  case vthunk => intro γ Γ M φ B _ ih; exact ih
  case inl => intro γ Γ w A B _ ih; exact ih
  case inr => intro γ Γ w A B _ ih; exact ih
  case pair => intro γ γ_v γ_w Γ w₁ w₂ A B _ _ hγ ihv ihw; subst hγ
               simp only [hadd_eq_add, GradeVec.add_length, ihv, ihw, Nat.min_self]
  case fold => intro γ Γ w A _ ih; exact ih
  case ret => intro γ γ' Γ w A q _ hγ ih; subst hγ
              simp only [hsmul_eq_smul, GradeVec.smul_length]; exact ih
  case letC => intro γ γ₁ γ₂ Γ M N φ₁ φ₂ q1 q2 A B _ _ hγ ihM ihN; subst hγ
               simp only [List.length_cons] at ihN
               simp only [hsmul_eq_smul, hadd_eq_add, GradeVec.add_length, GradeVec.smul_length,
                 ihM, Nat.succ.inj ihN, Nat.min_self]
  case force => intro γ Γ w φ B _ ih; exact ih
  case lam => intro γ Γ M φ q A B _ ih; simp only [List.length_cons] at ih; exact Nat.succ.inj ih
  case app => intro γ γ₁ γ₂ Γ M w φ q A B _ _ hγ ihM ihV; subst hγ
              simp only [hsmul_eq_smul, hadd_eq_add, GradeVec.add_length, GradeVec.smul_length,
                ihM, ihV, Nat.min_self]
  case case => intro γ γ_v γ_N Γ v N₁ N₂ φ q A B C _ _ _ hγ ihv ih₁ _; subst hγ
               simp only [List.length_cons] at ih₁
               simp only [hsmul_eq_smul, hadd_eq_add, GradeVec.add_length, GradeVec.smul_length,
                 ihv, Nat.succ.inj ih₁, Nat.min_self]
  case split => intro γ γ_v γ_N Γ v N φ q A B C _ _ hγ ihv ihN; subst hγ
                simp only [List.length_cons] at ihN
                simp only [hsmul_eq_smul, hadd_eq_add, GradeVec.add_length, GradeVec.smul_length,
                  ihv, Nat.succ.inj (Nat.succ.inj ihN), Nat.min_self]
  case unfold => intro γ Γ v A _ ih; exact ih
  case perform => intro γ_c γ_v Γ _c ℓ op w φ q A B _hcap _hle _harg _hres _hv ih_cap ih_v
                  -- ADR-0054: perform now carries the cap derivation (grade γ_c) alongside the arg (γ_v):
                  -- grade `(q • γ_v) + γ_c`. Both IHs give `_.length = Γ.length`.
                  simp only [hsmul_eq_smul, hadd_eq_add, GradeVec.add_length, GradeVec.smul_length,
                    ih_v, ih_cap, Nat.min_self]
  -- ADR-0054: handle BINDS the cap (mult `qc`), so the body grade is `qc :: γ` ⇒ the IH gives
  -- `(qc::γ).length = (cap ℓ::Γ).length`; strip the cons (`Nat.succ.inj`) for `γ.length = Γ.length`.
  case handleThrows => intro γ Γ ℓ M e φ q qc A _ _ _ _ _ ih
                       simp only [List.length_cons] at ih; exact Nat.succ.inj ih
  case handleState => intro γ Γ ℓ s₀ M e φ q qc S A _ _ _ _ _ _ _ _ _ _ ihM
                      simp only [List.length_cons] at ihM; exact Nat.succ.inj ihM
  case handleTransaction =>
    intro γ Γ ℓ Θ₀ M e φ q qc A _ _ _ _ _ _ _ _ _ _ _ _ ihM
    simp only [List.length_cons] at ihM; exact Nat.succ.inj ihM

/-! ## C. Weakening / shift  (port of `renaming.v` `shift_wb` case)

Inserting a fresh, 0-graded binding at de Bruijn cutoff `k` preserves typing,
with all free indices `≥ k` shifted up by one (`shiftFrom k`). This is the
load-bearing lemma for descending under binders in the substitution proof.

The grade-vector with a 0 inserted at position `k` is written
`γ.take k ++ 0 :: γ.drop k`. The context with a fresh type `A'` inserted at `k`
is `Γ.take k ++ A' :: Γ.drop k`. We carry `k = Γ'.length` for some prefix split,
generalized so binders can grow the prefix. -/

/-- Insert grade 0 / type `A'` at cutoff `k` in a context. Helper notation. -/
private abbrev insG (γ : GradeVec Mult) (k : Nat) : GradeVec Mult :=
  γ.take k ++ (0 : Mult) :: γ.drop k

private abbrev insT (Γ : TyCtx Eff Mult) (k : Nat) (A' : VTy Eff Mult) : TyCtx Eff Mult :=
  Γ.take k ++ A' :: Γ.drop k

/-- `insG` commutes with scaling: inserting a 0 at `k` then scaling = scaling then
inserting (since `q * 0 = 0`). -/
private theorem insG_smul (q : Mult) (γ : GradeVec Mult) (k : Nat) :
    insG (GradeVec.smul q γ) k = GradeVec.smul q (insG γ k) := by
  show (GradeVec.smul q γ).take k ++ (0:Mult) :: (GradeVec.smul q γ).drop k
    = GradeVec.smul q (γ.take k ++ (0:Mult) :: γ.drop k)
  simp only [GradeVec.smul, List.map_append, List.map_take, List.map_drop, List.map_cons,
    mul_zero]

/-- `insG` commutes with addition when the two vectors agree in length (so the
`take`/`drop` split lines up). -/
private theorem insG_add (γ₁ γ₂ : GradeVec Mult) (k : Nat)
    (hlen : γ₁.length = γ₂.length) :
    insG (GradeVec.add γ₁ γ₂) k = GradeVec.add (insG γ₁ k) (insG γ₂ k) := by
  unfold insG GradeVec.add
  rw [List.take_zipWith, List.drop_zipWith,
    List.zipWith_append (by rw [List.length_take, List.length_take, hlen]),
    List.zipWith_cons_cons, zero_add]

/-- Reshape lemma for the `letC` / `let`-style grade `(q' • γ₁) + γ₂`. -/
private theorem insG_add_smul_aux (q : Mult) (γ₁ γ₂ : GradeVec Mult) (k : Nat)
    (h1 : γ₁.length = γ₂.length) :
    insG (GradeVec.add (GradeVec.smul q γ₁) γ₂) k
      = GradeVec.add (GradeVec.smul q (insG γ₁ k)) (insG γ₂ k) := by
  rw [insG_add _ _ _ (by rw [GradeVec.smul_length, h1]), insG_smul]

/-- Reshape lemma for the `app`-style grade `γ₁ + (q • γ₂)`. -/
private theorem insG_add_smul_aux' (q : Mult) (γ₁ γ₂ : GradeVec Mult) (k : Nat)
    (h1 : γ₁.length = γ₂.length) :
    insG (GradeVec.add γ₁ (GradeVec.smul q γ₂)) k
      = GradeVec.add (insG γ₁ k) (GradeVec.smul q (insG γ₂ k)) := by
  rw [insG_add _ _ _ (by rw [GradeVec.smul_length, h1]), insG_smul]

/-! ### C.1 Closed values are shift- and subst-invariant (ADR-0025)

A value/computation typed under a length-`n` context mentions only de Bruijn indices `< n`, so a
`shiftFrom k`/`substFrom k` at cutoff `k ≥ n` leaves it unchanged. The `state` handler stores a CLOSED
state (`HasVTy [] [] s₀ S`, `n = 0`), so it survives weakening (`shiftFrom k s₀ = s₀`) and substitution
(`substFrom k v s₀ = s₀`) under any binder — the engine that makes `handleState` thread through
`weaken`/`subst` without grade content (the closed focus, ADR-0025 D2). -/

mutual
theorem HasVTy.shift_closed {γ : GradeVec Mult} {Γ : TyCtx Eff Mult}
    {v : Val} {A : VTy Eff Mult} (h : HasVTy γ Γ v A) (k : Nat) (hk : Γ.length ≤ k) :
    Val.shiftFrom k v = v := by
  cases h with
  | vunit => rfl
  | vint  => rfl
  | @vvar Γ i A hget =>
    -- i < Γ.length ≤ k, so the index is bound (below cutoff) and not shifted
    have hi : i < Γ.length := by
      rw [List.getElem?_eq_some_iff] at hget; exact hget.1
    simp only [Val.shiftFrom]; rw [if_pos (by omega)]
  | @vcap Γ n ℓ => rfl                            -- a capability is closed: shift is the identity
  | @vthunk γ Γ M φ B hM =>
    simp only [Val.shiftFrom]; rw [hM.shift_closed k hk]
  | @inl γ Γ w A B hw => simp only [Val.shiftFrom]; rw [hw.shift_closed k hk]
  | @inr γ Γ w A B hw => simp only [Val.shiftFrom]; rw [hw.shift_closed k hk]
  | @pair γ γ_v γ_w Γ w₁ w₂ A B hw₁ hw₂ _ =>
    simp only [Val.shiftFrom]; rw [hw₁.shift_closed k hk, hw₂.shift_closed k hk]
  | @fold γ Γ w A hw => simp only [Val.shiftFrom]; rw [hw.shift_closed k hk]

theorem HasCTy.shift_closed {γ : GradeVec Mult} {Γ : TyCtx Eff Mult}
    {c : Comp} {e : Eff} {C : CTy Eff Mult} (h : HasCTy γ Γ c e C) (k : Nat) (hk : Γ.length ≤ k) :
    Comp.shiftFrom k c = c := by
  cases h with
  | @ret γ γ' Γ v A q hv _ => simp only [Comp.shiftFrom]; rw [hv.shift_closed k hk]
  | @letC γ γ₁ γ₂ Γ M N φ₁ φ₂ q1 q2 A B hM hN _ =>
    simp only [Comp.shiftFrom]
    rw [hM.shift_closed k hk, hN.shift_closed (k + 1) (by simp only [List.length_cons]; omega)]
  | @force γ Γ v φ B hv => simp only [Comp.shiftFrom]; rw [hv.shift_closed k hk]
  | @lam γ Γ M φ q A B hM =>
    simp only [Comp.shiftFrom]
    rw [hM.shift_closed (k + 1) (by simp only [List.length_cons]; omega)]
  | @app γ γ₁ γ₂ Γ M v φ q A B hM hv _ =>
    simp only [Comp.shiftFrom]; rw [hM.shift_closed k hk, hv.shift_closed k hk]
  | @case γ γ_v γ_N Γ v N₁ N₂ φ q A B C hv hN₁ hN₂ _ =>
    simp only [Comp.shiftFrom]
    rw [hv.shift_closed k hk, hN₁.shift_closed (k + 1) (by simp only [List.length_cons]; omega),
      hN₂.shift_closed (k + 1) (by simp only [List.length_cons]; omega)]
  | @split γ γ_v γ_N Γ v N φ q A B C hv hN _ =>
    simp only [Comp.shiftFrom]
    rw [hv.shift_closed k hk, hN.shift_closed (k + 2) (by simp only [List.length_cons]; omega)]
  | @unfold γ Γ v A hv => simp only [Comp.shiftFrom]; rw [hv.shift_closed k hk]
  | @perform γ_c γ_v Γ c ℓ op v φ q A B hcap _ _ _ hv =>
    -- ADR-0054: perform carries the cap value `c` (closed) + the arg `v`; both shift-fixed.
    simp only [Comp.shiftFrom]; rw [hcap.shift_closed k hk, hv.shift_closed k hk]
  -- ADR-0054: handle BINDS the cap, so the body context is `cap ℓ :: Γ` (length +1) ⇒ cutoff `k+1`.
  | @handleThrows γ Γ ℓ M e φ q qc A _ _ hM _ _ =>
    simp only [Comp.shiftFrom, Handler.shiftFrom]
    rw [hM.shift_closed (k + 1) (by simp only [List.length_cons]; omega)]
  | @handleState γ Γ ℓ s₀ M e φ q qc S A _ _ _ _ _ hs hM _ _ =>
    simp only [Comp.shiftFrom, Handler.shiftFrom]
    rw [hM.shift_closed (k + 1) (by simp only [List.length_cons]; omega),
      hs.shift_closed k (Nat.zero_le k)]
  | @handleTransaction γ Γ ℓ Θ₀ M e φ q qc A _ _ _ _ _ _ _ hcells hM _ _ =>
    -- `Handler.shiftFrom` leaves the heap untouched (closed cells, ADR-0030); body fixed by IH at k+1.
    simp only [Comp.shiftFrom, Handler.shiftFrom]
    rw [hM.shift_closed (k + 1) (by simp only [List.length_cons]; omega)]
end

mutual
theorem HasVTy.subst_closed {γ : GradeVec Mult} {Γ : TyCtx Eff Mult}
    {v : Val} {A : VTy Eff Mult} (h : HasVTy γ Γ v A) (k : Nat) (hk : Γ.length ≤ k) (w : Val) :
    Val.substFrom k w v = v := by
  cases h with
  | vunit => rfl
  | vint  => rfl
  | @vvar Γ i A hget =>
    have hi : i < Γ.length := by
      rw [List.getElem?_eq_some_iff] at hget; exact hget.1
    simp only [Val.substFrom]; rw [if_neg (by omega), if_neg (by omega)]
  | @vcap Γ n ℓ => rfl                            -- a capability is closed: subst is the identity
  | @vthunk γ Γ M φ B hM =>
    simp only [Val.substFrom]; rw [hM.subst_closed k hk w]
  | @inl γ Γ u A B hu => simp only [Val.substFrom]; rw [hu.subst_closed k hk w]
  | @inr γ Γ u A B hu => simp only [Val.substFrom]; rw [hu.subst_closed k hk w]
  | @pair γ γ_v γ_w Γ u₁ u₂ A B hu₁ hu₂ _ =>
    simp only [Val.substFrom]; rw [hu₁.subst_closed k hk w, hu₂.subst_closed k hk w]
  | @fold γ Γ u A hu => simp only [Val.substFrom]; rw [hu.subst_closed k hk w]

theorem HasCTy.subst_closed {γ : GradeVec Mult} {Γ : TyCtx Eff Mult}
    {c : Comp} {e : Eff} {C : CTy Eff Mult} (h : HasCTy γ Γ c e C) (k : Nat) (hk : Γ.length ≤ k)
    (w : Val) : Comp.substFrom k w c = c := by
  cases h with
  | @ret γ γ' Γ v A q hv _ => simp only [Comp.substFrom]; rw [hv.subst_closed k hk w]
  | @letC γ γ₁ γ₂ Γ M N φ₁ φ₂ q1 q2 A B hM hN _ =>
    simp only [Comp.substFrom]
    rw [hM.subst_closed k hk w, hN.subst_closed (k + 1) (by simp only [List.length_cons]; omega) _]
  | @force γ Γ v φ B hv => simp only [Comp.substFrom]; rw [hv.subst_closed k hk w]
  | @lam γ Γ M φ q A B hM =>
    simp only [Comp.substFrom]
    rw [hM.subst_closed (k + 1) (by simp only [List.length_cons]; omega) _]
  | @app γ γ₁ γ₂ Γ M v φ q A B hM hv _ =>
    simp only [Comp.substFrom]; rw [hM.subst_closed k hk w, hv.subst_closed k hk w]
  | @case γ γ_v γ_N Γ v N₁ N₂ φ q A B C hv hN₁ hN₂ _ =>
    simp only [Comp.substFrom]
    rw [hv.subst_closed k hk w, hN₁.subst_closed (k + 1) (by simp only [List.length_cons]; omega) _,
      hN₂.subst_closed (k + 1) (by simp only [List.length_cons]; omega) _]
  | @split γ γ_v γ_N Γ v N φ q A B C hv hN _ =>
    simp only [Comp.substFrom]
    rw [hv.subst_closed k hk w, hN.subst_closed (k + 2) (by simp only [List.length_cons]; omega) _]
  | @unfold γ Γ v A hv => simp only [Comp.substFrom]; rw [hv.subst_closed k hk w]
  | @perform γ_c γ_v Γ c ℓ op v φ q A B hcap _ _ _ hv =>
    -- ADR-0054: perform carries the cap value `c` (closed) + the arg `v`; both subst-fixed.
    simp only [Comp.substFrom]; rw [hcap.subst_closed k hk w, hv.subst_closed k hk w]
  -- ADR-0054: handle BINDS the cap, so the body context is `cap ℓ :: Γ` (length +1) ⇒ the body
  -- substitutes at cutoff `k+1` with the lifted filler `shift w`; a CLOSED body is fixed by the IH.
  | @handleThrows γ Γ ℓ M e φ q qc A _ _ hM _ _ =>
    simp only [Comp.substFrom, Handler.substFrom]
    rw [hM.subst_closed (k + 1) (by simp only [List.length_cons]; omega) (Val.shift w)]
  | @handleState γ Γ ℓ s₀ M e φ q qc S A _ _ _ _ _ hs hM _ _ =>
    simp only [Comp.substFrom, Handler.substFrom]
    rw [hM.subst_closed (k + 1) (by simp only [List.length_cons]; omega) (Val.shift w),
      hs.subst_closed k (Nat.zero_le k) w]
  | @handleTransaction γ Γ ℓ Θ₀ M e φ q qc A _ _ _ _ _ _ _ hcells hM _ _ =>
    -- `Handler.substFrom` leaves the heap untouched (closed cells, ADR-0030); body fixed by IH at k+1.
    simp only [Comp.substFrom, Handler.substFrom]
    rw [hM.subst_closed (k + 1) (by simp only [List.length_cons]; omega) (Val.shift w)]
end

/-! ### ADR-0053: `HasVTy.shiftCap`/`HasCTy.shiftCap` (the cap-shift-preserves-typing re-typing theorems)
are DELETED. Caps are absolute root-levels: `subst`'s `handle` case fills the body with the UNSHIFTED
filler, so the STD handle arms re-type at the filler `v` directly (no `HasVTy.shiftCap`). With the
`shiftCapFrom` operation dead on all live paths, these re-typing theorems have no consumers. The
de-Bruijn shift wall (ADR-0050) is dissolved by construction. -/

mutual
theorem HasVTy.weaken {γ : GradeVec Mult} {Γ : TyCtx Eff Mult}
    {v : Val} {A : VTy Eff Mult}
    (h : HasVTy γ Γ v A) (k : Nat) (hk : k ≤ Γ.length) (A' : VTy Eff Mult) :
    HasVTy (insG γ k) (insT Γ k A') (Val.shiftFrom k v) A := by
  cases h with
  | @vunit Γ =>
    -- γ = zeros Γ.length ; insert 0 → zeros (Γ.length+1)
    have hlen : (GradeVec.zeros Γ.length : GradeVec Mult).length = Γ.length := by simp
    show HasVTy (insG (GradeVec.zeros Γ.length) k) (insT Γ k A') Val.vunit VTy.unit
    have : insG (GradeVec.zeros Γ.length) k
        = (GradeVec.zeros (insT Γ k A').length : GradeVec Mult) := by
      apply List.ext_getElem?
      intro j
      show ((GradeVec.zeros Γ.length).take k ++ (0:Mult) :: (GradeVec.zeros Γ.length).drop k)[j]?
        = (GradeVec.zeros (insT Γ k A').length : GradeVec Mult)[j]?
      rw [GradeVec.insert_get _ _ _ _ (by rw [GradeVec.zeros_length]; omega),
        GradeVec.zeros_get]
      simp only [GradeVec.zeros_get]
      have hl : (insT Γ k A').length = Γ.length + 1 := by
        simp only [insT, List.length_append, List.length_cons, List.length_take,
          List.length_drop]; omega
      rw [hl]
      split_ifs <;> first | rfl | (exfalso; omega)
    exact this ▸ HasVTy.vunit
  | @vint Γ n =>
    show HasVTy (insG (GradeVec.zeros Γ.length) k) (insT Γ k A') (Val.vint n) VTy.int
    have : insG (GradeVec.zeros Γ.length) k
        = (GradeVec.zeros (insT Γ k A').length : GradeVec Mult) := by
      apply List.ext_getElem?
      intro j
      show ((GradeVec.zeros Γ.length).take k ++ (0:Mult) :: (GradeVec.zeros Γ.length).drop k)[j]?
        = (GradeVec.zeros (insT Γ k A').length : GradeVec Mult)[j]?
      rw [GradeVec.insert_get _ _ _ _ (by rw [GradeVec.zeros_length]; omega),
        GradeVec.zeros_get]
      simp only [GradeVec.zeros_get]
      have hl : (insT Γ k A').length = Γ.length + 1 := by
        simp only [insT, List.length_append, List.length_cons, List.length_take,
          List.length_drop]; omega
      rw [hl]
      split_ifs <;> first | rfl | (exfalso; omega)
    exact this ▸ HasVTy.vint
  | @vvar Γ i A hget =>
    -- shiftFrom k (vvar i) = if i < k then vvar i else vvar (i+1)
    simp only [Val.shiftFrom]
    have hgetins : (insT Γ k A')[if i < k then i else i + 1]? = some A := by
      unfold insT
      by_cases hik : i < k
      · rw [if_pos hik]
        rw [List.getElem?_append_left (by rw [List.length_take]; omega)]
        rw [List.getElem?_take_of_lt hik]; exact hget
      · rw [if_neg hik]
        push_neg at hik
        rw [List.getElem?_append_right (by rw [List.length_take]; omega)]
        rw [List.length_take, min_eq_left hk]
        rw [show i + 1 - k = (i - k) + 1 by omega, List.getElem?_cons_succ,
          List.getElem?_drop]
        have : k + (i - k) = i := by omega
        rw [this]; exact hget
    have hbasis : insG (GradeVec.basis Γ.length i) k
        = (GradeVec.basis (insT Γ k A').length (if i < k then i else i + 1) : GradeVec Mult) := by
      show (GradeVec.basis Γ.length i : GradeVec Mult).take k ++ (0:Mult)
          :: (GradeVec.basis Γ.length i).drop k = _
      rw [GradeVec.basis_insert (M := Mult) Γ.length k i hk]
      have hl : (insT Γ k A').length = Γ.length + 1 := by
        simp only [insT, List.length_append, List.length_cons, List.length_take,
          List.length_drop]; omega
      rw [hl]
    by_cases hik : i < k
    · rw [if_pos hik]
      rw [if_pos hik] at hbasis
      rw [hbasis]
      exact HasVTy.vvar (by rw [if_pos hik] at hgetins; exact hgetins)
    · rw [if_neg hik]
      rw [if_neg hik] at hbasis
      rw [hbasis]
      exact HasVTy.vvar (by rw [if_neg hik] at hgetins; exact hgetins)
  | @vcap Γ n ℓ =>
    -- a capability is inert (grade `zeros`, like `vunit`/`vint`) and closed (shift = id);
    -- the inserted 0 keeps the grade `zeros` at the longer context length.
    show HasVTy (insG (GradeVec.zeros Γ.length) k) (insT Γ k A') (Val.vcap n ℓ) (VTy.cap ℓ)
    have : insG (GradeVec.zeros Γ.length) k
        = (GradeVec.zeros (insT Γ k A').length : GradeVec Mult) := by
      apply List.ext_getElem?
      intro j
      show ((GradeVec.zeros Γ.length).take k ++ (0:Mult) :: (GradeVec.zeros Γ.length).drop k)[j]?
        = (GradeVec.zeros (insT Γ k A').length : GradeVec Mult)[j]?
      rw [GradeVec.insert_get _ _ _ _ (by rw [GradeVec.zeros_length]; omega),
        GradeVec.zeros_get]
      simp only [GradeVec.zeros_get]
      have hl : (insT Γ k A').length = Γ.length + 1 := by
        simp only [insT, List.length_append, List.length_cons, List.length_take,
          List.length_drop]; omega
      rw [hl]
      split_ifs <;> first | rfl | (exfalso; omega)
    exact this ▸ HasVTy.vcap
  | @vthunk γ Γ M φ B hM =>
    simp only [Val.shiftFrom]
    exact HasVTy.vthunk (hM.weaken k hk A')
  | @inl γ Γ w A B hw =>
    simp only [Val.shiftFrom]
    exact HasVTy.inl (hw.weaken k hk A')
  | @inr γ Γ w A B hw =>
    simp only [Val.shiftFrom]
    exact HasVTy.inr (hw.weaken k hk A')
  | @pair γ γ_v γ_w Γ w₁ w₂ A B hw₁ hw₂ hγ =>
    subst hγ
    simp only [Val.shiftFrom]
    refine HasVTy.pair (hw₁.weaken k hk A') (hw₂.weaken k hk A') ?_
    -- insG (γ_v + γ_w) k = insG γ_v k + insG γ_w k
    exact insG_add γ_v γ_w k (by rw [hw₁.length_eq, hw₂.length_eq])
  | @fold γ Γ w A hw =>
    simp only [Val.shiftFrom]
    exact HasVTy.fold (hw.weaken k hk A')

theorem HasCTy.weaken {γ : GradeVec Mult} {Γ : TyCtx Eff Mult}
    {c : Comp} {e : Eff} {B : CTy Eff Mult}
    (h : HasCTy γ Γ c e B) (k : Nat) (hk : k ≤ Γ.length) (A' : VTy Eff Mult) :
    HasCTy (insG γ k) (insT Γ k A') (Comp.shiftFrom k c) e B := by
  cases h with
  | @ret γ γ' Γ v A q hv hγ =>
    subst hγ
    simp only [Comp.shiftFrom]
    refine HasCTy.ret (hv.weaken k hk A') ?_
    -- insG (q • γ') k = q • insG γ' k
    exact insG_smul q γ' k
  | @letC γ γ₁ γ₂ Γ M N φ₁ φ₂ q1 q2 A B hM hN hγ =>
    subst hγ
    simp only [Comp.shiftFrom]
    have hM' := hM.weaken k hk A'
    have hN' := hN.weaken (k + 1) (by simp; omega) A'
    -- reshape hN' : context (A :: Γ) inserted at k+1 = A :: (Γ inserted at k)
    have hctxN : insT (A :: Γ) (k + 1) A' = A :: insT Γ k A' := by
      unfold insT; rfl
    have hgrN : insG ((q1 * q_or_1 q2) :: γ₂) (k + 1)
        = (q1 * q_or_1 q2) :: insG γ₂ k := by
      unfold insG; rfl
    rw [hctxN, hgrN] at hN'
    refine HasCTy.letC hM' hN' ?_
    -- insG ((q_or_1 q2)•γ₁ + γ₂) k = (q_or_1 q2)•insG γ₁ k + insG γ₂ k
    have hlen1 : γ₁.length = Γ.length := hM.length_eq
    have hlen2 : γ₂.length = Γ.length := by
      have := hN.length_eq; simp only [List.length_cons] at this; omega
    apply insG_add_smul_aux <;> omega
  | @force γ Γ v φ B hv =>
    simp only [Comp.shiftFrom]
    exact HasCTy.force (hv.weaken k hk A')
  | @lam γ Γ M φ q A B hM =>
    simp only [Comp.shiftFrom]
    have hM' := hM.weaken (k + 1) (by simp; omega) A'
    have hctxM : insT (A :: Γ) (k + 1) A' = A :: insT Γ k A' := by unfold insT; rfl
    have hgrM : insG (q :: γ) (k + 1) = q :: insG γ k := by unfold insG; rfl
    rw [hctxM, hgrM] at hM'
    exact HasCTy.lam hM'
  | @app γ γ₁ γ₂ Γ M v φ q A B hM hv hγ =>
    subst hγ
    simp only [Comp.shiftFrom]
    have hM' := hM.weaken k hk A'
    have hv' := hv.weaken k hk A'
    refine HasCTy.app hM' hv' ?_
    have hlen1 : γ₁.length = Γ.length := hM.length_eq
    have hlen2 : γ₂.length = Γ.length := hv.length_eq
    apply insG_add_smul_aux' <;> omega
  | @case γ γ_v γ_N Γ v N₁ N₂ φ q A B C hv hN₁ hN₂ hγ =>
    subst hγ
    simp only [Comp.shiftFrom]
    have hv' := hv.weaken k hk A'
    have hN₁' := hN₁.weaken (k + 1) (by simp; omega) A'
    have hN₂' := hN₂.weaken (k + 1) (by simp; omega) A'
    -- reshape each branch: context (A/B :: Γ) inserted at k+1 = A/B :: (Γ inserted at k);
    -- grade (q :: γ_N) inserted at k+1 = q :: insG γ_N k.
    have hctxA : insT (A :: Γ) (k + 1) A' = A :: insT Γ k A' := by unfold insT; rfl
    have hctxB : insT (B :: Γ) (k + 1) A' = B :: insT Γ k A' := by unfold insT; rfl
    have hgr : insG (q :: γ_N) (k + 1) = q :: insG γ_N k := by unfold insG; rfl
    rw [hctxA, hgr] at hN₁'
    rw [hctxB, hgr] at hN₂'
    refine HasCTy.case hv' hN₁' hN₂' ?_
    -- insG (q • γ_v + γ_N) k = q • insG γ_v k + insG γ_N k  (smul on the LEFT summand)
    have hlen1 : γ_v.length = Γ.length := hv.length_eq
    have hlen2 : γ_N.length = Γ.length := by
      have := hN₁.length_eq; simp only [List.length_cons] at this; omega
    apply insG_add_smul_aux <;> omega
  | @split γ γ_v γ_N Γ v N φ q A B C hv hN hγ =>
    subst hγ
    simp only [Comp.shiftFrom]
    have hv' := hv.weaken k hk A'
    have hN' := hN.weaken (k + 2) (by simp; omega) A'
    -- N is under two binders (B :: A :: Γ); insert at k+2.
    have hctx : insT (B :: A :: Γ) (k + 2) A' = B :: A :: insT Γ k A' := by unfold insT; rfl
    have hgr : insG (q :: q :: γ_N) (k + 2) = q :: q :: insG γ_N k := by unfold insG; rfl
    rw [hctx, hgr] at hN'
    refine HasCTy.split hv' hN' ?_
    have hlen1 : γ_v.length = Γ.length := hv.length_eq
    have hlen2 : γ_N.length = Γ.length := by
      have := hN.length_eq; simp only [List.length_cons] at this; omega
    apply insG_add_smul_aux <;> omega
  | @unfold γ Γ v A hv =>
    simp only [Comp.shiftFrom]
    exact HasCTy.unfold (hv.weaken k hk A')
  | @perform γ_c γ_v Γ c ℓ op w φ q A B hcap hmem hopArg hopRes hw =>
    -- ADR-0054: shiftFrom k (perform c op w) = perform (shift c) op (shift w); grade
    -- insG ((q•γ_v) + γ_c) k = (q • insG γ_v k) + insG γ_c k (insG_add_smul_aux). Cap + arg both weaken.
    simp only [Comp.shiftFrom]
    have hl_v : γ_v.length = Γ.length := hw.length_eq
    have hl_c : γ_c.length = Γ.length := hcap.length_eq
    rw [show (q • γ_v) + γ_c = GradeVec.add (GradeVec.smul q γ_v) γ_c from rfl,
      insG_add_smul_aux q γ_v γ_c k (by omega)]
    exact HasCTy.perform (hcap.weaken k hk A') hmem hopArg hopRes (hw.weaken k hk A')
  -- ADR-0054: handle BINDS the cap (`cap ℓ :: Γ`, mult `qc`), so the body weakens at the SHIFTED
  -- cutoff `k+1`; `insT`/`insG` insert past the cap binder (`x :: insT Γ k A'`, `qc :: insG γ k`).
  | @handleThrows γ Γ ℓ M e φ q qc A hraise hiface hM hle hbocc =>
    simp only [Comp.shiftFrom, Handler.shiftFrom]
    have hM' := hM.weaken (k + 1) (by simp only [List.length_cons]; omega) A'
    have hctx : insT (VTy.cap ℓ :: Γ) (k + 1) A' = VTy.cap ℓ :: insT Γ k A' := by unfold insT; rfl
    have hgr2 : insG (qc :: γ) (k + 1) = qc :: insG γ k := by unfold insG; rfl
    rw [hctx, hgr2] at hM'
    exact HasCTy.handleThrows hraise hiface hM' hle hbocc
  | @handleState γ Γ ℓ s₀ M e φ q qc S A hga hgr hpa hpr hif hs hM hle hbocc =>
    -- state's stored value is CLOSED, so shift leaves it fixed (ADR-0025); body weakens at k+1.
    simp only [Comp.shiftFrom, Handler.shiftFrom]
    rw [hs.shift_closed k (Nat.zero_le k)]
    have hM' := hM.weaken (k + 1) (by simp only [List.length_cons]; omega) A'
    have hctx : insT (VTy.cap ℓ :: Γ) (k + 1) A' = VTy.cap ℓ :: insT Γ k A' := by unfold insT; rfl
    have hgr2 : insG (qc :: γ) (k + 1) = qc :: insG γ k := by unfold insG; rfl
    rw [hctx, hgr2] at hM'
    exact HasCTy.handleState hga hgr hpa hpr hif hs hM' hle hbocc
  | @handleTransaction γ Γ ℓ Θ₀ M e φ q qc A hna hnr hra hrr hwa hwr hif hcells hM hle hbocc =>
    -- `Handler.shiftFrom` leaves the heap untouched (closed cells, ADR-0030); body weakens at k+1.
    simp only [Comp.shiftFrom, Handler.shiftFrom]
    have hM' := hM.weaken (k + 1) (by simp only [List.length_cons]; omega) A'
    have hctx : insT (VTy.cap ℓ :: Γ) (k + 1) A' = VTy.cap ℓ :: insT Γ k A' := by unfold insT; rfl
    have hgr2 : insG (qc :: γ) (k + 1) = qc :: insG γ k := by unfold insG; rfl
    rw [hctx, hgr2] at hM'
    exact HasCTy.handleTransaction hna hnr hra hrr hwa hwr hif hcells hM' hle hbocc
end

/-- Grade at the substituted slot `k`, read off the derivation's grade vector. -/
private def slotGrade (γ_full : GradeVec Mult) (k : Nat) : Mult :=
  (γ_full[k]?).getD 0

/-! ### C.2 `eraseIdx` / `slotGrade` distribute over `+` and `•`

The structural cases of `subst_gen` (`ret`/`app`/`letC`) split the grade as
`s₁ • γ₁ + γ₂` etc.; these lemmas push `eraseIdx`/`slotGrade` through and then
re-associate the four-term `(γ₁'+s₁γ_v) + (γ₂'+s₂γ_v)` sum. -/

namespace GradeVec

variable {M : Type}

/-- `eraseIdx` commutes with `+` when lengths match. -/
theorem eraseIdx_add [Add M] (γ₁ γ₂ : GradeVec M) (k : Nat)
    (h : γ₁.length = γ₂.length) :
    (GradeVec.add γ₁ γ₂).eraseIdx k
      = GradeVec.add (γ₁.eraseIdx k) (γ₂.eraseIdx k) := by
  unfold GradeVec.add
  rw [List.eraseIdx_eq_take_drop_succ, List.eraseIdx_eq_take_drop_succ,
    List.eraseIdx_eq_take_drop_succ, List.take_zipWith, List.drop_zipWith,
    List.zipWith_append (by rw [List.length_take, List.length_take, h])]

/-- `eraseIdx` commutes with `•`. -/
theorem eraseIdx_smul [Mul M] (q : M) (γ : GradeVec M) (k : Nat) :
    (GradeVec.smul q γ).eraseIdx k = GradeVec.smul q (γ.eraseIdx k) := by
  unfold GradeVec.smul
  rw [List.eraseIdx_eq_take_drop_succ, List.eraseIdx_eq_take_drop_succ,
    List.map_append, List.map_take, List.map_drop]

end GradeVec

/-- `slotGrade (γ₁ + γ₂) k = slotGrade γ₁ k + slotGrade γ₂ k` when both vectors
have length `> k` (so neither index is out of range). -/
private theorem slotGrade_add (γ₁ γ₂ : GradeVec Mult) (k : Nat)
    (h1 : k < γ₁.length) (h2 : k < γ₂.length) :
    slotGrade (GradeVec.add γ₁ γ₂) k = slotGrade γ₁ k + slotGrade γ₂ k := by
  unfold slotGrade GradeVec.add
  rw [List.getElem?_zipWith]
  rcases ha : γ₁[k]? with _ | a
  · rw [List.getElem?_eq_none_iff] at ha; omega
  · rcases hb : γ₂[k]? with _ | b
    · rw [List.getElem?_eq_none_iff] at hb; omega
    · simp

private theorem slotGrade_smul (q : Mult) (γ : GradeVec Mult) (k : Nat) :
    slotGrade (GradeVec.smul q γ) k = q * slotGrade γ k := by
  unfold slotGrade GradeVec.smul
  rw [List.getElem?_map]
  rcases h : γ[k]? with _ | a
  · simp [mul_zero]
  · simp

/-- The substitution grade transform `S γ = eraseIdx k γ + slotGrade γ k • γ_v`,
abbreviated for the homomorphism lemmas below. -/
private def Sgrade (γ_v : GradeVec Mult) (k : Nat) (γ : GradeVec Mult) : GradeVec Mult :=
  GradeVec.add (γ.eraseIdx k) (GradeVec.smul (slotGrade γ k) γ_v)

/-- `S` length: `(Sgrade γ_v k γ).length = γ.length - 1` when `k < γ.length` and
`γ_v.length = γ.length - 1` (the value's grade matches the post-erase length). -/
private theorem Sgrade_length (γ_v : GradeVec Mult) (k : Nat) (γ : GradeVec Mult)
    (hk : k < γ.length) (hv : γ_v.length = γ.length - 1) :
    (Sgrade γ_v k γ).length = γ.length - 1 := by
  unfold Sgrade
  rw [GradeVec.add_length, List.length_eraseIdx, if_pos hk, GradeVec.smul_length, hv,
    Nat.min_self]

/-- `S` distributes over `+` (all vectors length-aligned, `> k`). -/
private theorem Sgrade_add (γ_v : GradeVec Mult) (k : Nat) (γ₁ γ₂ : GradeVec Mult)
    (h1 : k < γ₁.length) (h2 : k < γ₂.length) (hlen : γ₁.length = γ₂.length)
    (hv : γ_v.length = γ₁.length - 1) :
    Sgrade γ_v k (GradeVec.add γ₁ γ₂)
      = GradeVec.add (Sgrade γ_v k γ₁) (Sgrade γ_v k γ₂) := by
  unfold Sgrade
  apply List.ext_getElem?
  intro j
  rw [GradeVec.eraseIdx_add _ _ _ hlen, slotGrade_add _ _ _ h1 h2]
  -- compare pointwise; the 4-fold zipWith-add rearranges by AC + right-distrib
  simp only [GradeVec.add, GradeVec.smul, List.getElem?_zipWith, List.getElem?_map]
  rcases (γ₁.eraseIdx k)[j]? with _ | x <;> rcases (γ₂.eraseIdx k)[j]? with _ | y <;>
    rcases γ_v[j]? with _ | z <;>
    simp [add_comm, add_left_comm, add_assoc, add_mul]

/-- `S` distributes over `•`. -/
private theorem Sgrade_smul (γ_v : GradeVec Mult) (k : Nat) (q : Mult) (γ : GradeVec Mult) :
    Sgrade γ_v k (GradeVec.smul q γ) = GradeVec.smul q (Sgrade γ_v k γ) := by
  unfold Sgrade
  rw [GradeVec.eraseIdx_smul, slotGrade_smul, GradeVec.smul_add]
  congr 1
  -- q • (slotGrade γ k • γ_v) = (q * slotGrade γ k) • γ_v
  unfold GradeVec.smul
  rw [List.map_map]
  congr 1
  funext x
  simp [mul_assoc]

/-! ## D. Substitution

The single-variable substitution lemma, generalized to a level `k` via an
explicit prefix split `Δ` (so the cons-peeling under binders is structural).

Substituting `v` (typed `γ_v` over `Δ ++ Γ`, already prefix-valid) at de Bruijn
level `k = |Δ|` in `c` (typed `γ_full` over `Δ ++ A :: Γ`) yields `substFrom k v c`
typed `γ_full.eraseIdx k + (γ_full[k]) • γ_v` over `Δ ++ Γ`. At `k = 0`, `Δ = []`,
this collapses to the frozen `subst_value` statement. -/

/-! ### D.1 Helper lemmas for the leaf & binder cases of `subst_gen`. -/

/-- Descending under one binder: `Sgrade (0 :: γ_v) (k+1) (q :: γ) = q :: Sgrade γ_v k γ`.
This is exactly the grade reshape needed in the `lam`/`letC` cases (where `v`
becomes `shift v`, graded `0 :: γ_v`, and the level rises to `k+1`). -/
private theorem Sgrade_cons (γ_v : GradeVec Mult) (k : Nat) (q : Mult) (γ : GradeVec Mult) :
    Sgrade (0 :: γ_v) (k + 1) (q :: γ) = q :: Sgrade γ_v k γ := by
  unfold Sgrade
  have herase : (q :: γ).eraseIdx (k + 1) = q :: γ.eraseIdx k := by
    simp [List.eraseIdx_cons_succ]
  have hslot : slotGrade (q :: γ) (k + 1) = slotGrade γ k := by
    unfold slotGrade; simp
  rw [herase, hslot, GradeVec.smul_cons, GradeVec.add_cons, mul_zero, add_zero]

/-- The substitution motive for *values*: substituting at level `|Δ|`, with the
context decomposing as `Δ ++ A :: Γ`, preserves value typing with grade `S`. -/
private def VsubstMotive
    (γ₀ : GradeVec Mult) (Γ' : TyCtx Eff Mult) (w : Val) (A₀ : VTy Eff Mult)
    (_ : HasVTy γ₀ Γ' w A₀) : Prop :=
  ∀ (Δ Γ : TyCtx Eff Mult) (A : VTy Eff Mult) (γ_v : GradeVec Mult) (v : Val),
    Γ' = Δ ++ A :: Γ → HasVTy γ_v (Δ ++ Γ) v A →
    HasVTy (Sgrade γ_v Δ.length γ₀) (Δ ++ Γ) (Val.substFrom Δ.length v w) A₀

/-- The substitution motive for *computations*. -/
private def CsubstMotive
    (γ₀ : GradeVec Mult) (Γ' : TyCtx Eff Mult) (c : Comp) (e : Eff) (B : CTy Eff Mult)
    (_ : HasCTy γ₀ Γ' c e B) : Prop :=
  ∀ (Δ Γ : TyCtx Eff Mult) (A : VTy Eff Mult) (γ_v : GradeVec Mult) (v : Val),
    Γ' = Δ ++ A :: Γ → HasVTy γ_v (Δ ++ Γ) v A →
    HasCTy (Sgrade γ_v Δ.length γ₀) (Δ ++ Γ) (Comp.substFrom Δ.length v c) e B

/-- `slotGrade` of a zeros vector is `0` (in range). -/
private theorem slotGrade_zeros (n k : Nat) (hk : k < n) :
    slotGrade (GradeVec.zeros n : GradeVec Mult) k = 0 := by
  unfold slotGrade
  rw [GradeVec.zeros_getElem _ _ hk]; rfl

/-- For a `vunit`/`vint` leaf: the original grade is `zeros |Γ'|`; after `Sgrade`
the result grade is again a zeros vector of the post-erase length `|Δ++Γ|`. So any
0-graded constructor over `Δ ++ Γ` discharges the goal. `mkLeaf` is the typing of
the substituted term (which is unchanged: subst of unit/int is itself). -/
private theorem subst_leaf_zeros
    (Δ Γ : TyCtx Eff Mult) (A : VTy Eff Mult) (γ_v : GradeVec Mult) (v : Val)
    (hv : HasVTy γ_v (Δ ++ Γ) v A)
    (w' : Val) (A₀ : VTy Eff Mult)
    (mkLeaf : HasVTy (GradeVec.zeros (Δ ++ Γ).length) (Δ ++ Γ) w' A₀) :
    HasVTy (Sgrade γ_v Δ.length (GradeVec.zeros (Δ ++ A :: Γ).length)) (Δ ++ Γ) w' A₀ := by
  have hlen_v : γ_v.length = (Δ ++ Γ).length := hv.length_eq
  have hk : Δ.length < (Δ ++ A :: Γ).length := by
    rw [List.length_append, List.length_cons]; omega
  have hSg : Sgrade γ_v Δ.length (GradeVec.zeros (Δ ++ A :: Γ).length)
      = GradeVec.zeros (Δ ++ Γ).length := by
    unfold Sgrade
    rw [slotGrade_zeros _ _ hk]
    rw [GradeVec.zeros_eraseIdx _ _ hk]
    have : (Δ ++ A :: Γ).length - 1 = (Δ ++ Γ).length := by
      rw [List.length_append, List.length_append, List.length_cons]; omega
    rw [this]
    -- smul 0 γ_v = zeros |γ_v| = zeros |Δ++Γ|, then zeros + zeros = zeros
    have hlen_v : γ_v.length = (Δ ++ Γ).length := hv.length_eq
    have hsm : GradeVec.smul (0 : Mult) γ_v = GradeVec.zeros (Δ ++ Γ).length := by
      apply List.ext_getElem?
      intro j
      rw [GradeVec.smul, List.getElem?_map, GradeVec.zeros_get]
      rcases hj : γ_v[j]? with _ | a
      · simp only [Option.map_none]
        rw [List.getElem?_eq_none_iff] at hj
        rw [if_neg (by omega)]
      · simp only [Option.map_some]
        have hjlt : j < γ_v.length := by
          rw [List.getElem?_eq_some_iff] at hj; exact hj.1
        rw [if_pos (by omega), zero_mul]
    rw [hsm]
    -- add (zeros L) (zeros L) = zeros L
    apply List.ext_getElem?
    intro j
    simp only [GradeVec.add, List.getElem?_zipWith, GradeVec.zeros_get]
    split_ifs <;> simp [add_zero]
  rw [hSg]
  exact mkLeaf

/-- `vvar` case: `substFrom k v (vvar i)` is `v` at `i=k`, `vvar i` at `i<k`,
`vvar (i-1)` at `i>k`. The grade `Sgrade γ_v k (basis n i)` matches each. -/
private theorem subst_vvar_case
    (Δ Γ : TyCtx Eff Mult) (A : VTy Eff Mult) (γ_v : GradeVec Mult) (v : Val)
    (hv : HasVTy γ_v (Δ ++ Γ) v A)
    (i : Nat) (A₀ : VTy Eff Mult) (hget : (Δ ++ A :: Γ)[i]? = some A₀) :
    HasVTy (Sgrade γ_v Δ.length (GradeVec.basis (Δ ++ A :: Γ).length i))
           (Δ ++ Γ) (Val.substFrom Δ.length v (Val.vvar i)) A₀ := by
  set k := Δ.length with hk_def
  have hn : (Δ ++ A :: Γ).length = (Δ ++ Γ).length + 1 := by
    simp only [List.length_append, List.length_cons]; omega
  have hkn : k < (Δ ++ A :: Γ).length := by
    simp only [List.length_append, List.length_cons]; omega
  have hlen_v : γ_v.length = (Δ ++ Γ).length := hv.length_eq
  -- `0 • γ_v = zeros |Δ++Γ|` helper
  have h0smul : GradeVec.smul (0 : Mult) γ_v = GradeVec.zeros (Δ ++ Γ).length := by
    apply List.ext_getElem?
    intro j
    rw [GradeVec.smul, List.getElem?_map, GradeVec.zeros_get]
    rcases hj : γ_v[j]? with _ | a
    · simp only [Option.map_none]; rw [List.getElem?_eq_none_iff] at hj; rw [if_neg (by omega)]
    · simp only [Option.map_some]
      have : j < γ_v.length := by rw [List.getElem?_eq_some_iff] at hj; exact hj.1
      rw [if_pos (by omega), zero_mul]
  rw [Val.substFrom]
  rcases Nat.lt_trichotomy i k with hlt | heq | hgt
  · -- i < k : var stays `vvar i`, grade = basis (|Δ++Γ|) i
    rw [if_neg (by omega), if_neg (by omega)]
    have hslot : slotGrade (GradeVec.basis (Δ ++ A :: Γ).length i : GradeVec Mult) k = 0 := by
      unfold slotGrade; rw [GradeVec.basis_get, if_pos hkn, if_neg (by omega : k ≠ i)]; rfl
    have hSg : Sgrade γ_v k (GradeVec.basis (Δ ++ A :: Γ).length i)
        = GradeVec.basis (Δ ++ Γ).length i := by
      unfold Sgrade
      rw [hslot, h0smul, GradeVec.basis_eraseIdx _ _ _ hkn (by omega), hn, if_pos hlt]
      simp only [Nat.add_sub_cancel]
      -- basis L i + zeros L = basis L i
      apply List.ext_getElem?
      intro j
      simp only [GradeVec.add, List.getElem?_zipWith, GradeVec.basis_get, GradeVec.zeros_get]
      split_ifs <;> simp [add_zero]
    rw [hSg]
    refine HasVTy.vvar ?_
    -- (Δ++Γ)[i]? = some A₀ from hget, since i < |Δ|
    rw [List.getElem?_append_left (by omega)] at hget ⊢
    exact hget
  · -- i = k : the substituted slot, term = v, grade = γ_v
    subst heq
    rw [if_pos rfl]
    -- A₀ = A
    have hAA : A₀ = A := by
      rw [List.getElem?_append_right (by omega), Nat.sub_self] at hget
      simp at hget; exact hget.symm
    subst hAA
    have hslot : slotGrade (GradeVec.basis (Δ ++ A₀ :: Γ).length k : GradeVec Mult) k = 1 := by
      unfold slotGrade; rw [GradeVec.basis_get, if_pos hkn]; simp
    have hSg : Sgrade γ_v k (GradeVec.basis (Δ ++ A₀ :: Γ).length k) = γ_v := by
      unfold Sgrade
      rw [hslot]
      -- eraseIdx k (basis n k) = zeros (n-1) ; 1 • γ_v = γ_v
      have herase : (GradeVec.basis (Δ ++ A₀ :: Γ).length k : GradeVec Mult).eraseIdx k
          = GradeVec.zeros (Δ ++ Γ).length := by
        apply List.ext_getElem?
        intro j
        rw [List.getElem?_eraseIdx, GradeVec.zeros_get]
        by_cases hji : j < k <;>
          simp only [hji, if_true, if_false, GradeVec.basis_get]
        · split_ifs <;> first | rfl | (exfalso; omega)
        · split_ifs <;> first | rfl | (exfalso; omega)
      have h1smul : GradeVec.smul (1 : Mult) γ_v = γ_v := by
        rw [GradeVec.smul]; simp
      rw [herase, h1smul]
      -- zeros |Δ++Γ| + γ_v = γ_v
      rw [show (Δ ++ Γ).length = γ_v.length from hlen_v.symm]
      exact GradeVec.zeros_add γ_v
    rw [hSg]; exact hv
  · -- i > k : var renumbers to `vvar (i-1)`, grade = basis (|Δ++Γ|) (i-1)
    rw [if_neg (by omega), if_pos hgt]
    have hslot : slotGrade (GradeVec.basis (Δ ++ A :: Γ).length i : GradeVec Mult) k = 0 := by
      unfold slotGrade; rw [GradeVec.basis_get, if_pos hkn, if_neg (by omega : k ≠ i)]; rfl
    have hSg : Sgrade γ_v k (GradeVec.basis (Δ ++ A :: Γ).length i)
        = GradeVec.basis (Δ ++ Γ).length (i - 1) := by
      unfold Sgrade
      rw [hslot, h0smul, GradeVec.basis_eraseIdx _ _ _ hkn (by omega), hn, if_neg (by omega)]
      simp only [Nat.add_sub_cancel]
      apply List.ext_getElem?
      intro j
      simp only [GradeVec.add, List.getElem?_zipWith, GradeVec.basis_get, GradeVec.zeros_get]
      split_ifs <;> simp [add_zero]
    rw [hSg]
    refine HasVTy.vvar ?_
    -- (Δ++Γ)[i-1]? = some A₀ from hget at index i (i > |Δ|)
    rw [List.getElem?_append_right (by omega)] at hget
    rw [List.getElem?_append_right (by omega)]
    -- hget : (A::Γ)[i - |Δ|]? = some A₀ ; goal : Γ[i-1 - |Δ|]? = some A₀
    have hidx : i - Δ.length = (i - 1 - Δ.length) + 1 := by omega
    rw [hidx, List.getElem?_cons_succ] at hget
    exact hget

/-- `letC` case. -/
private theorem subst_letC_case
    (Δ Γ : TyCtx Eff Mult) (A : VTy Eff Mult) (γ_v : GradeVec Mult) (v : Val)
    (hv : HasVTy γ_v (Δ ++ Γ) v A)
    {γ₁ γ₂ : GradeVec Mult} {M N : Comp} {φ₁ φ₂ q1 q2 : _} {A₀ : VTy Eff Mult}
    {B : CTy Eff Mult}
    (hM : HasCTy γ₁ (Δ ++ A :: Γ) M φ₁ (CTy.F q1 A₀))
    (hN : HasCTy ((q1 * q_or_1 q2) :: γ₂) (A₀ :: Δ ++ A :: Γ) N φ₂ B)
    (ihM : CsubstMotive γ₁ (Δ ++ A :: Γ) M φ₁ (CTy.F q1 A₀) hM)
    (ihN : CsubstMotive ((q1 * q_or_1 q2) :: γ₂) (A₀ :: Δ ++ A :: Γ) N φ₂ B hN) :
    HasCTy (Sgrade γ_v Δ.length ((q_or_1 q2) • γ₁ + γ₂)) (Δ ++ Γ)
           (Comp.substFrom Δ.length v (Comp.letC M N)) (φ₁ ⊔ φ₂) B := by
  have hl1 : γ₁.length = (Δ ++ A :: Γ).length := hM.length_eq
  have hl2 : γ₂.length = (Δ ++ A :: Γ).length := by
    have h := hN.length_eq
    simp only [List.length_cons, List.length_append] at h ⊢; omega
  have hk : Δ.length < (Δ ++ A :: Γ).length := by
    rw [List.length_append, List.length_cons]; omega
  have hvl : γ_v.length = (Δ ++ A :: Γ).length - 1 := by
    rw [hv.length_eq, List.length_append, List.length_append, List.length_cons]; omega
  rw [Comp.substFrom]
  -- grade reshape
  show HasCTy (Sgrade γ_v Δ.length
      (GradeVec.add (GradeVec.smul (q_or_1 q2) γ₁) γ₂)) _ _ _ _
  rw [Sgrade_add γ_v Δ.length (GradeVec.smul (q_or_1 q2) γ₁) γ₂
        (by rw [GradeVec.smul_length]; omega) (by omega)
        (by rw [GradeVec.smul_length, hl1, hl2]) (by rw [GradeVec.smul_length]; omega),
      Sgrade_smul]
  -- M branch
  have hihM := ihM Δ Γ A γ_v v rfl hv
  -- N branch: descend under binder A₀
  have hk0 : (0 : Nat) ≤ (Δ ++ Γ).length := Nat.zero_le _
  have hvw := hv.weaken 0 hk0 A₀
  have hctx : insT (Δ ++ Γ) 0 A₀ = (A₀ :: Δ) ++ Γ := by unfold insT; simp
  have hgr : insG γ_v 0 = (0 : Mult) :: γ_v := by unfold insG; simp
  rw [hctx, hgr] at hvw
  have hΓeq : A₀ :: Δ ++ A :: Γ = (A₀ :: Δ) ++ A :: Γ := by simp
  have hihN := ihN (A₀ :: Δ) Γ A ((0 : Mult) :: γ_v) (Val.shiftFrom 0 v) hΓeq hvw
  rw [List.length_cons, Sgrade_cons] at hihN
  have hctx2 : (A₀ :: Δ) ++ Γ = A₀ :: (Δ ++ Γ) := by simp
  rw [hctx2] at hihN
  exact HasCTy.letC hihM hihN rfl

/-- `lam` case. -/
private theorem subst_lam_case
    (Δ Γ : TyCtx Eff Mult) (A : VTy Eff Mult) (γ_v : GradeVec Mult) (v : Val)
    (hv : HasVTy γ_v (Δ ++ Γ) v A)
    {γ : GradeVec Mult} {M : Comp} {φ q : _} {A₀ : VTy Eff Mult} {B : CTy Eff Mult}
    (hM : HasCTy (q :: γ) (A₀ :: Δ ++ A :: Γ) M φ B)
    (ih : CsubstMotive (q :: γ) (A₀ :: Δ ++ A :: Γ) M φ B hM) :
    HasCTy (Sgrade γ_v Δ.length γ) (Δ ++ Γ)
           (Comp.substFrom Δ.length v (Comp.lam M)) φ (CTy.arr q A₀ B) := by
  rw [Comp.substFrom]
  -- weaken v under the fresh binder A₀ (insert at position 0)
  have hk0 : (0 : Nat) ≤ (Δ ++ Γ).length := Nat.zero_le _
  have hvw := hv.weaken 0 hk0 A₀
  -- insG γ_v 0 = 0 :: γ_v ; insT (Δ++Γ) 0 A₀ = A₀ :: (Δ++Γ) ; shiftFrom 0 = shift
  have hctx : insT (Δ ++ Γ) 0 A₀ = (A₀ :: Δ) ++ Γ := by unfold insT; simp
  have hgr : insG γ_v 0 = (0 : Mult) :: γ_v := by unfold insG; simp
  rw [hctx, hgr] at hvw
  -- apply the IH with prefix Δ' = A₀ :: Δ
  have hΓeq : A₀ :: Δ ++ A :: Γ = (A₀ :: Δ) ++ A :: Γ := by simp
  have hih := ih (A₀ :: Δ) Γ A ((0 : Mult) :: γ_v) (Val.shiftFrom 0 v) hΓeq hvw
  -- reshape: |A₀::Δ| = Δ.length+1 ; Sgrade (0::γ_v) (k+1) (q::γ) = q :: Sgrade γ_v k γ
  rw [List.length_cons] at hih
  rw [Sgrade_cons] at hih
  -- hih : HasCTy (q :: Sgrade γ_v Δ.length γ) ((A₀::Δ)++Γ) (substFrom (Δ.length+1) (shift v) M) φ B
  -- context (A₀::Δ)++Γ = A₀ :: (Δ++Γ); shift v = shiftFrom 0 v ; substFrom uses Δ.length+1
  have hctx2 : (A₀ :: Δ) ++ Γ = A₀ :: (Δ ++ Γ) := by simp
  rw [hctx2] at hih
  exact HasCTy.lam hih

/-- ADR-0054 `handle*` body descent: `handle` BINDS the capability (`Cap ℓ` at index 0, mult `qc`), so the
body `M` descends under a fresh binder EXACTLY like `lam` — only the binder TYPE differs (`VTy.cap ℓ`).
Shared by all three handle arms (the interface/grade premises thread verbatim; only the body needs the
binder-shift). Mirrors `subst_lam_case`. -/
private theorem subst_handle_body
    (Δ Γ : TyCtx Eff Mult) (A : VTy Eff Mult) (γ_v : GradeVec Mult) (v : Val)
    (hv : HasVTy γ_v (Δ ++ Γ) v A)
    {γ : GradeVec Mult} {ℓ : Label} {M : Comp} {e : Eff} {q qc : Mult} {A₀ : VTy Eff Mult}
    (hM : HasCTy (qc :: γ) (VTy.cap ℓ :: (Δ ++ A :: Γ)) M e (CTy.F q A₀))
    (ih : CsubstMotive (qc :: γ) (VTy.cap ℓ :: (Δ ++ A :: Γ)) M e (CTy.F q A₀) hM) :
    HasCTy (qc :: Sgrade γ_v Δ.length γ) (VTy.cap ℓ :: (Δ ++ Γ))
           (Comp.substFrom (Δ.length + 1) (Val.shift v) M) e (CTy.F q A₀) := by
  have hk0 : (0 : Nat) ≤ (Δ ++ Γ).length := Nat.zero_le _
  have hvw := hv.weaken 0 hk0 (VTy.cap ℓ)
  have hctx : insT (Δ ++ Γ) 0 (VTy.cap ℓ) = (VTy.cap ℓ :: Δ) ++ Γ := by unfold insT; simp
  have hgr : insG γ_v 0 = (0 : Mult) :: γ_v := by unfold insG; simp
  rw [hctx, hgr] at hvw
  have hΓeq : VTy.cap ℓ :: (Δ ++ A :: Γ) = (VTy.cap ℓ :: Δ) ++ A :: Γ := by simp
  have hih := ih (VTy.cap ℓ :: Δ) Γ A ((0 : Mult) :: γ_v) (Val.shiftFrom 0 v) hΓeq hvw
  rw [List.length_cons] at hih
  rw [Sgrade_cons] at hih
  have hctx2 : (VTy.cap ℓ :: Δ) ++ Γ = VTy.cap ℓ :: (Δ ++ Γ) := by simp
  rw [hctx2] at hih
  exact hih

/-- `app` case. -/
private theorem subst_app_case
    (Δ Γ : TyCtx Eff Mult) (A : VTy Eff Mult) (γ_v : GradeVec Mult) (v : Val)
    (hv : HasVTy γ_v (Δ ++ Γ) v A)
    {γ₁ γ₂ : GradeVec Mult} {M : Comp} {w : Val} {φ q : _} {A₀ : VTy Eff Mult}
    {B : CTy Eff Mult}
    (hM : HasCTy γ₁ (Δ ++ A :: Γ) M φ (CTy.arr q A₀ B))
    (hw : HasVTy γ₂ (Δ ++ A :: Γ) w A₀)
    (ihM : CsubstMotive γ₁ (Δ ++ A :: Γ) M φ (CTy.arr q A₀ B) hM)
    (ihV : VsubstMotive γ₂ (Δ ++ A :: Γ) w A₀ hw) :
    HasCTy (Sgrade γ_v Δ.length (γ₁ + q • γ₂)) (Δ ++ Γ)
           (Comp.substFrom Δ.length v (Comp.app M w)) φ B := by
  have hl1 : γ₁.length = (Δ ++ A :: Γ).length := hM.length_eq
  have hl2 : γ₂.length = (Δ ++ A :: Γ).length := hw.length_eq
  have hk : Δ.length < (Δ ++ A :: Γ).length := by
    rw [List.length_append, List.length_cons]; omega
  have hvl : γ_v.length = (Δ ++ A :: Γ).length - 1 := by
    rw [hv.length_eq, List.length_append, List.length_append, List.length_cons]; omega
  rw [Comp.substFrom]
  show HasCTy (Sgrade γ_v Δ.length (GradeVec.add γ₁ (GradeVec.smul q γ₂))) _ _ _ _
  rw [Sgrade_add γ_v Δ.length γ₁ (GradeVec.smul q γ₂)
        (by omega) (by rw [GradeVec.smul_length]; omega)
        (by rw [GradeVec.smul_length, hl1, hl2]) (by omega),
      Sgrade_smul]
  exact HasCTy.app (ihM Δ Γ A γ_v v rfl hv) (ihV Δ Γ A γ_v v rfl hv) rfl

/-- `case` case. Scrutinee `v : A₀ + B₀` graded `γ_s`, scaled by `q`; each branch
`Nᵢ` descends under ONE binder (`A₀`/`B₀`) sharing grade `γ_N`. Grade reshape:
`Sgrade k (q • γ_s + γ_N) = q • Sgrade k γ_s + Sgrade k γ_N` (Sgrade_add/smul),
with each branch's binder-descent via Sgrade_cons (mirrors `subst_letC_case`). -/
private theorem subst_case_case
    (Δ Γ : TyCtx Eff Mult) (A : VTy Eff Mult) (γ_v : GradeVec Mult) (v : Val)
    (hv : HasVTy γ_v (Δ ++ Γ) v A)
    {γ_s γ_N : GradeVec Mult} {s : Val} {N₁ N₂ : Comp} {φ q : _}
    {A₀ B₀ : VTy Eff Mult} {C : CTy Eff Mult}
    (hs : HasVTy γ_s (Δ ++ A :: Γ) s (VTy.sum A₀ B₀))
    (hN₁ : HasCTy (q :: γ_N) (A₀ :: Δ ++ A :: Γ) N₁ φ C)
    (hN₂ : HasCTy (q :: γ_N) (B₀ :: Δ ++ A :: Γ) N₂ φ C)
    (ihs : VsubstMotive γ_s (Δ ++ A :: Γ) s (VTy.sum A₀ B₀) hs)
    (ihN₁ : CsubstMotive (q :: γ_N) (A₀ :: Δ ++ A :: Γ) N₁ φ C hN₁)
    (ihN₂ : CsubstMotive (q :: γ_N) (B₀ :: Δ ++ A :: Γ) N₂ φ C hN₂) :
    HasCTy (Sgrade γ_v Δ.length (q • γ_s + γ_N)) (Δ ++ Γ)
           (Comp.substFrom Δ.length v (Comp.case s N₁ N₂)) φ C := by
  have hk : Δ.length < (Δ ++ A :: Γ).length := by
    rw [List.length_append, List.length_cons]; omega
  have hl1 : γ_s.length = (Δ ++ A :: Γ).length := hs.length_eq
  have hl2 : γ_N.length = (Δ ++ A :: Γ).length := by
    have h := hN₁.length_eq
    simp only [List.length_cons, List.length_append] at h ⊢; omega
  have hvl : γ_v.length = (Δ ++ A :: Γ).length - 1 := by
    rw [hv.length_eq, List.length_append, List.length_append, List.length_cons]; omega
  rw [Comp.substFrom]
  -- grade reshape: q • γ_s + γ_N
  show HasCTy (Sgrade γ_v Δ.length
      (GradeVec.add (GradeVec.smul q γ_s) γ_N)) _ _ _ _
  rw [Sgrade_add γ_v Δ.length (GradeVec.smul q γ_s) γ_N
        (by rw [GradeVec.smul_length]; omega) (by omega)
        (by rw [GradeVec.smul_length, hl1, hl2]) (by rw [GradeVec.smul_length]; omega),
      Sgrade_smul]
  -- scrutinee branch
  have hihs := ihs Δ Γ A γ_v v rfl hv
  -- weaken `v` under a fresh binder (shared shape for both branches)
  have hk0 : (0 : Nat) ≤ (Δ ++ Γ).length := Nat.zero_le _
  have hgr : insG γ_v 0 = (0 : Mult) :: γ_v := by unfold insG; simp
  have hctx2 : ∀ (D : VTy Eff Mult), (D :: Δ) ++ Γ = D :: (Δ ++ Γ) := by intro D; simp
  -- N₁ branch: descend under A₀
  have hvwA := hv.weaken 0 hk0 A₀
  have hctxA : insT (Δ ++ Γ) 0 A₀ = (A₀ :: Δ) ++ Γ := by unfold insT; simp
  rw [hctxA, hgr] at hvwA
  have hΓeqA : A₀ :: Δ ++ A :: Γ = (A₀ :: Δ) ++ A :: Γ := by simp
  have hihN₁ := ihN₁ (A₀ :: Δ) Γ A ((0 : Mult) :: γ_v) (Val.shiftFrom 0 v) hΓeqA hvwA
  rw [List.length_cons, Sgrade_cons, hctx2] at hihN₁
  -- N₂ branch: descend under B₀
  have hvwB := hv.weaken 0 hk0 B₀
  have hctxB : insT (Δ ++ Γ) 0 B₀ = (B₀ :: Δ) ++ Γ := by unfold insT; simp
  rw [hctxB, hgr] at hvwB
  have hΓeqB : B₀ :: Δ ++ A :: Γ = (B₀ :: Δ) ++ A :: Γ := by simp
  have hihN₂ := ihN₂ (B₀ :: Δ) Γ A ((0 : Mult) :: γ_v) (Val.shiftFrom 0 v) hΓeqB hvwB
  rw [List.length_cons, Sgrade_cons, hctx2] at hihN₂
  exact HasCTy.case hihs hihN₁ hihN₂ rfl

/-- `split` case. Like `case`, but `N` descends under TWO binders (`B₀` then `A₀`,
matching the typing rule's `B₀ :: A₀ :: Γ` and `substFrom (k+2)`); Sgrade_cons is
applied twice. Grade `q • γ_s + γ_N` as in `case`. -/
private theorem subst_split_case
    (Δ Γ : TyCtx Eff Mult) (A : VTy Eff Mult) (γ_v : GradeVec Mult) (v : Val)
    (hv : HasVTy γ_v (Δ ++ Γ) v A)
    {γ_s γ_N : GradeVec Mult} {s : Val} {N : Comp} {φ q : _}
    {A₀ B₀ : VTy Eff Mult} {C : CTy Eff Mult}
    (hs : HasVTy γ_s (Δ ++ A :: Γ) s (VTy.prod A₀ B₀))
    (hN : HasCTy (q :: q :: γ_N) (B₀ :: A₀ :: Δ ++ A :: Γ) N φ C)
    (ihs : VsubstMotive γ_s (Δ ++ A :: Γ) s (VTy.prod A₀ B₀) hs)
    (ihN : CsubstMotive (q :: q :: γ_N) (B₀ :: A₀ :: Δ ++ A :: Γ) N φ C hN) :
    HasCTy (Sgrade γ_v Δ.length (q • γ_s + γ_N)) (Δ ++ Γ)
           (Comp.substFrom Δ.length v (Comp.split s N)) φ C := by
  have hk : Δ.length < (Δ ++ A :: Γ).length := by
    rw [List.length_append, List.length_cons]; omega
  have hl1 : γ_s.length = (Δ ++ A :: Γ).length := hs.length_eq
  have hl2 : γ_N.length = (Δ ++ A :: Γ).length := by
    have h := hN.length_eq
    simp only [List.length_cons, List.length_append] at h ⊢; omega
  have hvl : γ_v.length = (Δ ++ A :: Γ).length - 1 := by
    rw [hv.length_eq, List.length_append, List.length_append, List.length_cons]; omega
  rw [Comp.substFrom]
  show HasCTy (Sgrade γ_v Δ.length
      (GradeVec.add (GradeVec.smul q γ_s) γ_N)) _ _ _ _
  rw [Sgrade_add γ_v Δ.length (GradeVec.smul q γ_s) γ_N
        (by rw [GradeVec.smul_length]; omega) (by omega)
        (by rw [GradeVec.smul_length, hl1, hl2]) (by rw [GradeVec.smul_length]; omega),
      Sgrade_smul]
  have hihs := ihs Δ Γ A γ_v v rfl hv
  -- N descends under TWO binders A₀ (inner, position 1) then B₀ (outer, position 0).
  -- Weaken v under A₀ first, then under B₀ on top, mirroring substFrom (k+2)(shift (shift v)).
  have hk0 : (0 : Nat) ≤ (Δ ++ Γ).length := Nat.zero_le _
  have hgr : insG γ_v 0 = (0 : Mult) :: γ_v := by unfold insG; simp
  -- first descent: under A₀
  have hvwA := hv.weaken 0 hk0 A₀
  have hctxA : insT (Δ ++ Γ) 0 A₀ = (A₀ :: Δ) ++ Γ := by unfold insT; simp
  rw [hctxA, hgr] at hvwA
  -- hvwA : HasVTy (0 :: γ_v) ((A₀ :: Δ) ++ Γ) (shiftFrom 0 v) A
  -- second descent: under B₀ on top of A₀
  have hk0' : (0 : Nat) ≤ ((A₀ :: Δ) ++ Γ).length := Nat.zero_le _
  have hvwB := hvwA.weaken 0 hk0' B₀
  have hctxB : insT ((A₀ :: Δ) ++ Γ) 0 B₀ = (B₀ :: A₀ :: Δ) ++ Γ := by unfold insT; simp
  have hgr' : insG ((0 : Mult) :: γ_v) 0 = (0 : Mult) :: (0 : Mult) :: γ_v := by unfold insG; simp
  rw [hctxB, hgr'] at hvwB
  -- shiftFrom 0 (shiftFrom 0 v) = shift (shift v)
  have hΓeq : B₀ :: A₀ :: Δ ++ A :: Γ = (B₀ :: A₀ :: Δ) ++ A :: Γ := by simp
  have hihN := ihN (B₀ :: A₀ :: Δ) Γ A ((0 : Mult) :: (0 : Mult) :: γ_v)
    (Val.shiftFrom 0 (Val.shiftFrom 0 v)) hΓeq hvwB
  -- reshape: |B₀::A₀::Δ| = Δ.length+2 ; Sgrade twice via Sgrade_cons
  rw [List.length_cons, List.length_cons] at hihN
  rw [show Δ.length + 1 + 1 = (Δ.length + 1) + 1 from rfl, Sgrade_cons, Sgrade_cons] at hihN
  have hctx2 : (B₀ :: A₀ :: Δ) ++ Γ = B₀ :: A₀ :: (Δ ++ Γ) := by simp
  rw [hctx2] at hihN
  exact HasCTy.split hihs hihN rfl

set_option maxHeartbeats 1600000 in
theorem HasCTy.subst_gen
    {A : VTy Eff Mult} {Γ : TyCtx Eff Mult}
    {γ_full : GradeVec Mult} {c : Comp} {e : Eff} {B : CTy Eff Mult}
    (Δ : TyCtx Eff Mult)
    {γ_v : GradeVec Mult} {v : Val}
    (hv : HasVTy γ_v (Δ ++ Γ) v A)
    (hc : HasCTy γ_full (Δ ++ A :: Γ) c e B) :
    HasCTy (Sgrade γ_v Δ.length γ_full)
           (Δ ++ Γ) (Comp.substFrom Δ.length v c) e B := by
  refine HasCTy.rec
    (motive_1 := VsubstMotive) (motive_2 := CsubstMotive)
    ?vunit ?vint ?vvar ?vcap ?vthunk ?inl ?inr ?pair ?fold
    ?ret ?letC ?force ?lam ?app ?case ?split ?unfold ?perform ?handleThrows ?handleState
    ?handleTransaction
    hc Δ Γ A γ_v v rfl hv
  case vunit =>
    intro Γ₀ Δ Γ A γ_v v hΓ hv
    subst hΓ
    rw [show Val.substFrom Δ.length v Val.vunit = Val.vunit from by rw [Val.substFrom]]
    exact subst_leaf_zeros Δ Γ A γ_v v hv Val.vunit VTy.unit HasVTy.vunit
  case vint =>
    intro Γ₀ n Δ Γ A γ_v v hΓ hv
    subst hΓ
    rw [show Val.substFrom Δ.length v (Val.vint n) = Val.vint n from by rw [Val.substFrom]]
    exact subst_leaf_zeros Δ Γ A γ_v v hv (Val.vint n) VTy.int HasVTy.vint
  case vvar =>
    intro Γ₀ i A₀ hget Δ Γ A γ_v v hΓ hv
    subst hΓ
    exact subst_vvar_case Δ Γ A γ_v v hv i A₀ hget
  case vcap =>
    -- ADR-0054: a capability is inert (grade `zeros`) and closed (subst = id), like `vunit`/`vint`.
    intro Γ₀ n ℓ Δ Γ A γ_v v hΓ hv
    subst hΓ
    rw [show Val.substFrom Δ.length v (Val.vcap n ℓ) = Val.vcap n ℓ from by rw [Val.substFrom]]
    exact subst_leaf_zeros Δ Γ A γ_v v hv (Val.vcap n ℓ) (VTy.cap ℓ) HasVTy.vcap
  case vthunk =>
    intro γ Γ₀ M φ B hM ih Δ Γ A γ_v v hΓ hv
    subst hΓ
    have := ih Δ Γ A γ_v v rfl hv
    rw [Val.substFrom]
    exact HasVTy.vthunk this
  case inl =>
    intro γ Γ₀ w A₀ B₀ hw ih Δ Γ A γ_v v hΓ hv
    subst hΓ
    rw [Val.substFrom]
    exact HasVTy.inl (ih Δ Γ A γ_v v rfl hv)
  case inr =>
    intro γ Γ₀ w A₀ B₀ hw ih Δ Γ A γ_v v hΓ hv
    subst hΓ
    rw [Val.substFrom]
    exact HasVTy.inr (ih Δ Γ A γ_v v rfl hv)
  case pair =>
    intro γ γ_a γ_b Γ₀ w₁ w₂ A₀ B₀ hw₁ hw₂ hγ ih₁ ih₂ Δ Γ A γ_v v hΓ hv
    subst hΓ; subst hγ
    rw [Val.substFrom]
    -- Sgrade γ_v k (γ_a + γ_b) = Sgrade γ_v k γ_a + Sgrade γ_v k γ_b (Sgrade_add).
    have hk : Δ.length < (Δ ++ A :: Γ).length := by
      rw [List.length_append, List.length_cons]; omega
    have hl1 : γ_a.length = (Δ ++ A :: Γ).length := hw₁.length_eq
    have hl2 : γ_b.length = (Δ ++ A :: Γ).length := hw₂.length_eq
    have hvl : γ_v.length = (Δ ++ A :: Γ).length - 1 := by
      rw [hv.length_eq, List.length_append, List.length_append, List.length_cons]; omega
    rw [show γ_a + γ_b = GradeVec.add γ_a γ_b from rfl,
      Sgrade_add γ_v Δ.length γ_a γ_b (by omega) (by omega) (by omega) (by omega)]
    exact HasVTy.pair (ih₁ Δ Γ A γ_v v rfl hv) (ih₂ Δ Γ A γ_v v rfl hv) rfl
  case fold =>
    intro γ Γ₀ w A₀ hw ih Δ Γ A γ_v v hΓ hv
    subst hΓ
    rw [Val.substFrom]
    exact HasVTy.fold (ih Δ Γ A γ_v v rfl hv)
  case ret =>
    intro γ γ' Γ₀ w A₀ q hw hγ ih Δ Γ A γ_v v hΓ hv
    subst hΓ; subst hγ
    rw [Comp.substFrom]
    simp only [hsmul_eq_smul, Sgrade_smul]
    exact HasCTy.ret (ih Δ Γ A γ_v v rfl hv) rfl
  case letC =>
    intro γ γ₁ γ₂ Γ₀ M N φ₁ φ₂ q1 q2 A₀ B hM hN hγ ihM ihN Δ Γ A γ_v v hΓ hv
    subst hΓ; subst hγ
    exact subst_letC_case Δ Γ A γ_v v hv hM hN ihM ihN
  case force =>
    intro γ Γ₀ w φ B hw ih Δ Γ A γ_v v hΓ hv
    subst hΓ
    rw [Comp.substFrom]
    exact HasCTy.force (ih Δ Γ A γ_v v rfl hv)
  case lam =>
    intro γ Γ₀ M φ q A₀ B hM ih Δ Γ A γ_v v hΓ hv
    subst hΓ
    exact subst_lam_case Δ Γ A γ_v v hv hM ih
  case app =>
    intro γ γ₁ γ₂ Γ₀ M w φ q A₀ B hM hw hγ ihM ihV Δ Γ A γ_v v hΓ hv
    subst hΓ; subst hγ
    exact subst_app_case Δ Γ A γ_v v hv hM hw ihM ihV
  case case =>
    intro γ γ_s γ_N Γ₀ s N₁ N₂ φ q A₀ B₀ C hs hN₁ hN₂ hγ ihs ihN₁ ihN₂ Δ Γ A γ_v v hΓ hv
    subst hΓ; subst hγ
    exact subst_case_case Δ Γ A γ_v v hv hs hN₁ hN₂ ihs ihN₁ ihN₂
  case split =>
    intro γ γ_s γ_N Γ₀ s N φ q A₀ B₀ C hs hN hγ ihs ihN Δ Γ A γ_v v hΓ hv
    subst hΓ; subst hγ
    exact subst_split_case Δ Γ A γ_v v hv hs hN ihs ihN
  case unfold =>
    intro γ Γ₀ s A₀ hs ih Δ Γ A γ_v v hΓ hv
    subst hΓ
    rw [Comp.substFrom]
    exact HasCTy.unfold (ih Δ Γ A γ_v v rfl hv)
  case perform =>
    -- ADR-0054: perform now carries the cap derivation (grade γ_cp) alongside the arg (γ_a); the
    -- substituted grade `Sgrade k ((q•γ_a) + γ_cp)` reshapes via `Sgrade_add` + `Sgrade_smul` (the
    -- `pair`-case combinator over the `ret`-case scalar). Both sub-derivations re-type at the filler `v`.
    intro γ_cp γ_a Γ₀ cp ℓ op w φ q A₀ B₀ hcap hmem hopArg hopRes hw ih_cap ih_w Δ Γ A γ_v v hΓ hv
    subst hΓ
    rw [Comp.substFrom]
    have hk : Δ.length < (Δ ++ A :: Γ).length := by rw [List.length_append, List.length_cons]; omega
    have hl_a : γ_a.length = (Δ ++ A :: Γ).length := hw.length_eq
    have hl_cp : γ_cp.length = (Δ ++ A :: Γ).length := hcap.length_eq
    have hvl : γ_v.length = (Δ ++ A :: Γ).length - 1 := by
      rw [hv.length_eq, List.length_append, List.length_append, List.length_cons]; omega
    rw [show (q • γ_a) + γ_cp = GradeVec.add (GradeVec.smul q γ_a) γ_cp from rfl,
      Sgrade_add γ_v Δ.length (GradeVec.smul q γ_a) γ_cp
        (by rw [GradeVec.smul_length]; omega) (by omega)
        (by rw [GradeVec.smul_length]; omega) (by rw [GradeVec.smul_length]; omega),
      Sgrade_smul]
    exact HasCTy.perform (ih_cap Δ Γ A γ_v v rfl hv) hmem hopArg hopRes (ih_w Δ Γ A γ_v v rfl hv)
  -- ADR-0053: `Comp.substFrom`'s `handle` arm fills the body with `v` UNCHANGED (absolute caps don't
  -- shift on handle-crossing). The body IH re-types it at the filler `v` directly — no `HasVTy.shiftCap`,
  -- no cap-shift. This is the STD-block simplification the absolute-cap representation buys.
  case handleThrows =>
    -- ADR-0054: handle BINDS the cap (`qc`); the body descends under it (subst_handle_body).
    intro γ Γ₀ ℓ M e φ q qc A₀ hraise hiface hM hle hbocc _ihM Δ Γ A γ_v v hΓ hv
    subst hΓ
    rw [Comp.substFrom, Handler.substFrom]
    exact HasCTy.handleThrows hraise hiface (subst_handle_body Δ Γ A γ_v v hv hM _ihM) hle hbocc
  case handleState =>
    intro γ Γ₀ ℓ s₀ M e φ q qc S A₀ hga hgr hpa hpr hif hs hM hle hbocc _ihs ihM Δ Γ A γ_v v hΓ hv
    subst hΓ
    rw [Comp.substFrom, Handler.substFrom]
    -- the stored state is CLOSED ⇒ substFrom leaves it fixed (ADR-0025); body descends under the cap.
    rw [hs.subst_closed Δ.length (Nat.zero_le _) _]
    exact HasCTy.handleState hga hgr hpa hpr hif hs
      (subst_handle_body Δ Γ A γ_v v hv hM ihM) hle hbocc
  case handleTransaction =>
    -- subst through a transaction handler. `Handler.substFrom` leaves the heap untouched (closed
    -- cells, ADR-0030), so only the body substitutes (under the cap binder); like `handleState`.
    intro γ Γ₀ ℓ Θ₀ M e φ q qc A₀ hna hnr hra hrr hwa hwr hif hcells hM hle hbocc _hcellsIH ihM
      Δ Γ A γ_v v hΓ hv
    subst hΓ
    rw [Comp.substFrom, Handler.substFrom]
    exact HasCTy.handleTransaction hna hnr hra hrr hwa hwr hif hcells
      (subst_handle_body Δ Γ A γ_v v hv hM ihM) hle hbocc

/-- The frozen `subst_value` statement, derived from `subst_gen` at `k = 0`.
At `Δ = []`: `eraseIdx 0 (ρ :: γ) = γ`, `slotGrade (ρ::γ) 0 = ρ`, and
`Comp.substFrom 0 = Comp.subst`. The grade `γ + ρ • γ_v` matches exactly. -/
theorem subst_value_proof
    (ρ : Mult) {γ γ_v : GradeVec Mult} {Γ : TyCtx Eff Mult}
    {v : Val} {A : VTy Eff Mult}
    {c : Comp} {e : Eff} {B : CTy Eff Mult} :
    HasVTy γ_v Γ v A →
    HasCTy (ρ :: γ) (A :: Γ) c e B →
    HasCTy (GradeVec.add γ (GradeVec.smul ρ γ_v)) Γ (Comp.subst v c) e B := by
  intro hv hc
  have h := HasCTy.subst_gen (γ_v := γ_v) (v := v) (A := A) [] hv hc
  simpa [Sgrade, slotGrade, List.eraseIdx, Comp.subst] using h

/-! ## E. The STD block: preservation, progress, type_safety (CK machine, ADR-0023)

Standard syntactic-soundness metatheory (Wright–Felleisen) over the de Bruijn graded
CBPV, now stated over the CK machine's `Config`. `subst_value_proof` (above) is the
substitution lemma; these three ride it. Statements frozen in `Bang/Spec.lean`. The
focus is always closed (substitution-based binding), so the stack threads only effects
+ computation types — `HasStack`/`HasConfig` (Syntax.lean §1.7). -/

/-! ### E.0 stack effect-weakening + the dispatch decomposition

Two structural lemmas the config-level preservation/progress need:
  - `HasStack.weaken_eff`: a focus typed at a SMALLER effect still plugs into the same
    stack (REDUCE-handleF/ret narrows the focus to `⊥`; DISPATCH narrows to `⊥`).
  - `HasStack.dispatch_typed`: when `dispatch` finds the handling `throws ℓ` frame, the
    outer stack `Kₒ` types the aborted `ret v` and the whole-program effect shrinks. -/

/-! ### E.0a HasStack frame inversion lemmas

Each peels one frame off a stack typing. Stated with all the effect/type indices as
free variables so the `cases` inside succeeds (only the EvalCtx index is constructor-
shaped, which `cases` resolves by unification). The callers then avoid the
dependent-elimination friction of `cases hstack` directly on a specialized focus type. -/

theorem HasStack.letF_inv {N : Comp} {K : EvalCtx} {e : Eff} {C : CTy Eff Mult}
    {eo : Eff} {Co : CTy Eff Mult} :
    HasStack (Frame.letF N :: K) e C eo Co →
    ∃ q A e₂ qk B, C = CTy.F q A ∧ HasCTy (qk :: []) [A] N e₂ B
      ∧ HasStack K (e ⊔ e₂) B eo Co := by
  intro h
  cases h with
  | @letF _ _ e₁ e₂ eo q qk A B Co hN hsub => exact ⟨q, A, e₂, qk, B, rfl, hN, hsub⟩

theorem HasStack.appF_inv {w : Val} {K : EvalCtx} {e : Eff} {C : CTy Eff Mult}
    {eo : Eff} {Co : CTy Eff Mult} :
    HasStack (Frame.appF w :: K) e C eo Co →
    ∃ q A B, C = CTy.arr q A B ∧ HasVTy [] [] w A ∧ HasStack K e B eo Co := by
  intro h
  cases h with
  | @appF _ _ _ _ q A B Co hv hsub => exact ⟨q, A, B, rfl, hv, hsub⟩

/-- Invert a `throws` handler frame (the focus type forces the handler to be `throws`, since the
caller already knows `hdl = throws ℓ`). -/
theorem HasStack.handleF_throws_inv {n : Nat} {ℓ : Label} {K : EvalCtx} {e : Eff} {C : CTy Eff Mult}
    {eo : Eff} {Co : CTy Eff Mult} :
    HasStack (Frame.handleF n (Handler.throws ℓ) :: K) e C eo Co →
    ∃ φ q A, C = CTy.F q A
      ∧ EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "raise" = some A
      ∧ (∀ op B, EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ op = some B → op = "raise")
      ∧ e ≤ EffSig.labelEff (Eff := Eff) (Mult := Mult) ℓ ⊔ φ
      ∧ HasStack K φ (CTy.F q A) eo Co := by
  intro h
  cases h with
  | @handleF _ _ _ _ φ eo q A Co hraise hiface hdis _ hsub =>
    exact ⟨φ, q, A, rfl, hraise, hiface, hdis, hsub⟩

/-- Invert ANY handler frame (`throws` or `state`): the focus is `F q A`, the handler discharges its
label, and the substack types `F q A` to the whole program. Used by the REDUCE-`handleF`-`ret` case
(the handler return clause is the identity for both handler kinds, ADR-0023 Q6 / ADR-0025).
ADR-0054: the frame carries the identity `n` (extra implicit). -/
theorem HasStack.handleAny_inv {n : Nat} {hdl : Handler} {K : EvalCtx} {e : Eff} {C : CTy Eff Mult}
    {eo : Eff} {Co : CTy Eff Mult} :
    HasStack (Frame.handleF n hdl :: K) e C eo Co →
    ∃ φ q A, C = CTy.F q A ∧ ∃ eo', eo' ≤ eo ∧ HasStack K φ (CTy.F q A) eo' Co := by
  intro h
  cases h with
  | @handleF _ _ _ _ φ eo q A Co hraise hiface hdis _ hsub => exact ⟨φ, q, A, rfl, eo, le_refl _, hsub⟩
  | @stateF _ _ _ _ _ φ eo q A S Co hga hgr hpa hpr hif hs hdis _ hsub =>
    exact ⟨φ, q, A, rfl, eo, le_refl _, hsub⟩
  | @transactionF _ _ _ _ _ φ eo q A Co hna hnr hra hrr hwa hwr hif hcells hdis _ hsub =>
    exact ⟨φ, q, A, rfl, eo, le_refl _, hsub⟩

/-! ### E.0b Closed-focus HasCTy inversion lemmas (Γ = [], γ = [])

The CK focus is always closed (`HasCTy [] [] M e C`). These peel one head constructor.
Each is `cases` over a fully-variable-indexed hypothesis, so dependent elimination
goes through; the callers stay clear of the friction. -/

theorem HasCTy.ret_inv {γ0 : GradeVec Mult} {Γ0 : TyCtx Eff Mult}
    {v : Val} {e : Eff} {C : CTy Eff Mult} :
    HasCTy γ0 Γ0 (Comp.ret v) e C →
    ∃ γ' A q, e = ⊥ ∧ C = CTy.F q A ∧ γ0 = q • γ' ∧ HasVTy γ' Γ0 v A := by
  intro h
  cases h with
  | @ret _ γ' _ _ A q hv hγ => exact ⟨γ', A, q, rfl, rfl, hγ, hv⟩

-- ADR-0054: `HasCTy.perform_inv` is DELETED — the old positional `perform cap ℓ op v` shape is gone
-- (perform now carries a `Cap ℓ` VALUE), and its sole consumer was the deleted `preservation_perform_typing`.
-- progress's perform case reads `CapResolves` off `NonEscape` directly (no typed inversion needed).

theorem HasCTy.letC_inv {γ0 : GradeVec Mult} {Γ0 : TyCtx Eff Mult}
    {M N : Comp} {e : Eff} {C : CTy Eff Mult} :
    HasCTy γ0 Γ0 (Comp.letC M N) e C →
    ∃ γ₁ γ₂ φ₁ φ₂ q1 q2 A, e = φ₁ ⊔ φ₂ ∧ γ0 = (q_or_1 q2) • γ₁ + γ₂
      ∧ HasCTy γ₁ Γ0 M φ₁ (CTy.F q1 A)
      ∧ HasCTy ((q1 * q_or_1 q2) :: γ₂) (A :: Γ0) N φ₂ C := by
  intro h
  cases h with
  | @letC _ γ₁ γ₂ _ _ _ φ₁ φ₂ q1 q2 A B hM hN hγ =>
    exact ⟨γ₁, γ₂, φ₁, φ₂, q1, q2, A, rfl, hγ, hM, hN⟩

theorem HasCTy.app_inv {γ0 : GradeVec Mult} {Γ0 : TyCtx Eff Mult}
    {M : Comp} {w : Val} {e : Eff} {C : CTy Eff Mult} :
    HasCTy γ0 Γ0 (Comp.app M w) e C →
    ∃ γ₁ γ₂ q A, γ0 = γ₁ + q • γ₂
      ∧ HasCTy γ₁ Γ0 M e (CTy.arr q A C) ∧ HasVTy γ₂ Γ0 w A := by
  intro h
  cases h with
  | @app _ γ₁ γ₂ _ _ _ φ q A B hM hw hγ =>
    exact ⟨γ₁, γ₂, q, A, hγ, hM, hw⟩

theorem HasCTy.force_inv {γ0 : GradeVec Mult} {Γ0 : TyCtx Eff Mult}
    {w : Val} {e : Eff} {C : CTy Eff Mult} :
    HasCTy γ0 Γ0 (Comp.force w) e C → HasVTy γ0 Γ0 w (VTy.U e C) := by
  intro h
  cases h with
  | @force _ _ _ φ B hw => exact hw

/-- Invert a `U`-typed value: in any context it is `vthunk` or `vvar`. -/
theorem HasVTy.U_inv {γ0 : GradeVec Mult} {Γ0 : TyCtx Eff Mult}
    {w : Val} {φ : Eff} {B : CTy Eff Mult} :
    HasVTy γ0 Γ0 w (VTy.U φ B) →
    (∃ M, w = Val.vthunk M ∧ HasCTy γ0 Γ0 M φ B)
      ∨ (∃ i, w = Val.vvar i ∧ Γ0[i]? = some (VTy.U φ B) ∧ γ0 = GradeVec.basis Γ0.length i) := by
  intro h
  cases h with
  | @vthunk γ Γ M φ' B' hM => exact Or.inl ⟨M, rfl, hM⟩
  | @vvar Γ i A hget => exact Or.inr ⟨i, rfl, hget, rfl⟩

theorem HasCTy.handleThrows_inv {γ0 : GradeVec Mult} {Γ0 : TyCtx Eff Mult}
    {ℓ : Label} {M : Comp} {e : Eff} {C : CTy Eff Mult} :
    HasCTy γ0 Γ0 (Comp.handle (Handler.throws ℓ) M) e C →
    -- ADR-0054: handle BINDS the cap, so the body is typed under `cap ℓ :: Γ0` with grade `qc :: γ0`.
    ∃ e_body q qc A, C = CTy.F q A
      ∧ EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "raise" = some A
      ∧ (∀ op B, EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ op = some B → op = "raise")
      ∧ HasCTy (qc :: γ0) (VTy.cap ℓ :: Γ0) M e_body (CTy.F q A)
      ∧ e_body ≤ EffSig.labelEff (Eff := Eff) (Mult := Mult) ℓ ⊔ e
      ∧ ¬ LabelOccurs (Eff := Eff) (Mult := Mult) ℓ A := by
  intro h
  cases h with
  | @handleThrows _ _ _ _ e_body φ q qc A hraise hiface hM hle hbocc =>
    exact ⟨e_body, q, qc, A, rfl, hraise, hiface, hM, hle, hbocc⟩

/-- Invert a `handle (state ℓ s₀) M` typing (ADR-0025) — was `handleState_untypable` pre-rung-1. -/
theorem HasCTy.handleState_inv {γ0 : GradeVec Mult} {Γ0 : TyCtx Eff Mult}
    {ℓ : Label} {s₀ : Val} {M : Comp} {e : Eff} {C : CTy Eff Mult} :
    HasCTy γ0 Γ0 (Comp.handle (Handler.state ℓ s₀) M) e C →
    ∃ e_body q qc S A, C = CTy.F q A
      ∧ EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "get" = some VTy.unit
      ∧ EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "get" = some S
      ∧ EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "put" = some S
      ∧ EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "put" = some VTy.unit
      ∧ (∀ op B, EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ op = some B → op = "get" ∨ op = "put")
      ∧ HasVTy [] [] s₀ S
      ∧ HasCTy (qc :: γ0) (VTy.cap ℓ :: Γ0) M e_body (CTy.F q A)
      ∧ e_body ≤ EffSig.labelEff (Eff := Eff) (Mult := Mult) ℓ ⊔ e
      ∧ ¬ LabelOccurs (Eff := Eff) (Mult := Mult) ℓ A := by
  intro h
  cases h with
  | @handleState _ _ _ _ _ e_body φ q qc S A hga hgr hpa hpr hif hs hM hle hbocc =>
    exact ⟨e_body, q, qc, S, A, rfl, hga, hgr, hpa, hpr, hif, hs, hM, hle, hbocc⟩

/-- Invert a `handle (transaction ℓ Θ₀) M` typing (ADR-0030). -/
theorem HasCTy.handleTransaction_inv {γ0 : GradeVec Mult} {Γ0 : TyCtx Eff Mult}
    {ℓ : Label} {Θ₀ : List Val} {M : Comp} {e : Eff} {C : CTy Eff Mult} :
    HasCTy γ0 Γ0 (Comp.handle (Handler.transaction ℓ Θ₀) M) e C →
    ∃ e_body q qc A, C = CTy.F q A
      ∧ EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "newTVar" = some (VTy.int : VTy Eff Mult)
      ∧ EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "newTVar" = some (VTy.int : VTy Eff Mult)
      ∧ EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "readTVar" = some (VTy.int : VTy Eff Mult)
      ∧ EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "readTVar" = some (VTy.int : VTy Eff Mult)
      ∧ EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "writeTVar"
          = some (VTy.prod (VTy.int : VTy Eff Mult) VTy.int)
      ∧ EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "writeTVar" = some VTy.unit
      ∧ (∀ op B, EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ op = some B →
          op = "newTVar" ∨ op = "readTVar" ∨ op = "writeTVar")
      ∧ (∀ cell ∈ Θ₀, HasVTy [] [] cell (VTy.int : VTy Eff Mult))
      ∧ HasCTy (qc :: γ0) (VTy.cap ℓ :: Γ0) M e_body (CTy.F q A)
      ∧ e_body ≤ EffSig.labelEff (Eff := Eff) (Mult := Mult) ℓ ⊔ e
      ∧ ¬ LabelOccurs (Eff := Eff) (Mult := Mult) ℓ A := by
  intro h
  cases h with
  | @handleTransaction _ _ _ _ _ e_body φ q qc A hna hnr hra hrr hwa hwr hif hcells hM hle hbocc =>
    exact ⟨e_body, q, qc, A, rfl, hna, hnr, hra, hrr, hwa, hwr, hif, hcells, hM, hle, hbocc⟩

theorem HasCTy.lam_inv {γ0 : GradeVec Mult} {Γ0 : TyCtx Eff Mult}
    {M : Comp} {e : Eff} {C : CTy Eff Mult} :
    HasCTy γ0 Γ0 (Comp.lam M) e C →
    ∃ q A B, C = CTy.arr q A B ∧ HasCTy (q :: γ0) (A :: Γ0) M e B := by
  intro h
  cases h with
  | @lam _ _ _ φ q A B hM => exact ⟨q, A, B, rfl, hM⟩

theorem HasCTy.case_inv {γ0 : GradeVec Mult} {Γ0 : TyCtx Eff Mult}
    {v : Val} {N₁ N₂ : Comp} {e : Eff} {C : CTy Eff Mult} :
    HasCTy γ0 Γ0 (Comp.case v N₁ N₂) e C →
    ∃ γ_v γ_N q A B, γ0 = q • γ_v + γ_N
      ∧ HasVTy γ_v Γ0 v (VTy.sum A B)
      ∧ HasCTy (q :: γ_N) (A :: Γ0) N₁ e C
      ∧ HasCTy (q :: γ_N) (B :: Γ0) N₂ e C := by
  intro h
  cases h with
  | @case _ γ_v γ_N _ _ _ _ φ q A B C hv hN₁ hN₂ hγ =>
    exact ⟨γ_v, γ_N, q, A, B, hγ, hv, hN₁, hN₂⟩

theorem HasCTy.split_inv {γ0 : GradeVec Mult} {Γ0 : TyCtx Eff Mult}
    {v : Val} {N : Comp} {e : Eff} {C : CTy Eff Mult} :
    HasCTy γ0 Γ0 (Comp.split v N) e C →
    ∃ γ_v γ_N q A B, γ0 = q • γ_v + γ_N
      ∧ HasVTy γ_v Γ0 v (VTy.prod A B)
      ∧ HasCTy (q :: q :: γ_N) (B :: A :: Γ0) N e C := by
  intro h
  cases h with
  | @split _ γ_v γ_N _ _ _ φ q A B C hv hN hγ =>
    exact ⟨γ_v, γ_N, q, A, B, hγ, hv, hN⟩

theorem HasCTy.unfold_inv {γ0 : GradeVec Mult} {Γ0 : TyCtx Eff Mult}
    {v : Val} {e : Eff} {C : CTy Eff Mult} :
    HasCTy γ0 Γ0 (Comp.unfold v) e C →
    ∃ A, e = ⊥ ∧ C = CTy.F 1 (VTy.unrollMu A) ∧ HasVTy γ0 Γ0 v (VTy.mu A) := by
  intro h
  cases h with
  | @unfold _ _ _ A hv => exact ⟨A, rfl, rfl, hv⟩

/-- Canonical forms for a CLOSED sum value: `v : A + B` in the empty context is
`inl a` or `inr a`. `vvar` is excluded ( `[][i]? = none`). -/
theorem HasVTy.sum_canonical {γ0 : GradeVec Mult}
    {v : Val} {A B : VTy Eff Mult} :
    HasVTy γ0 [] v (VTy.sum A B) →
    (∃ a, v = Val.inl a ∧ HasVTy γ0 [] a A)
      ∨ (∃ a, v = Val.inr a ∧ HasVTy γ0 [] a B) := by
  intro h
  cases h with
  | @inl _ _ a _ _ ha => exact Or.inl ⟨a, rfl, ha⟩
  | @inr _ _ a _ _ ha => exact Or.inr ⟨a, rfl, ha⟩
  | @vvar _ i _ hget => simp at hget

/-- Canonical forms for a CLOSED product value: `v : A × B` is `pair a b`. -/
theorem HasVTy.prod_canonical {γ0 : GradeVec Mult}
    {v : Val} {A B : VTy Eff Mult} :
    HasVTy γ0 [] v (VTy.prod A B) →
    ∃ γ_a γ_b a b, v = Val.pair a b ∧ γ0 = γ_a + γ_b
      ∧ HasVTy γ_a [] a A ∧ HasVTy γ_b [] b B := by
  intro h
  cases h with
  | @pair _ γ_a γ_b _ a b _ _ ha hb hγ => exact ⟨γ_a, γ_b, a, b, rfl, hγ, ha, hb⟩
  | @vvar _ i _ hget => simp at hget

/-- Canonical forms for a CLOSED μ value: `v : μX.A` is `fold a` with `a : unrollMu A`. -/
theorem HasVTy.mu_canonical {γ0 : GradeVec Mult}
    {v : Val} {A : VTy Eff Mult} :
    HasVTy γ0 [] v (VTy.mu A) →
    ∃ a, v = Val.fold a ∧ HasVTy γ0 [] a (VTy.unrollMu A) := by
  intro h
  cases h with
  | @fold _ _ a _ ha => exact ⟨a, rfl, ha⟩
  | @vvar _ i _ hget => simp at hget

/-- `oom`/`wrong` are untypable: no HasCTy rule. -/
theorem HasCTy.oom_untypable {γ0 : GradeVec Mult} {Γ0 : TyCtx Eff Mult}
    {e : Eff} {C : CTy Eff Mult} : ¬ HasCTy γ0 Γ0 Comp.oom e C := by
  intro h; cases h

theorem HasCTy.wrong_untypable {γ0 : GradeVec Mult} {Γ0 : TyCtx Eff Mult}
    {s : String} {e : Eff} {C : CTy Eff Mult} : ¬ HasCTy γ0 Γ0 (Comp.wrong s) e C := by
  intro h; cases h

/-- A focus typed at a smaller effect `e'` plugs into the same stack, with the
whole-program effect only shrinking. Induction on `HasStack`; each frame is
effect-monotone in its focus effect. -/
theorem HasStack.weaken_eff {K : EvalCtx} {e e' : Eff} {C : CTy Eff Mult}
    {eo : Eff} {Co : CTy Eff Mult} :
    HasStack K e C eo Co → e' ≤ e → ∃ eo', eo' ≤ eo ∧ HasStack K e' C eo' Co := by
  intro hK
  induction hK generalizing e' with
  | @nil e0 C0 =>
    intro hle; exact ⟨e', hle, HasStack.nil⟩
  | @letF K N e₁ e₂ eo q qk A B Co hN hsub ih =>
    intro hle
    -- focus F q A at e₁ → narrow to e₁'; substack runs at (e₁' ⊔ e₂) ≤ (e₁ ⊔ e₂)
    obtain ⟨eo', hleo, hsub'⟩ := ih (sup_le_sup_right hle e₂)
    exact ⟨eo', hleo, HasStack.letF hN hsub'⟩
  | @appF K v e eo q A B Co hv hsub ih =>
    intro hle
    obtain ⟨eo', hleo, hsub'⟩ := ih hle
    exact ⟨eo', hleo, HasStack.appF hv hsub'⟩
  | @handleF K n ℓ e φ eo q A Co hraise hiface hdis hbocc hsub ih =>
    intro hle
    -- e' ≤ e ≤ labelEff ℓ ⊔ φ; rebuild same frame, same substack ⇒ same eo
    exact ⟨eo, le_refl _, HasStack.handleF hraise hiface (le_trans hle hdis) hbocc hsub⟩
  | @stateF K n ℓ s e φ eo q A S Co hga hgr hpa hpr hif hs hdis hbocc hsub ih =>
    intro hle
    exact ⟨eo, le_refl _, HasStack.stateF hga hgr hpa hpr hif hs (le_trans hle hdis) hbocc hsub⟩
  | @transactionF K n ℓ Θ e φ eo q A Co hna hnr hra hrr hwa hwr hif hcells hdis hbocc hsub ih =>
    -- rebuild the same transaction frame at the narrowed focus effect (ADR-0030).
    intro hle
    exact ⟨eo, le_refl _,
      HasStack.transactionF hna hnr hra hrr hwa hwr hif hcells (le_trans hle hdis) hbocc hsub⟩

/-! ### E.1c label-blind concat decomposition (the STATIC re-typing core, ADR-0045 1b → ADR-0054 STEP-5)

RE-KEYED onto identity dispatch (STEP 5): the boundary frame carries the identity `n`
(`Frame.handleF n (Handler.…)`), and the resume lemmas reinstall `handleF n (…)` (matching `dispatchOn`'s
reinstall). The `Kᵢ`-peeling is unchanged (label-blind). Used by `preservation_proof`'s perform case.

Given `HasStack (Kᵢ ++ handleF h :: Kₒ) e C eo Co`, peel `Kᵢ` frame-by-frame to expose the boundary
`handleF h` frame's typing and re-type either the OUTER `Kₒ` (throws abort) or the RESUMED stack
`Kᵢ ++ handleF h' :: Kₒ` (state/transaction resume). These are LABEL-BLIND (`Kᵢ` is rebuilt by its own
`HasStack` constructors regardless of what it contains) and are the static analogues of
`dispatch_typed` / `dispatch_state_typed` / `dispatch_transaction_typed` — simpler, because the cap
already located the boundary, so no `handlesOp`-driven search/skip recursion is needed. -/

/-- THROWS abort re-typing (static). The boundary handler is a `throws ℓ'` frame; type the outer `Kₒ`
at the throws answer type `A_h = opArg ℓ' "raise"`, whole-program effect `eo' ≤ eo`. Induct on `Kᵢ`. -/
theorem HasStack.concat_throws_typed {n : Nat} {Kᵢ Kₒ : EvalCtx} {ℓ' : Label} {e : Eff} {C : CTy Eff Mult}
    {eo : Eff} {Co : CTy Eff Mult} :
    HasStack (Kᵢ ++ Frame.handleF n (Handler.throws ℓ') :: Kₒ) e C eo Co →
    ∃ q A_h eo', eo' ≤ eo
      ∧ EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ' "raise" = some A_h
      ∧ HasStack Kₒ ⊥ (CTy.F q A_h) eo' Co := by
  induction Kᵢ generalizing e C with
  | nil =>
    intro hK; simp only [List.nil_append] at hK
    obtain ⟨φ, q, A, hCeq, hraise, hiface, hle, hsub⟩ := hK.handleF_throws_inv
    obtain ⟨eo', hleo, hsub'⟩ := hsub.weaken_eff (bot_le)
    exact ⟨q, A, eo', hleo, hraise, hsub'⟩
  | cons fr Kᵢ ih =>
    intro hK; simp only [List.cons_append] at hK
    cases hK with
    | @letF _ _ _ e₂ _ q qk A B _ hN hsub => exact ih hsub
    | @appF _ _ _ _ q A B _ hv hsub => exact ih hsub
    | @handleF _ _ ℓ'' _ φ _ q A _ hraise hiface hle _ hsub => exact ih hsub
    | @stateF _ _ ℓ'' s₀ _ φ _ q A S₀ _ hga hgr hpa hpr hif hs hle _ hsub => exact ih hsub
    | @transactionF _ _ ℓ'' Θ₀ _ φ _ q A _ hna hnr hra hrr hwa hwr hif hcells hle _ hsub => exact ih hsub

/-- STATE resume re-typing (static). The boundary handler is a `state ℓ' s` frame; reinstall a
`state ℓ' s'` frame (any closed `s' : S`, `S = opRes ℓ' "get"`) over the same `Kᵢ`/`Kₒ`, re-typing the
resumed stack at the SAME `e C`. Each `Kᵢ` frame is rebuilt by `cases hK` (so the exact constructor —
incl. nested `state`/`transaction` frames — is preserved, not lost to `handleAny_inv`). This is the
WellCapped-under-resume core: the resumed stack has the IDENTICAL frame skeleton (only `s↦s'` at one
`handleF`), which is why the static cap of every buried perform still resolves. -/
theorem HasStack.concat_state_resume {n : Nat} {Kᵢ Kₒ : EvalCtx} {ℓ' : Label} {s s' : Val} {S : VTy Eff Mult}
    {e : Eff} {C : CTy Eff Mult} {eo : Eff} {Co : CTy Eff Mult} :
    HasStack (Kᵢ ++ Frame.handleF n (Handler.state ℓ' s) :: Kₒ) e C eo Co →
    EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ' "get" = some S →
    HasVTy [] [] s' S →
    ∃ eo', eo' ≤ eo
      ∧ HasStack (Kᵢ ++ Frame.handleF n (Handler.state ℓ' s') :: Kₒ) e C eo' Co := by
  intro hK hgetRes hs'
  induction Kᵢ generalizing e C with
  | nil =>
    simp only [List.nil_append] at hK ⊢
    cases hK with
    | @stateF _ _ _ _ _ φ _ q A S0 _ hga hgr hpa hpr hif hs hle hbocc hsub =>
      have hSeq : S = S0 := by rw [hgr] at hgetRes; exact (Option.some.inj hgetRes).symm
      subst hSeq
      exact ⟨eo, le_refl _, HasStack.stateF hga hgr hpa hpr hif hs' hle hbocc hsub⟩
  | cons fr Kᵢ ih =>
    simp only [List.cons_append] at hK ⊢
    cases hK with
    | @letF _ _ _ e₂ _ q qk A B _ hN hsub =>
      obtain ⟨eo', hleo, hsub'⟩ := ih hsub
      exact ⟨eo', hleo, HasStack.letF hN hsub'⟩
    | @appF _ _ _ _ q A B _ hv hsub =>
      obtain ⟨eo', hleo, hsub'⟩ := ih hsub
      exact ⟨eo', hleo, HasStack.appF hv hsub'⟩
    | @handleF _ _ ℓ'' _ φ _ q A _ hraise hiface hle hbocc hsub =>
      obtain ⟨eo', hleo, hsub'⟩ := ih hsub
      exact ⟨eo', hleo, HasStack.handleF hraise hiface hle hbocc hsub'⟩
    | @stateF _ _ ℓ'' s₀ _ φ _ q A S₀ _ hga hgr hpa hpr hif hs hle hbocc hsub =>
      obtain ⟨eo', hleo, hsub'⟩ := ih hsub
      exact ⟨eo', hleo, HasStack.stateF hga hgr hpa hpr hif hs hle hbocc hsub'⟩
    | @transactionF _ _ ℓ'' Θ₀ _ φ _ q A _ hna hnr hra hrr hwa hwr hif hcells hle hbocc hsub =>
      obtain ⟨eo', hleo, hsub'⟩ := ih hsub
      exact ⟨eo', hleo, HasStack.transactionF hna hnr hra hrr hwa hwr hif hcells hle hbocc hsub'⟩

/-- TRANSACTION resume re-typing (static), the multi-cell analogue of `concat_state_resume`. The
boundary `transaction ℓ' Θ` frame is reinstalled as `transaction ℓ' Θ'` (any all-`int`-cells heap `Θ'`)
over the same `Kᵢ`/`Kₒ`. The interface premises (facts about `ℓ'`'s `EffSig`, heap-invariant) are
passed in to re-discharge the reinstalled frame. -/
theorem HasStack.concat_transaction_resume {n : Nat} {Kᵢ Kₒ : EvalCtx} {ℓ' : Label} {Θ Θ' : Store}
    {e : Eff} {C : CTy Eff Mult} {eo : Eff} {Co : CTy Eff Mult} :
    HasStack (Kᵢ ++ Frame.handleF n (Handler.transaction ℓ' Θ) :: Kₒ) e C eo Co →
    (∀ cell ∈ Θ', HasVTy [] [] cell (VTy.int : VTy Eff Mult)) →
    ∃ eo', eo' ≤ eo
      ∧ HasStack (Kᵢ ++ Frame.handleF n (Handler.transaction ℓ' Θ') :: Kₒ) e C eo' Co := by
  intro hK hcells'
  induction Kᵢ generalizing e C with
  | nil =>
    simp only [List.nil_append] at hK ⊢
    cases hK with
    | @transactionF _ _ _ _ _ φ _ q A _ hna hnr hra hrr hwa hwr hif hcells hle hbocc hsub =>
      exact ⟨eo, le_refl _, HasStack.transactionF hna hnr hra hrr hwa hwr hif hcells' hle hbocc hsub⟩
  | cons fr Kᵢ ih =>
    simp only [List.cons_append] at hK ⊢
    cases hK with
    | @letF _ _ _ e₂ _ q qk A B _ hN hsub =>
      obtain ⟨eo', hleo, hsub'⟩ := ih hsub
      exact ⟨eo', hleo, HasStack.letF hN hsub'⟩
    | @appF _ _ _ _ q A B _ hv hsub =>
      obtain ⟨eo', hleo, hsub'⟩ := ih hsub
      exact ⟨eo', hleo, HasStack.appF hv hsub'⟩
    | @handleF _ _ ℓ'' _ φ _ q A _ hraise hiface hle hbocc hsub =>
      obtain ⟨eo', hleo, hsub'⟩ := ih hsub
      exact ⟨eo', hleo, HasStack.handleF hraise hiface hle hbocc hsub'⟩
    | @stateF _ _ ℓ'' s₀ _ φ _ q A S₀ _ hga hgr hpa hpr hif hs hle hbocc hsub =>
      obtain ⟨eo', hleo, hsub'⟩ := ih hsub
      exact ⟨eo', hleo, HasStack.stateF hga hgr hpa hpr hif hs hle hbocc hsub'⟩
    | @transactionF _ _ ℓ'' Θ₀ _ φ _ q A _ hna hnr hra hrr hwa hwr hif hcells hle hbocc hsub =>
      obtain ⟨eo', hleo, hsub'⟩ := ih hsub
      exact ⟨eo', hleo, HasStack.transactionF hna hnr hra hrr hwa hwr hif hcells hle hbocc hsub'⟩

/-- The boundary `state ℓ' s` frame (located by the cap) carries a CLOSED stored state of type
`S = opRes ℓ' "get"` and the get/put interface signatures — read off by peeling `Kᵢ` to the boundary
(`cases hK`). The static analogue of `splitAt_state_closed`, over the concat. -/
theorem HasStack.concat_state_closed {n : Nat} {Kᵢ Kₒ : EvalCtx} {ℓ' : Label} {s : Val} {e : Eff}
    {C : CTy Eff Mult} {eo : Eff} {Co : CTy Eff Mult} :
    HasStack (Kᵢ ++ Frame.handleF n (Handler.state ℓ' s) :: Kₒ) e C eo Co →
    ∃ S, EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ' "get" = some S
      ∧ EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ' "put" = some S
      ∧ EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ' "put" = some VTy.unit
      ∧ HasVTy [] [] s S := by
  induction Kᵢ generalizing e C with
  | nil =>
    intro hK; simp only [List.nil_append] at hK
    cases hK with
    | @stateF _ _ _ _ _ φ _ q A S0 _ hga hgr hpa hpr hif hs hle _ hsub => exact ⟨S0, hgr, hpa, hpr, hs⟩
  | cons fr Kᵢ ih =>
    intro hK; simp only [List.cons_append] at hK
    cases hK with
    | @letF _ _ _ e₂ _ q qk A B _ hN hsub => exact ih hsub
    | @appF _ _ _ _ q A B _ hv hsub => exact ih hsub
    | @handleF _ _ ℓ'' _ φ _ q A _ hraise hiface hle _ hsub => exact ih hsub
    | @stateF _ _ ℓ'' s₀ _ φ _ q A S₀ _ hga hgr hpa hpr hif hs hle _ hsub => exact ih hsub
    | @transactionF _ _ ℓ'' Θ₀ _ φ _ q A _ hna hnr hra hrr hwa hwr hif hcells hle _ hsub => exact ih hsub

/-- The boundary `transaction ℓ' Θ` frame (located by the cap) carries a CLOSED all-`int` heap and the
monomorphic-`int` stm interface signatures — read off by peeling `Kᵢ` to the boundary. The static
analogue of `splitAt_transaction_store`, over the concat. -/
theorem HasStack.concat_transaction_store {n : Nat} {Kᵢ Kₒ : EvalCtx} {ℓ' : Label} {Θ : Store} {e : Eff}
    {C : CTy Eff Mult} {eo : Eff} {Co : CTy Eff Mult} :
    HasStack (Kᵢ ++ Frame.handleF n (Handler.transaction ℓ' Θ) :: Kₒ) e C eo Co →
      EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ' "newTVar" = some VTy.int
      ∧ EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ' "newTVar" = some VTy.int
      ∧ EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ' "readTVar" = some VTy.int
      ∧ EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ' "readTVar" = some VTy.int
      ∧ EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ' "writeTVar" = some (VTy.prod VTy.int VTy.int)
      ∧ EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ' "writeTVar" = some VTy.unit
      ∧ (∀ op B, EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ' op = some B →
          op = "newTVar" ∨ op = "readTVar" ∨ op = "writeTVar")
      ∧ (∀ cell ∈ Θ, HasVTy [] [] cell (VTy.int : VTy Eff Mult)) := by
  induction Kᵢ generalizing e C with
  | nil =>
    intro hK; simp only [List.nil_append] at hK
    cases hK with
    | @transactionF _ _ _ _ _ φ _ q A _ hna hnr hra hrr hwa hwr hif hcells hle _ hsub =>
      exact ⟨hna, hnr, hra, hrr, hwa, hwr, hif, hcells⟩
  | cons fr Kᵢ ih =>
    intro hK; simp only [List.cons_append] at hK
    cases hK with
    | @letF _ _ _ e₂ _ q qk A B _ hN hsub => exact ih hsub
    | @appF _ _ _ _ q A B _ hv hsub => exact ih hsub
    | @handleF _ _ ℓ'' _ φ _ q A _ hraise hiface hle _ hsub => exact ih hsub
    | @stateF _ _ ℓ'' s₀ _ φ _ q A S₀ _ hga hgr hpa hpr hif hs hle _ hsub => exact ih hsub
    | @transactionF _ _ ℓ'' Θ₀ _ φ _ q A _ hna hnr hra hrr hwa hwr hif hcells hle _ hsub => exact ih hsub

/-! ### E.1d STEP-5: identity-dispatch decomposition (`splitAtId_decomp`) -/

/-- **The identity-dispatch decomposition.** A successful `splitAtId` certifies the stack is
`Kᵢ ++ handleF n h :: Kₒ` — the boundary frame's identity IS the resolved cap `n` (the `m = n` match),
the inner prefix `Kᵢ` is the captured continuation, `Kₒ` the outer stack. Mirror of the deleted
`staticSplit_decomp` onto `splitAtId` (ADR-0054). Induction on `K`. -/
theorem splitAtId_decomp : ∀ (K : EvalCtx) (n : Nat) {Kᵢ Kₒ : EvalCtx} {h : Handler},
    splitAtId K n = some (Kᵢ, h, Kₒ) → K = Kᵢ ++ Frame.handleF n h :: Kₒ := by
  intro K n
  induction K with
  | nil => intro Kᵢ Kₒ h hsp; simp [splitAtId] at hsp
  | cons fr K ih =>
    intro Kᵢ Kₒ h hsp
    cases fr with
    | handleF m h₀ =>
      simp only [splitAtId] at hsp
      by_cases hmn : m = n
      · rw [if_pos hmn] at hsp
        simp only [Option.some.injEq, Prod.mk.injEq] at hsp
        obtain ⟨hKi, hh, hKo⟩ := hsp
        subst hKi; subst hh; subst hKo; subst hmn; rfl
      · rw [if_neg hmn, Option.map_eq_some_iff] at hsp
        obtain ⟨⟨Kᵢ', h', Kₒ'⟩, hsp', heq⟩ := hsp
        simp only [Prod.mk.injEq] at heq
        obtain ⟨hKi, hh, hKo⟩ := heq
        subst hKi; subst hh; subst hKo
        rw [ih hsp']; rfl
    | letF N =>
      simp only [splitAtId, Option.map_eq_some_iff] at hsp
      obtain ⟨⟨Kᵢ', h', Kₒ'⟩, hsp', heq⟩ := hsp
      simp only [Prod.mk.injEq] at heq
      obtain ⟨hKi, hh, hKo⟩ := heq
      subst hKi; subst hh; subst hKo
      rw [ih hsp']; rfl
    | appF w =>
      simp only [splitAtId, Option.map_eq_some_iff] at hsp
      obtain ⟨⟨Kᵢ', h', Kₒ'⟩, hsp', heq⟩ := hsp
      simp only [Prod.mk.injEq] at heq
      obtain ⟨hKi, hh, hKo⟩ := heq
      subst hKi; subst hh; subst hKo
      rw [ih hsp']; rfl

/-- Full `perform` focus inversion (ADR-0054 shape): exposes the cap typing, the op interface, and the
argument typing. The re-typing the preservation perform case threads. -/
theorem HasCTy.perform_full_inv {γ0 : GradeVec Mult} {Γ0 : TyCtx Eff Mult}
    {c : Val} {op : OpId} {v : Val} {e : Eff} {C : CTy Eff Mult} :
    HasCTy γ0 Γ0 (Comp.perform c op v) e C →
    ∃ (ℓ : Label) (γ_c γ_v : GradeVec Mult) (q : Mult) (A B : VTy Eff Mult),
      C = CTy.F q B ∧ γ0 = (q • γ_v) + γ_c
      ∧ HasVTy γ_c Γ0 c (VTy.cap ℓ)
      ∧ EffSig.labelEff (Eff := Eff) (Mult := Mult) ℓ ≤ e
      ∧ EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ op = some A
      ∧ EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ op = some B
      ∧ HasVTy γ_v Γ0 v A := by
  intro h
  cases h with
  | @perform γ_c γ_v _ _ ℓ _ _ φ q A B hcap hle harg hres hv =>
    exact ⟨ℓ, γ_c, γ_v, q, A, B, rfl, rfl, hcap, hle, harg, hres, hv⟩

/-- Canonical form for a CLOSED capability value: `c : Cap ℓ` in the empty context is `vcap n ℓ`
(`vvar` is excluded — `[][i]? = none`). The preservation/progress perform cases rest on this. -/
theorem HasVTy.cap_canonical {γ0 : GradeVec Mult} {c : Val} {ℓ : Label} :
    HasVTy γ0 ([] : TyCtx Eff Mult) c (VTy.cap ℓ) → ∃ n, c = Val.vcap n ℓ := by
  intro h
  cases h with
  | @vcap _ n _ => exact ⟨n, rfl⟩
  | @vvar _ i A hget => simp at hget

theorem preservation_proof
    {cfg cfg' : Config} {eo : Eff} {Co : CTy Eff Mult} :
    HasConfig cfg eo Co → Source.step cfg = some cfg' →
    ∃ eo', eo' ≤ eo ∧ HasConfig cfg' eo' Co := by
  -- ADR-0054: `HasConfig = HasConfigTy ∧ NonEscape`. The TYPING core (`HasConfigTy`) is proven per-case
  -- below. `NonEscape` of the reduct (`hnecfg'`) is preserved BY CONSTRUCTION (`preservation_returnEscape_TODO`,
  -- proven in Operational). The ONE remaining obligation is the DISPATCH (`perform`) reduct re-typing —
  -- the single documented sorry, named below (STEP 5: splitAtId_decomp + the commented E.1c re-typing).
  rintro ⟨⟨e, C, hfocus, hstack⟩, hne⟩ hstep
  have hnecfg' : NonEscape cfg' := preservation_returnEscape_TODO hne hstep
  obtain ⟨g, K, M⟩ := cfg
  cases M with
  | ret v =>
    -- REDUCE/terminal: the top frame drives the step. Focus ret v : ⊥ (F q A), v : A closed.
    obtain ⟨γ', A, q, he, hC, hγ, hwv⟩ := hfocus.ret_inv
    subst he; subst hC
    have hγ'nil : γ' = [] := by have := hwv.length_eq; simpa using this
    subst hγ'nil
    cases K with
    | nil => simp [Source.step] at hstep
    | cons fr K' =>
      cases fr with
      | letF N =>
        simp only [Source.step, Option.some.injEq] at hstep
        subst hstep
        obtain ⟨q', A', e₂, qk, B, hCeq, hN, hsub⟩ := hstack.letF_inv
        rw [CTy.F.injEq] at hCeq; obtain ⟨hqq, hAA⟩ := hCeq; subst hAA
        rw [bot_sup_eq] at hsub
        have hsubst := subst_value_proof qk hwv hN
        simp only [hsmul_eq_smul, GradeVec.smul_nil, hadd_eq_add,
          GradeVec.add_nil_left] at hsubst
        -- NonEscape of the reduct routes through the single typed return-escape lemma (`hnecfg'`).
        exact ⟨eo, le_refl _, ⟨e₂, B, hsubst, hsub⟩, hnecfg'⟩
      | appF w => simp [Source.step] at hstep
      | handleF n h =>
        -- REDUCE handler-return = identity (both throws and state, ADR-0023 Q6 / ADR-0025).
        obtain ⟨φ, q', A', hCeq, eo₀, hleo₀, hsub⟩ := hstack.handleAny_inv
        simp only [Source.step, Option.some.injEq] at hstep
        subst hstep
        rw [CTy.F.injEq] at hCeq; obtain ⟨hqq, hAA⟩ := hCeq; subst hAA
        obtain ⟨eo', hleo, hsub'⟩ := hsub.weaken_eff (bot_le)
        -- ★ THE DECISIVE CASE — handleF-ret preservation BY CONSTRUCTION (R1). ★
        exact ⟨eo', le_trans hleo hleo₀,
          ⟨⊥, CTy.F q' A, HasCTy.ret hwv (by simp [hsmul_eq_smul, GradeVec.smul]), hsub'⟩,
          hnecfg'⟩
  | perform c op v =>
    -- DISPATCH (ADR-0054 IDENTITY). The reduct re-typing, keyed on `splitAtId_decomp` + the E.1c concat
    -- lemmas (re-keyed onto identity dispatch). The step gives the resolved boundary + `handlesOp`; the
    -- boundary handler's KIND drives the 6 op paths (throws-abort / state-get,put / txn-new,read,write).
    obtain ⟨ℓ, γ_c, γ_v, q, A, B, hC, hγ, hcap, hle, hopArg, hopRes, hwv⟩ := hfocus.perform_full_inv
    subst hC
    have hγc : γ_c = [] := by have := hcap.length_eq; simpa using this
    have hγv : γ_v = [] := by have := hwv.length_eq; simpa using this
    subst hγc; subst hγv
    obtain ⟨n, hceq⟩ := hcap.cap_canonical
    subst hceq
    -- ADR-0055: `Source.step`'s perform arm threads the counter `g` via `.map` over the (counter-free)
    -- `idDispatch`. Strip the map FIRST (the inner result `p` stays a single var, so every handler-kind
    -- leaf's `subst hstep2` substitutes it exactly as before), then decompose the `bind`.
    simp only [Source.step, idDispatch, Option.map_eq_some_iff] at hstep
    obtain ⟨p, hbind, hcfg⟩ := hstep
    subst hcfg
    obtain ⟨⟨Kᵢ, hh, Kₒ⟩, hsplit, hstep2⟩ := Option.bind_eq_some_iff.mp hbind
    by_cases hk : handlesOp hh ℓ op = true
    · rw [if_pos hk] at hstep2
      have hdecomp : K = Kᵢ ++ Frame.handleF n hh :: Kₒ := splitAtId_decomp K n hsplit
      rw [hdecomp] at hstack
      cases hh with
      | throws ℓ' =>
        simp only [handlesOp, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hk
        obtain ⟨hℓ, hopr⟩ := hk; subst hℓ; subst hopr
        simp only [dispatchOn, Option.some.injEq] at hstep2
        subst hstep2
        obtain ⟨qh, Ah, eo', hleo, hrA, hsub'⟩ := hstack.concat_throws_typed
        have hAAh : A = Ah := by rw [hopArg] at hrA; exact Option.some.inj hrA
        subst hAAh
        exact ⟨eo', hleo,
          ⟨⊥, CTy.F qh A, HasCTy.ret hwv (by simp [hsmul_eq_smul, GradeVec.smul]), hsub'⟩, hnecfg'⟩
      | state ℓ' s =>
        simp only [handlesOp, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at hk
        obtain ⟨hℓ, hopGP⟩ := hk; subst hℓ
        obtain ⟨S, hgetRes, hputArg, hputRes, hs⟩ := hstack.concat_state_closed
        rcases hopGP with hget | hput
        · subst hget
          simp only [dispatchOn, beq_self_eq_true, if_true, Option.some.injEq] at hstep2
          subst hstep2
          have hSB : S = B := by rw [hopRes] at hgetRes; exact (Option.some.inj hgetRes).symm
          subst hSB
          obtain ⟨eo', hleo, hsub'⟩ := hstack.concat_state_resume hgetRes hs
          obtain ⟨eo'', hleo', hsub''⟩ := hsub'.weaken_eff (bot_le)
          exact ⟨eo'', le_trans hleo' hleo,
            ⟨⊥, CTy.F q S, HasCTy.ret hs (by simp [hsmul_eq_smul, GradeVec.smul]), hsub''⟩, hnecfg'⟩
        · subst hput
          simp only [dispatchOn, show ("put" == "get") = false by decide, Bool.false_eq_true,
            if_false, Option.some.injEq] at hstep2
          subst hstep2
          have hAS : A = S := by rw [hopArg] at hputArg; exact Option.some.inj hputArg
          subst hAS
          have hBunit : B = VTy.unit := by rw [hopRes] at hputRes; exact Option.some.inj hputRes
          subst hBunit
          obtain ⟨eo', hleo, hsub'⟩ := hstack.concat_state_resume hgetRes hwv
          obtain ⟨eo'', hleo', hsub''⟩ := hsub'.weaken_eff (bot_le)
          exact ⟨eo'', le_trans hleo' hleo,
            ⟨⊥, CTy.F q VTy.unit,
              HasCTy.ret HasVTy.vunit (by simp [hsmul_eq_smul, GradeVec.smul, GradeVec.zeros]),
              hsub''⟩, hnecfg'⟩
      | transaction ℓ' Θ =>
        simp only [handlesOp, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at hk
        obtain ⟨hℓ, hopT⟩ := hk; subst hℓ
        obtain ⟨hna, hnr, hra, hrr, hwa, hwr, hif, hcells⟩ := hstack.concat_transaction_store
        rcases hopT with (hnew | hread) | hwrite
        · rw [hnew] at hstep2 hopArg hopRes
          simp only [dispatchOn, beq_self_eq_true, if_true, Option.some.injEq] at hstep2
          subst hstep2
          have hAint : A = VTy.int := by rw [hopArg] at hna; exact Option.some.inj hna
          have hBint : B = VTy.int := by rw [hopRes] at hnr; exact Option.some.inj hnr
          subst hAint; subst hBint
          have hcells' : ∀ cell ∈ Θ ++ [v], HasVTy [] [] cell (VTy.int : VTy Eff Mult) := by
            intro cell hcm; rcases List.mem_append.mp hcm with hc | hc
            · exact hcells cell hc
            · rw [List.mem_singleton] at hc; subst hc; exact hwv
          obtain ⟨eo', hleo, hsub'⟩ := hstack.concat_transaction_resume hcells'
          obtain ⟨eo'', hleo', hsub''⟩ := hsub'.weaken_eff (bot_le)
          exact ⟨eo'', le_trans hleo' hleo,
            ⟨⊥, CTy.F q VTy.int,
              HasCTy.ret (HasVTy.vint (n := (Θ.length : Int)) (Γ := []))
                (by simp [hsmul_eq_smul, GradeVec.smul, GradeVec.zeros]), hsub''⟩, hnecfg'⟩
        · rw [hread] at hstep2 hopArg hopRes
          simp only [dispatchOn, show ("readTVar" == "newTVar") = false by decide, Bool.false_eq_true,
            if_false, beq_self_eq_true, if_true, Option.some.injEq] at hstep2
          subst hstep2
          have hBint : B = VTy.int := by rw [hopRes] at hrr; exact Option.some.inj hrr
          subst hBint
          obtain ⟨eo', hleo, hsub'⟩ := hstack.concat_transaction_resume hcells
          obtain ⟨eo'', hleo', hsub''⟩ := hsub'.weaken_eff (bot_le)
          have hcell : HasVTy [] [] (Θ.getD ((tvarIdx v).getD 0) (Val.vint 0)) (VTy.int : VTy Eff Mult) := by
            rw [List.getD_eq_getElem?_getD]
            rcases lt_or_ge ((tvarIdx v).getD 0) Θ.length with hlt | hge
            · rw [List.getElem?_eq_getElem hlt, Option.getD_some]; exact hcells _ (List.getElem_mem hlt)
            · rw [List.getElem?_eq_none hge, Option.getD_none]; exact HasVTy.vint (n := 0) (Γ := [])
          exact ⟨eo'', le_trans hleo' hleo,
            ⟨⊥, CTy.F q VTy.int, HasCTy.ret hcell (by simp [hsmul_eq_smul, GradeVec.smul, GradeVec.zeros]),
              hsub''⟩, hnecfg'⟩
        · rw [hwrite] at hstep2 hopArg hopRes
          simp only [dispatchOn, show ("writeTVar" == "newTVar") = false by decide,
            show ("writeTVar" == "readTVar") = false by decide, Bool.false_eq_true, if_false] at hstep2
          have hBunit : B = VTy.unit := by rw [hopRes] at hwr; exact Option.some.inj hwr
          subst hBunit
          have hAprod : A = VTy.prod VTy.int VTy.int := by rw [hopArg] at hwa; exact Option.some.inj hwa
          subst hAprod
          obtain ⟨_, γ_b, a, b, hvpair, _, _, hbint⟩ := hwv.prod_canonical
          have hγb : γ_b = [] := by have := hbint.length_eq; simpa using this
          subst hγb
          subst hvpair
          simp only [dispatchOn, Option.some.injEq] at hstep2
          subst hstep2
          have hcells' : ∀ cell ∈ storeSet Θ ((tvarIdx a).getD 0) b,
              HasVTy [] [] cell (VTy.int : VTy Eff Mult) := by
            intro cell hcm
            unfold storeSet at hcm
            rcases List.mem_or_eq_of_mem_set hcm with hc | hc
            · exact hcells cell hc
            · subst hc; exact hbint
          obtain ⟨eo', hleo, hsub'⟩ := hstack.concat_transaction_resume hcells'
          obtain ⟨eo'', hleo', hsub''⟩ := hsub'.weaken_eff (bot_le)
          exact ⟨eo'', le_trans hleo' hleo,
            ⟨⊥, CTy.F q VTy.unit,
              HasCTy.ret HasVTy.vunit (by simp [hsmul_eq_smul, GradeVec.smul, GradeVec.zeros]),
              hsub''⟩, hnecfg'⟩
    · rw [if_neg hk] at hstep2; exact absurd hstep2 (by simp)
  | letC M N =>
    -- PUSH letC
    simp only [Source.step, Option.some.injEq] at hstep
    subst hstep
    obtain ⟨γ₁, γ₂, φ₁, φ₂, q1, q2, A, he, hγ, hM, hN⟩ := hfocus.letC_inv
    subst he
    -- focus is closed: γ₁ = [], γ₂ = []
    have hγ₁ : γ₁ = [] := by have := hM.length_eq; simpa using this
    have hγ₂ : γ₂ = [] := by have := hN.length_eq; simpa using this
    subst hγ₁; subst hγ₂
    -- NonEscape of the reduct via the single return-escape lemma (`hnecfg'`).
    exact ⟨eo, le_refl _, ⟨φ₁, CTy.F q1 A, hM, HasStack.letF hN hstack⟩, hnecfg'⟩
  | app M w =>
    -- PUSH app
    simp only [Source.step, Option.some.injEq] at hstep
    subst hstep
    obtain ⟨γ₁, γ₂, q, A, hγ, hM, hw⟩ := hfocus.app_inv
    have hγ₁ : γ₁ = [] := by have := hM.length_eq; simpa using this
    have hγ₂ : γ₂ = [] := by have := hw.length_eq; simpa using this
    subst hγ₁; subst hγ₂
    -- NonEscape of the reduct via the single return-escape lemma (`hnecfg'`).
    exact ⟨eo, le_refl _, ⟨e, CTy.arr q A C, hM, HasStack.appF hw hstack⟩, hnecfg'⟩
  | handle h M =>
    -- PUSH handle (ADR-0055): mint the GLOBAL-FRESH identity `g` (the carried counter), push
    -- `handleF g h`, advance to `g+1`, and SUBSTITUTE the capability `vcap g ℓ` for the handle-bound
    -- var 0. The reduct focus `subst (vcap g ℓ) M` re-types via `subst_value_proof` at the inert cap
    -- (`HasVTy.vcap`, identity-agnostic), collapsing the body grade `qc::[]` to `[]`. The counter value
    -- is invisible to typing — only the substituted `n := g` must match the step's mint.
    cases h with
    | throws ℓ =>
      simp only [Source.step, Handler.label, Option.some.injEq] at hstep
      subst hstep
      obtain ⟨e_body, q, qc, A, hC, hraise, hiface, hM, hle, hbocc⟩ := hfocus.handleThrows_inv
      subst hC
      have hfocus' := subst_value_proof qc (HasVTy.vcap (n := g) (ℓ := ℓ)) hM
      simp only [hsmul_eq_smul, GradeVec.smul_nil, hadd_eq_add, GradeVec.add_nil_left] at hfocus'
      exact ⟨eo, le_refl _,
        ⟨e_body, CTy.F q A, hfocus', HasStack.handleF hraise hiface hle hbocc hstack⟩, hnecfg'⟩
    | state ℓ s =>
      simp only [Source.step, Handler.label, Option.some.injEq] at hstep
      subst hstep
      obtain ⟨e_body, q, qc, S, A, hC, hga, hgr, hpa, hpr, hif, hs, hM, hle, hbocc⟩ :=
        hfocus.handleState_inv
      subst hC
      have hfocus' := subst_value_proof qc (HasVTy.vcap (n := g) (ℓ := ℓ)) hM
      simp only [hsmul_eq_smul, GradeVec.smul_nil, hadd_eq_add, GradeVec.add_nil_left] at hfocus'
      exact ⟨eo, le_refl _,
        ⟨e_body, CTy.F q A, hfocus', HasStack.stateF hga hgr hpa hpr hif hs hle hbocc hstack⟩, hnecfg'⟩
    | transaction ℓ Θ =>
      simp only [Source.step, Handler.label, Option.some.injEq] at hstep
      subst hstep
      obtain ⟨e_body, q, qc, A, hC, hna, hnr, hra, hrr, hwa, hwr, hif, hcells, hM, hle, hbocc⟩ :=
        hfocus.handleTransaction_inv
      subst hC
      have hfocus' := subst_value_proof qc (HasVTy.vcap (n := g) (ℓ := ℓ)) hM
      simp only [hsmul_eq_smul, GradeVec.smul_nil, hadd_eq_add, GradeVec.add_nil_left] at hfocus'
      exact ⟨eo, le_refl _,
        ⟨e_body, CTy.F q A, hfocus',
          HasStack.transactionF hna hnr hra hrr hwa hwr hif hcells hle hbocc hstack⟩, hnecfg'⟩
  | force w =>
    -- PUSH force: focus typing forces w = vthunk M
    rcases hfocus.force_inv.U_inv with ⟨MT, hweq, hMT⟩ | ⟨i, hweq, hget, _⟩
    · subst hweq
      simp only [Source.step, Option.some.injEq] at hstep
      subst hstep
      -- NonEscape of the reduct via the single return-escape lemma (`hnecfg'`).
      exact ⟨eo, le_refl _, ⟨e, C, hMT, hstack⟩, hnecfg'⟩
    · simp at hget
  | lam M =>
    -- focus lam M : arr-typed; only the appF top-frame drives a step (β).
    obtain ⟨q, A, B, hC, hM⟩ := hfocus.lam_inv
    subst hC
    -- focus closed: the body grade is q :: [] (γ0 = [])
    cases K with
    | nil => simp [Source.step] at hstep
    | cons fr K' =>
      cases fr with
      | letF N =>
        -- letF wants F-focus; arr ≠ F via letF_inv
        obtain ⟨q', A', e₂, qk, B', hCeq, _⟩ := hstack.letF_inv
        exact absurd hCeq (by simp)
      | handleF n h =>
        obtain ⟨φ, q', A', hCeq, _⟩ := hstack.handleAny_inv
        exact absurd hCeq (by simp)
      | appF w =>
        simp only [Source.step, Option.some.injEq] at hstep
        subst hstep
        obtain ⟨q', A', B', hCeq, hwv, hsub⟩ := hstack.appF_inv
        rw [CTy.arr.injEq] at hCeq
        obtain ⟨hqq, hAA, hBB⟩ := hCeq; subst hqq; subst hAA; subst hBB
        have hsubst := subst_value_proof q hwv hM
        simp only [hsmul_eq_smul, GradeVec.smul_nil, hadd_eq_add,
          GradeVec.add_nil_left] at hsubst
        -- NonEscape of the reduct via the single return-escape lemma (`hnecfg'`).
        exact ⟨eo, le_refl _, ⟨e, B, hsubst, hsub⟩, hnecfg'⟩
  | case v N₁ N₂ =>
    -- closed focus `case v N₁ N₂ : (e, C)`; `v : sum A B` is `inl a`/`inr a`
    -- (canonical forms); the matching branch `Nᵢ[a]` re-types at `(e, C)` via subst.
    obtain ⟨γ_v, γ_N, q, A, B, hγ, hv, hN₁, hN₂⟩ := hfocus.case_inv
    -- closed: scrutinee grade `γ_v = []`; branch shared grade `γ_N = []`.
    have hγv : γ_v = [] := by have := hv.length_eq; simpa using this
    have hγN : γ_N = [] := by have := hN₁.length_eq; simp at this; simpa using this
    subst hγv; subst hγN
    rcases hv.sum_canonical with ⟨a, hveq, ha⟩ | ⟨a, hveq, ha⟩
    · subst hveq
      simp only [Source.step, Option.some.injEq] at hstep
      subst hstep
      have hsubst := subst_value_proof q ha hN₁
      simp only [hsmul_eq_smul, GradeVec.smul_nil, hadd_eq_add,
        GradeVec.add_nil_left] at hsubst
      -- NonEscape of the reduct via the single return-escape lemma (`hnecfg'`).
      exact ⟨eo, le_refl _, ⟨e, C, hsubst, hstack⟩, hnecfg'⟩
    · subst hveq
      simp only [Source.step, Option.some.injEq] at hstep
      subst hstep
      have hsubst := subst_value_proof q ha hN₂
      simp only [hsmul_eq_smul, GradeVec.smul_nil, hadd_eq_add,
        GradeVec.add_nil_left] at hsubst
      -- NonEscape of the reduct via the single return-escape lemma (`hnecfg'`).
      exact ⟨eo, le_refl _, ⟨e, C, hsubst, hstack⟩, hnecfg'⟩
  | split v N =>
    -- closed focus `split v N`; `v : prod A B` is `pair a b` (canonical forms);
    -- `N[a][b]` re-types at `(e, C)` via two substitutions (outer `b`, inner `a`).
    obtain ⟨γ_v, γ_N, q, A, B, hγ, hv, hN⟩ := hfocus.split_inv
    obtain ⟨γ_a, γ_b, a, b, hveq, hγab, ha, hb⟩ := hv.prod_canonical
    subst hveq
    simp only [Source.step, Option.some.injEq] at hstep
    subst hstep
    -- closed: every value grade is `[]`; the branch shared grade `γ_N = []`.
    have hlenb : γ_b = [] := by have := hb.length_eq; simpa using this
    have hlena : γ_a = [] := by have := ha.length_eq; simpa using this
    subst hlenb; subst hlena
    have hγN : γ_N = [] := by have := hN.length_eq; simp at this; simpa using this
    subst hγN
    -- inner subst: the OUTER binder (slot 0 of `B :: A :: []`) is `b : B`; weaken `b`
    -- under the `A` binder so it types over `A :: []` (graded `[0]` after the insert).
    have hbw : HasVTy [0] (A :: []) (Val.shift b) B := by
      have := hb.weaken 0 (Nat.zero_le _) A
      simpa [Val.shift, insT, insG, GradeVec.zeros] using this
    -- result grade `(q :: []) + q • [0] = [q]`, i.e. `q :: []` — the shape the outer subst needs.
    have hsubst_inner := subst_value_proof q hbw hN
    simp only [hsmul_eq_smul, GradeVec.smul_cons, GradeVec.smul_nil, hadd_eq_add,
      GradeVec.add_cons, GradeVec.add_nil_left, mul_zero, add_zero] at hsubst_inner
    -- outer subst: the inner binder (now slot 0) is `a : A` (closed, graded `[]`).
    have hsubst_outer := subst_value_proof q ha hsubst_inner
    simp only [hsmul_eq_smul, GradeVec.smul_nil, hadd_eq_add,
      GradeVec.add_nil_left, GradeVec.add_nil_right] at hsubst_outer
    -- NonEscape of the reduct via the single return-escape lemma (`hnecfg'`).
    exact ⟨eo, le_refl _, ⟨e, C, hsubst_outer, hstack⟩, hnecfg'⟩
  | unfold v =>
    -- closed focus `unfold v : (⊥, F 1 (unrollMu A))`; `v : mu A` is `fold a` with
    -- `a : unrollMu A`. Step `unfold (fold a) ↦ ret a`; `ret a : F 1 (unrollMu A)` matches.
    obtain ⟨A, heq, hCeq, hv⟩ := hfocus.unfold_inv
    subst heq; subst hCeq
    obtain ⟨a, hveq, ha⟩ := hv.mu_canonical
    subst hveq
    simp only [Source.step, Option.some.injEq] at hstep
    subst hstep
    -- the closed payload `a` is graded `[]`; `ret a : F 1 (unrollMu A)`, grade `1 • [] = []`.
    -- NonEscape of the reduct via the single return-escape lemma (`hnecfg'`).
    exact ⟨eo, le_refl _, ⟨⊥, CTy.F 1 (VTy.unrollMu A), HasCTy.ret ha (by simp [hsmul_eq_smul]), hstack⟩, hnecfg'⟩
  | oom => exact absurd hfocus HasCTy.oom_untypable
  | wrong s => exact absurd hfocus HasCTy.wrong_untypable

/-! ### E.3 progress (config level, ADR-0023) -/

/-- Expose the capability typing buried in a `perform` focus (the new ADR-0054 shape: the head is a
`Cap ℓ` VALUE). Replaces the deleted positional `perform_inv` for the progress path. -/
theorem HasCTy.perform_cap_inv {γ0 : GradeVec Mult} {Γ0 : TyCtx Eff Mult}
    {c : Val} {op : OpId} {v : Val} {e : Eff} {C : CTy Eff Mult} :
    HasCTy γ0 Γ0 (Comp.perform c op v) e C → ∃ ℓ γ_c, HasVTy γ_c Γ0 c (VTy.cap ℓ) := by
  intro h
  cases h with
  | @perform γ_c _ _ _ ℓ _ _ _ _ _ _ hcap _ _ _ _ => exact ⟨ℓ, γ_c, hcap⟩

/-- `dispatchOn` is TOTAL — every handler kind / op branch returns `some`. shape: NonEscapeProbe §2. -/
theorem dispatchOn_isSome (n : Nat) (op : OpId) (v : Val) (X : EvalCtx × Handler × EvalCtx) :
    ∃ cfg', dispatchOn n op v X = some cfg' := by
  obtain ⟨Kᵢ, h, Kₒ⟩ := X
  cases h <;>
    simp only [dispatchOn] <;>
    (first
      | exact ⟨_, rfl⟩
      | (split <;> exact ⟨_, rfl⟩)
      | (repeat' first | split | exact ⟨_, rfl⟩))

/-- **PROGRESS'S PERFORM CASE** (probe §2): given `CapResolves K n ℓ op`, the `idDispatch` step fires —
`splitAtId` finds the handling frame, the fail-loud `handlesOp` guard passes, and `dispatchOn` is total. -/
theorem progress_perform_from_capResolves
    (g : Nat) (K : EvalCtx) (n : Nat) (ℓ : Label) (op : OpId) (v : Val)
    (hr : CapResolves K n ℓ op) :
    ∃ cfg', Source.step (g, K, Comp.perform (Val.vcap n ℓ) op v) = some cfg' := by
  obtain ⟨Kᵢ, h, Kₒ, hsplit, hhandles⟩ := hr
  obtain ⟨p, hp⟩ := dispatchOn_isSome n op v (Kᵢ, h, Kₒ)
  refine ⟨(g, p.1, p.2), ?_⟩
  simp only [Source.step, idDispatch, hsplit, Option.bind_some, hhandles, if_true, hp,
    Option.map_some]

theorem progress_proof
    {cfg : Config} {q : Mult} {A : VTy Eff Mult} :
    HasConfig cfg ⊥ (CTy.F q A) →
    isReturnConfig cfg ∨ ∃ cfg', Source.step cfg = some cfg' := by
  -- ADR-0054: `HasConfig = HasConfigTy ∧ NonEscape`. The perform case is UNBLOCKED by `NonEscape`: its
  -- `FocusResolves` clause (at the reflexive reach) yields `CapResolves K n ℓ op`, so `idDispatch` fires
  -- (`progress_perform_from_capResolves`). The cap value is `vcap n ℓ` by canonical forms.
  rintro ⟨⟨e, C, hfocus, hstack⟩, hne⟩
  obtain ⟨g, K, M⟩ := cfg
  cases M with
  | letC M N => exact Or.inr ⟨(g, Frame.letF N :: K, M), by simp [Source.step]⟩
  | app M w => exact Or.inr ⟨(g, Frame.appF w :: K, M), by simp [Source.step]⟩
  | handle h M => exact Or.inr ⟨_, rfl⟩
  | force w =>
    rcases hfocus.force_inv.U_inv with ⟨MT, hweq, hMT⟩ | ⟨i, hweq, hget, _⟩
    · subst hweq; exact Or.inr ⟨(g, K, MT), by simp [Source.step]⟩
    · simp at hget
  | perform c op v =>
    -- ADR-0054: the focus types `c : Cap ℓ` (closed) ⇒ `c = vcap n ℓ` (canonical). `NonEscape` then
    -- supplies `CapResolves K n ℓ op` (FocusResolves at the reflexive reach), and `idDispatch` fires.
    obtain ⟨ℓ, γ_c, hcap⟩ := hfocus.perform_cap_inv
    obtain ⟨n, hceq⟩ := hcap.cap_canonical
    subst hceq
    have hfr : FocusResolves (g, K, Comp.perform (Val.vcap n ℓ) op v) := hne _ StepStar.refl
    exact Or.inr (progress_perform_from_capResolves g K n ℓ op v hfr)
  | ret v =>
    cases K with
    | nil => exact Or.inl (by simp [isReturnConfig])
    | cons fr K' =>
      cases fr with
      | letF N => exact Or.inr ⟨(g, K', Comp.subst v N), by simp [Source.step]⟩
      | handleF n h =>
        -- REDUCE handler-return = identity for BOTH throws and state (ADR-0023 Q6 / ADR-0025).
        cases h with
        | throws ℓ => exact Or.inr ⟨(g, K', Comp.ret v), by simp [Source.step]⟩
        | state ℓ s => exact Or.inr ⟨(g, K', Comp.ret v), by simp [Source.step]⟩
        | transaction ℓ Θ => exact Or.inr ⟨(g, K', Comp.ret v), by simp [Source.step]⟩
      | appF w =>
        -- appF wants an arr-focus; ret v : F _ _ contradicts the appF stack premise
        obtain ⟨γ', A0, q0, he, hC, hγ, hwv⟩ := hfocus.ret_inv
        obtain ⟨q', A', B', hCeq, _⟩ := hstack.appF_inv
        rw [hC] at hCeq; exact absurd hCeq (by simp)
  | lam M =>
    -- focus lam M : arr; only the appF top-frame drives a step (β).
    obtain ⟨q', A', B', hC, hM⟩ := hfocus.lam_inv
    subst hC
    cases K with
    | nil =>
      -- HasStack [] (arr ..) C' ⊥ (F q A) via nil forces F q A = arr .. ⇒ contradiction
      cases hstack
    | cons fr K' =>
      cases fr with
      | appF w => exact Or.inr ⟨(g, K', Comp.subst w M), by simp [Source.step]⟩
      | letF N =>
        obtain ⟨q'', A'', e₂, qk, B'', hCeq, _⟩ := hstack.letF_inv
        exact absurd hCeq (by simp)
      | handleF n h =>
        obtain ⟨φ, q'', A'', hCeq, _⟩ := hstack.handleAny_inv
        exact absurd hCeq (by simp)
  | case v N₁ N₂ =>
    -- closed `v : sum A B` is `inl a`/`inr a` (canonical forms); each fires its branch.
    obtain ⟨γ_v, γ_N, q, A, B, hγ, hv, hN₁, hN₂⟩ := hfocus.case_inv
    rcases hv.sum_canonical with ⟨a, hveq, _⟩ | ⟨a, hveq, _⟩
    · subst hveq; exact Or.inr ⟨(g, K, Comp.subst a N₁), by simp [Source.step]⟩
    · subst hveq; exact Or.inr ⟨(g, K, Comp.subst a N₂), by simp [Source.step]⟩
  | split v N =>
    -- closed `v : prod A B` is `pair a b`; split reduces.
    obtain ⟨γ_v, γ_N, q, A, B, hγ, hv, hN⟩ := hfocus.split_inv
    obtain ⟨γ_a, γ_b, a, b, hveq, _, _, _⟩ := hv.prod_canonical
    subst hveq
    exact Or.inr ⟨(g, K, Comp.subst a (Comp.subst (Val.shift b) N)), by simp [Source.step]⟩
  | unfold v =>
    -- closed `v : mu A` is `fold a`; `unfold (fold a) ↦ ret a`.
    obtain ⟨A, _, _, hv⟩ := hfocus.unfold_inv
    obtain ⟨a, hveq, _⟩ := hv.mu_canonical
    subst hveq
    exact Or.inr ⟨(g, K, Comp.ret a), by simp [Source.step]⟩
  | oom => exact absurd hfocus HasCTy.oom_untypable
  | wrong s => exact absurd hfocus HasCTy.wrong_untypable

/-! ### E.4 type_safety (frozen statement, ADR-0023 D3) -/

/-- Config-level safety: a config typed at whole-program `⊥`/`F q A` never runs to
`stuck`. Fuel induction generalizing the config, using config `progress`/`preservation`.
`Config.run`'s `([], ret v)` arm is `done`; otherwise `progress` supplies a step (so the
`none → stuck` arm is unreachable) and `preservation` re-establishes the `⊥` precondition. -/
private theorem run_safe {q : Mult} {A : VTy Eff Mult} :
    ∀ (fuel : Nat) (cfg : Config),
      HasConfig cfg (⊥ : Eff) (CTy.F q A) → Config.run fuel cfg ≠ Result.stuck := by
  intro fuel
  induction fuel with
  | zero => intro cfg _; simp [Config.run]
  | succ n ih =>
    intro cfg hcfg
    rcases progress_proof hcfg with hret | ⟨cfg', hstep⟩
    · -- isReturnConfig cfg ⇒ cfg = (g, [], ret v) ⇒ Config.run hits the `done` arm.
      obtain ⟨g, K, M⟩ := cfg
      cases K with
      | cons fr K' => cases M <;> simp only [isReturnConfig] at hret
      | nil =>
        cases M with
        | ret v => simp [Config.run]
        | letC _ _ => simp only [isReturnConfig] at hret
        | app _ _ => simp only [isReturnConfig] at hret
        | handle _ _ => simp only [isReturnConfig] at hret
        | force _ => simp only [isReturnConfig] at hret
        | perform _ _ _ => simp only [isReturnConfig] at hret
        | lam _ => simp only [isReturnConfig] at hret
        | case _ _ _ => simp only [isReturnConfig] at hret
        | split _ _ => simp only [isReturnConfig] at hret
        | unfold _ => simp only [isReturnConfig] at hret
        | oom => simp only [isReturnConfig] at hret
        | wrong _ => simp only [isReturnConfig] at hret
    · -- cfg steps; preservation gives eo' ≤ ⊥ ⇒ eo' = ⊥; re-establish IH on cfg'.
      obtain ⟨eo', hle, hcfg'⟩ := preservation_proof hcfg hstep
      rw [le_bot_iff] at hle; subst hle
      obtain ⟨g, K, M⟩ := cfg
      have hrun : Config.run (n + 1) (g, K, M) = Config.run n cfg' := by
        cases K with
        | cons fr K' => simp only [Config.run]; rw [hstep]
        | nil =>
          cases M with
          | ret v => simp [Source.step] at hstep
          | letC M N => simp only [Config.run]; rw [hstep]
          | app M w => simp only [Config.run]; rw [hstep]
          | handle hh M => simp only [Config.run]; rw [hstep]
          | force w => simp only [Config.run]; rw [hstep]
          | perform _ o w => simp only [Config.run]; rw [hstep]
          | lam M => simp [Source.step] at hstep
          | case v N₁ N₂ => simp only [Config.run]; rw [hstep]
          | split v N => simp only [Config.run]; rw [hstep]
          | unfold v => simp only [Config.run]; rw [hstep]
          | oom => simp [Source.step] at hstep
          | wrong s => simp [Source.step] at hstep
      rw [hrun]
      exact ih cfg' hcfg'

/-- ADR-0054 collapse: `type_safety` is now stated over `HasConfig ([], c) ⊥ (F q A)` — the SAME
`HasConfig` as `preservation`/`progress`, whose definition is `HasConfigTy ∧ NonEscape`. The empty stack
forces `HasConfigTy ([], c) ⊥ (F q A) ≡ HasCTy [] [] c ⊥ (F q A)`, so this folds the old ADR-0045
`LWConfig ([], c)` premise into `HasConfig`'s `NonEscape ([], c)` conjunct — the INITIAL-CONFIG obligation
the ported LR discharges (inc 5). No raw cap-invariant premise surfaces; the proof is `run_safe` directly. -/
theorem type_safety_proof
    {c : Comp} {q : Mult} {A : VTy Eff Mult} :
    HasConfig (0, [], c) ⊥ (CTy.F q A) → ∀ fuel, Source.eval fuel c ≠ Result.stuck := by
  intro hcfg fuel
  rw [show Source.eval fuel c = Config.run fuel (0, [], c) from rfl]
  exact run_safe fuel (0, [], c) hcfg

/-! ## F. Abstraction-safety — no accidental handling (ADR-0024)

The §0.5 abstraction-safety invariant, monomorphic half. In the label-indexed CK machine
(ADR-0023) a handler catches an operation only via `handlesOp h ℓ op`, which for `throws ℓ₀`
is `ℓ₀ = ℓ` — so a handler structurally cannot catch a label it does not name. Accidental
handling is *unrepresentable*; `no_accidental_handling` witnesses it. (The polymorphic half —
`rowinst_requires_disjoint` — is the lacks-constraint, `WfInst`/ADR-0024 D3.) -/

/-- Handler `h`'s interface lies within row `l`: every operation it catches has its label ≤ `l`. -/
def HandlesWithin (l : Eff) (h : Handler) : Prop :=
  ∀ ℓ' op, handlesOp h ℓ' op = true → EffSig.labelEff (Eff := Eff) (Mult := Mult) ℓ' ≤ l

/-- A `throws ℓ₀` handler is scoped to its own label's row (discharges the `HandlesWithin`
premise of `no_accidental_handling` for the only handler form; `state` extends it — Q12). -/
theorem throws_handlesWithin (ℓ₀ : Label) :
    HandlesWithin (Eff := Eff) (Mult := Mult)
      (EffSig.labelEff (Eff := Eff) (Mult := Mult) ℓ₀) (Handler.throws ℓ₀) := by
  intro ℓ' op hcatch
  simp only [handlesOp, Bool.and_eq_true, decide_eq_true_eq] at hcatch
  obtain ⟨hℓ, _⟩ := hcatch
  subst hℓ
  exact le_refl _

/-- NO ACCIDENTAL HANDLING (ADR-0024 D2): a handler scoped to row `l` never catches a FOREIGN
operation — one whose label is in a disjoint row `e`. Such operations tunnel to an outer handler.
Every hypothesis is load-bearing: `HandlesWithin` (a catch forces label ≤ l), `Disjoint l e`
(label ≤ l ⊓ e = ⊥), `labelEff_ne_bot` (⊥ is impossible for a real label). -/
theorem no_accidental_handling_proof
    {l e : Eff} {h : Handler} :
    HandlesWithin (Eff := Eff) (Mult := Mult) l h → Disjoint l e →
    ∀ ℓ' op, EffSig.labelEff (Eff := Eff) (Mult := Mult) ℓ' ≤ e → handlesOp h ℓ' op = false := by
  intro hHW hDisj ℓ' op hℓ'e
  by_contra hne
  have hcatch : handlesOp h ℓ' op = true := by
    cases hh : handlesOp h ℓ' op
    · exact absurd hh hne
    · rfl
  have hℓ'l := hHW ℓ' op hcatch
  have hbot : EffSig.labelEff (Eff := Eff) (Mult := Mult) ℓ' ≤ (⊥ : Eff) := hDisj hℓ'l hℓ'e
  exact EffSig.labelEff_ne_bot (Eff := Eff) (Mult := Mult) ℓ' (le_bot_iff.mp hbot)

/-- Lacks-constrained row instantiation is well-formed only when disjoint (ADR-0018 rule 2,
ADR-0024 D3). `WfInst` carries exactly this, so the theorem projects it out. -/
theorem rowinst_requires_disjoint_proof
    {q : Eff → CTy Eff Mult} {L ε : Eff} :
    WfInst q L ε → Disjoint ε L := id

end Bang
