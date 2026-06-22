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

variable {Eff  : Type} [Lattice Eff] [OrderBot Eff]
variable {Mult : Type} [Semiring Mult] [DecidableEq Mult]

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

theorem HasCTy.length_eq {γ : GradeVec Mult} {Γ : TyCtx Eff Mult}
    {c : Comp} {e : Eff} {B : CTy Eff Mult} :
    HasCTy γ Γ c e B → γ.length = Γ.length := by
  intro h
  refine HasCTy.rec
    (motive_1 := fun γ Γ _ _ _ => γ.length = Γ.length)
    (motive_2 := fun γ Γ _ _ _ _ => γ.length = Γ.length)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro Γ; simp
  · intro Γ n; simp
  · intro Γ i A hget; simp
  · intro γ Γ M φ B _ ih; exact ih
  · intro γ γ' Γ w A q hw hγ ih; subst hγ; simp only [hsmul_eq_smul,
      GradeVec.smul_length]; exact ih
  · intro γ γ₁ γ₂ Γ M N φ₁ φ₂ q1 q2 A B _ _ hγ ihM ihN
    subst hγ
    simp only [List.length_cons] at ihN
    simp only [hsmul_eq_smul, hadd_eq_add, GradeVec.add_length, GradeVec.smul_length,
      ihM, Nat.succ.inj ihN, Nat.min_self]
  · intro γ Γ w φ B _ ih; exact ih
  · intro γ Γ M φ q A B _ ih
    simp only [List.length_cons] at ih
    exact Nat.succ.inj ih
  · intro γ γ₁ γ₂ Γ M w φ q A B _ _ hγ ihM ihV
    subst hγ
    simp only [hsmul_eq_smul, hadd_eq_add, GradeVec.add_length, GradeVec.smul_length,
      ihM, ihV, Nat.min_self]
  · intro γ Γ hdl M φ B _ ih; exact ih

theorem HasVTy.length_eq {γ : GradeVec Mult} {Γ : TyCtx Eff Mult}
    {v : Val} {A : VTy Eff Mult} :
    HasVTy γ Γ v A → γ.length = Γ.length := by
  intro h
  refine HasVTy.rec
    (motive_1 := fun γ Γ _ _ _ => γ.length = Γ.length)
    (motive_2 := fun γ Γ _ _ _ _ => γ.length = Γ.length)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro Γ; simp
  · intro Γ n; simp
  · intro Γ i A hget; simp
  · intro γ Γ M φ B _ ih; exact ih
  · intro γ γ' Γ w A q hw hγ ih; subst hγ; simp only [hsmul_eq_smul,
      GradeVec.smul_length]; exact ih
  · intro γ γ₁ γ₂ Γ M N φ₁ φ₂ q1 q2 A B _ _ hγ ihM ihN
    subst hγ
    simp only [List.length_cons] at ihN
    simp only [hsmul_eq_smul, hadd_eq_add, GradeVec.add_length, GradeVec.smul_length,
      ihM, Nat.succ.inj ihN, Nat.min_self]
  · intro γ Γ w φ B _ ih; exact ih
  · intro γ Γ M φ q A B _ ih
    simp only [List.length_cons] at ih
    exact Nat.succ.inj ih
  · intro γ γ₁ γ₂ Γ M w φ q A B _ _ hγ ihM ihV
    subst hγ
    simp only [hsmul_eq_smul, hadd_eq_add, GradeVec.add_length, GradeVec.smul_length,
      ihM, ihV, Nat.min_self]
  · intro γ Γ hdl M φ B _ ih; exact ih

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
  | @vthunk γ Γ M φ B hM =>
    simp only [Val.shiftFrom]
    exact HasVTy.vthunk (hM.weaken k hk A')

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
  | @handle γ Γ h M φ B hM =>
    simp only [Comp.shiftFrom]
    exact HasCTy.handle (hM.weaken k hk A')
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
    simp [add_comm, add_left_comm, add_assoc, add_mul, mul_comm]

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
           (Comp.substFrom Δ.length v (Comp.lam M)) ⊥ (CTy.arr q A₀ B) := by
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
    ?vunit ?vint ?vvar ?vthunk ?ret ?letC ?force ?lam ?app ?handle
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
  case vthunk =>
    intro γ Γ₀ M φ B hM ih Δ Γ A γ_v v hΓ hv
    subst hΓ
    have := ih Δ Γ A γ_v v rfl hv
    rw [Val.substFrom]
    exact HasVTy.vthunk this
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
  case handle =>
    intro γ Γ₀ hdl M φ B hM ih Δ Γ A γ_v v hΓ hv
    subst hΓ
    rw [Comp.substFrom]
    exact HasCTy.handle (ih Δ Γ A γ_v v rfl hv)

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

end Bang
