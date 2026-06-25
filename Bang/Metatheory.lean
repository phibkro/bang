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
    ?vunit ?vint ?vvar ?vthunk ?inl ?inr ?pair ?fold
    ?ret ?letC ?force ?lam ?app ?case ?split ?unfold ?perform ?handleThrows ?handleState
    ?handleTransaction h
  case vunit => intro Γ; simp
  case vint => intro Γ n; simp
  case vvar => intro Γ i A hget; simp
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
  case perform => intro γ Γ _cap ℓ op w φ q A B _ _ _ _ ih; simp only [hsmul_eq_smul, GradeVec.smul_length]
                  exact ih
  case handleThrows => intro γ Γ ℓ M e φ q A _ _ _ _ ih; exact ih
  case handleState => intro γ Γ ℓ s₀ M e φ q S A _ _ _ _ _ _ _ _ _ ihM; exact ihM
  case handleTransaction =>
    -- the handler leaves γ/Γ unchanged ⇒ `motive M = motive (handle ...)` definitionally. After
    -- intro-ing all value-args + the `hcells` IH, the goal is the `hM`-IH implication
    -- `motive M → motive (handle …)`, which id discharges.
    intro γ Γ ℓ Θ₀ M e φ q A _ _ _ _ _ _ _ _ _ _ _
    exact fun ih => ih

theorem HasVTy.length_eq {γ : GradeVec Mult} {Γ : TyCtx Eff Mult}
    {v : Val} {A : VTy Eff Mult} :
    HasVTy γ Γ v A → γ.length = Γ.length := by
  intro h
  refine HasVTy.rec
    (motive_1 := fun γ Γ _ _ _ => γ.length = Γ.length)
    (motive_2 := fun γ Γ _ _ _ _ => γ.length = Γ.length)
    ?vunit ?vint ?vvar ?vthunk ?inl ?inr ?pair ?fold
    ?ret ?letC ?force ?lam ?app ?case ?split ?unfold ?perform ?handleThrows ?handleState
    ?handleTransaction h
  case vunit => intro Γ; simp
  case vint => intro Γ n; simp
  case vvar => intro Γ i A hget; simp
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
  case perform => intro γ Γ _cap ℓ op w φ q A B _ _ _ _ ih; simp only [hsmul_eq_smul, GradeVec.smul_length]
                  exact ih
  case handleThrows => intro γ Γ ℓ M e φ q A _ _ _ _ ih; exact ih
  case handleState => intro γ Γ ℓ s₀ M e φ q S A _ _ _ _ _ _ _ _ _ ihM; exact ihM
  case handleTransaction =>
    -- the handler leaves γ/Γ unchanged ⇒ `motive M = motive (handle ...)` definitionally. After
    -- intro-ing all value-args + the `hcells` IH, the goal is the `hM`-IH implication
    -- `motive M → motive (handle …)`, which id discharges.
    intro γ Γ ℓ Θ₀ M e φ q A _ _ _ _ _ _ _ _ _ _ _
    exact fun ih => ih

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
  | @perform γ Γ _ ℓ op v φ q A B _ _ _ hv =>
    simp only [Comp.shiftFrom]; rw [hv.shift_closed k hk]
  | @handleThrows γ Γ ℓ M e φ q A _ _ hM _ =>
    simp only [Comp.shiftFrom, Handler.shiftFrom]; rw [hM.shift_closed k hk]
  | @handleState γ Γ ℓ s₀ M e φ q S A _ _ _ _ _ hs hM _ =>
    simp only [Comp.shiftFrom, Handler.shiftFrom]
    rw [hM.shift_closed k hk, hs.shift_closed k (Nat.zero_le k)]
  | @handleTransaction γ Γ ℓ Θ₀ M e φ q A _ _ _ _ _ _ _ hcells hM _ =>
    -- `Handler.shiftFrom` leaves the heap untouched (closed cells, ADR-0030); body fixed by IH.
    simp only [Comp.shiftFrom, Handler.shiftFrom]
    rw [hM.shift_closed k hk]
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
  | @perform γ Γ _ ℓ op v φ q A B _ _ _ hv =>
    simp only [Comp.substFrom]; rw [hv.subst_closed k hk w]
  -- ADR-0045 cap-shift: `Comp.substFrom`'s `handle` case fills the body with `Val.shiftCap w`.
  -- For a CLOSED body (no free vars ≥ k), `substFrom k (shiftCap w) M = M` — apply the IH at the
  -- SHIFTED filler (the IH is universally quantified over the filler value).
  | @handleThrows γ Γ ℓ M e φ q A _ _ hM _ =>
    simp only [Comp.substFrom, Handler.substFrom]; rw [hM.subst_closed k hk (Val.shiftCap w)]
  | @handleState γ Γ ℓ s₀ M e φ q S A _ _ _ _ _ hs hM _ =>
    simp only [Comp.substFrom, Handler.substFrom]
    rw [hM.subst_closed k hk (Val.shiftCap w), hs.subst_closed k (Nat.zero_le k) w]
  | @handleTransaction γ Γ ℓ Θ₀ M e φ q A _ _ _ _ _ _ _ hcells hM _ =>
    -- `Handler.substFrom` leaves the heap untouched (closed cells, ADR-0030); body fixed by IH.
    simp only [Comp.substFrom, Handler.substFrom]
    rw [hM.subst_closed k hk (Val.shiftCap w)]
end

/-! ### Cap-shift preserves typing (ADR-0045 R1) — the enabler for the `handle`-case substitution ripple.

`Comp.shiftCapFrom`/`Val.shiftCapFrom` rewrite ONLY the `cap` field of `perform`s (and recurse). Since
`HasCTy.perform` is CAP-IRRELEVANT (the rule constrains the row/grade/op, never the cap), the cap-shift
preserves `HasCTy`/`HasVTy` — re-type each shifted subterm by the IH. The `handle` cases bump the cutoff
(`d+1`), matching `shiftCapFrom`'s `handle` arm. This is what lets `subst`'s `handle` case (filler
`Val.shiftCap v`) re-type its body: the cap-shift on the filler does not disturb its type. -/
mutual
theorem HasVTy.shiftCap {γ : GradeVec Mult} {Γ : TyCtx Eff Mult} {v : Val} {A : VTy Eff Mult}
    (h : HasVTy γ Γ v A) (d : Nat) : HasVTy γ Γ (Val.shiftCapFrom d v) A := by
  cases h with
  | vunit => exact HasVTy.vunit
  | vint => exact HasVTy.vint
  | @vvar Γ i A hget => exact HasVTy.vvar hget
  | @vthunk γ Γ M φ B hM => exact HasVTy.vthunk (hM.shiftCap d)
  | @inl γ Γ u A B hu => exact HasVTy.inl (hu.shiftCap d)
  | @inr γ Γ u A B hu => exact HasVTy.inr (hu.shiftCap d)
  | @pair γ γ_v γ_w Γ u₁ u₂ A B hu₁ hu₂ heq => exact HasVTy.pair (hu₁.shiftCap d) (hu₂.shiftCap d) heq
  | @fold γ Γ u A hu => exact HasVTy.fold (hu.shiftCap d)
theorem HasCTy.shiftCap {γ : GradeVec Mult} {Γ : TyCtx Eff Mult} {c : Comp} {e : Eff}
    {C : CTy Eff Mult} (h : HasCTy γ Γ c e C) (d : Nat) : HasCTy γ Γ (Comp.shiftCapFrom d c) e C := by
  cases h with
  | @ret γ γ' Γ v A q hv heq => exact HasCTy.ret (hv.shiftCap d) heq
  | @letC γ γ₁ γ₂ Γ M N φ₁ φ₂ q1 q2 A B hM hN heq => exact HasCTy.letC (hM.shiftCap d) (hN.shiftCap d) heq
  | @force γ Γ v φ B hv => exact HasCTy.force (hv.shiftCap d)
  | @lam γ Γ M φ q A B hM => exact HasCTy.lam (hM.shiftCap d)
  | @app γ γ₁ γ₂ Γ M v φ q A B hM hv heq => exact HasCTy.app (hM.shiftCap d) (hv.shiftCap d) heq
  | @case γ γ_v γ_N Γ v N₁ N₂ φ q A B C hv hN₁ hN₂ heq =>
      exact HasCTy.case (hv.shiftCap d) (hN₁.shiftCap d) (hN₂.shiftCap d) heq
  | @split γ γ_v γ_N Γ v N φ q A B C hv hN heq => exact HasCTy.split (hv.shiftCap d) (hN.shiftCap d) heq
  | @unfold γ Γ v A hv => exact HasCTy.unfold (hv.shiftCap d)
  | @perform γ Γ cap ℓ op v φ q A B hmem hopArg hopRes hv =>
      exact HasCTy.perform hmem hopArg hopRes (hv.shiftCap d)
  | @handleThrows γ Γ ℓ M e φ q A hraise hiface hM hle =>
      exact HasCTy.handleThrows hraise hiface (hM.shiftCap (d+1)) hle
  | @handleState γ Γ ℓ s₀ M e φ q S A hga hgr hpa hpr hif hs hM hle =>
      exact HasCTy.handleState hga hgr hpa hpr hif (hs.shiftCap d) (hM.shiftCap (d+1)) hle
  | @handleTransaction γ Γ ℓ Θ₀ M e φ q A hna hnr hra hrr hwa hwr hif hcells hM hle =>
      exact HasCTy.handleTransaction hna hnr hra hrr hwa hwr hif hcells (hM.shiftCap (d+1)) hle
end

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
  | @perform γ Γ _ ℓ op w φ q A B hmem hopArg hopRes hw =>
    -- shiftFrom k (up ℓ op w) = up ℓ op (shiftFrom k w); grade insG (q•γ) k = q • insG γ k.
    -- The interface premises (opArg/opRes) carry no grade content; thread verbatim.
    simp only [Comp.shiftFrom]
    have hw' := hw.weaken k hk A'
    have hgr : insG (q • γ) k = q • insG γ k := insG_smul q γ k
    rw [hgr]
    exact HasCTy.perform hmem hopArg hopRes hw'
  | @handleThrows γ Γ ℓ M e φ q A hraise hiface hM hle =>
    -- handle (throws ℓ) carries no value ⇒ unchanged by shift; weaken the body.
    -- Answer-type + interface premises thread verbatim (no grade content).
    simp only [Comp.shiftFrom, Handler.shiftFrom]
    exact HasCTy.handleThrows hraise hiface (hM.weaken k hk A') hle
  | @handleState γ Γ ℓ s₀ M e φ q S A hga hgr hpa hpr hif hs hM hle =>
    -- state's stored value is CLOSED, so shift leaves it fixed (ADR-0025); weaken the body.
    simp only [Comp.shiftFrom, Handler.shiftFrom]
    rw [hs.shift_closed k (Nat.zero_le k)]
    exact HasCTy.handleState hga hgr hpa hpr hif hs (hM.weaken k hk A') hle
  | @handleTransaction γ Γ ℓ Θ₀ M e φ q A hna hnr hra hrr hwa hwr hif hcells hM hle =>
    -- `Handler.shiftFrom` leaves the heap untouched (closed cells, ADR-0030); weaken the body.
    simp only [Comp.shiftFrom, Handler.shiftFrom]
    exact HasCTy.handleTransaction hna hnr hra hrr hwa hwr hif hcells (hM.weaken k hk A') hle
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
    ?vunit ?vint ?vvar ?vthunk ?inl ?inr ?pair ?fold
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
    intro γ Γ₀ _cap ℓ op w φ q A₀ B₀ hmem hopArg hopRes hw ih Δ Γ A γ_v v hΓ hv
    subst hΓ
    rw [Comp.substFrom]
    -- Sgrade γ_v k (q • γ) = q • Sgrade γ_v k γ. Interface premises thread verbatim.
    simp only [hsmul_eq_smul, Sgrade_smul]
    exact HasCTy.perform hmem hopArg hopRes (ih Δ Γ A γ_v v rfl hv)
  -- ADR-0045 cap-shift: `Comp.substFrom`'s `handle` arm fills the body with `Val.shiftCap v`
  -- (`handle` is a cap-binder). The body IH (`ihM`) re-types it at the SHIFTED filler — `v`'s type is
  -- preserved by `HasVTy.shiftCap`, so `ihM Δ Γ A γ_v (shiftCap v) rfl (hv.shiftCap 0)` discharges it.
  case handleThrows =>
    intro γ Γ₀ ℓ M e φ q A₀ hraise hiface hM hle ih Δ Γ A γ_v v hΓ hv
    subst hΓ
    rw [Comp.substFrom, Handler.substFrom]
    exact HasCTy.handleThrows hraise hiface (ih Δ Γ A γ_v (Val.shiftCap v) rfl (hv.shiftCap 0)) hle
  case handleState =>
    intro γ Γ₀ ℓ s₀ M e φ q S A₀ hga hgr hpa hpr hif hs hM hle _ihs ihM Δ Γ A γ_v v hΓ hv
    subst hΓ
    rw [Comp.substFrom, Handler.substFrom]
    -- the stored state is CLOSED ⇒ substFrom leaves it fixed (ADR-0025)
    rw [hs.subst_closed Δ.length (Nat.zero_le _) _]
    exact HasCTy.handleState hga hgr hpa hpr hif hs
      (ihM Δ Γ A γ_v (Val.shiftCap v) rfl (hv.shiftCap 0)) hle
  case handleTransaction =>
    -- subst through a transaction handler. `Handler.substFrom` leaves the heap untouched (closed
    -- cells, ADR-0030), so only the body substitutes (via `ihM`); structural, like `handleState`.
    intro γ Γ₀ ℓ Θ₀ M e φ q A₀ hna hnr hra hrr hwa hwr hif hcells hM hle _hcellsIH ihM
      Δ Γ A γ_v v hΓ hv
    subst hΓ
    rw [Comp.substFrom, Handler.substFrom]
    exact HasCTy.handleTransaction hna hnr hra hrr hwa hwr hif hcells
      (ihM Δ Γ A γ_v (Val.shiftCap v) rfl (hv.shiftCap 0)) hle

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
theorem HasStack.handleF_throws_inv {ℓ : Label} {K : EvalCtx} {e : Eff} {C : CTy Eff Mult}
    {eo : Eff} {Co : CTy Eff Mult} :
    HasStack (Frame.handleF (Handler.throws ℓ) :: K) e C eo Co →
    ∃ φ q A, C = CTy.F q A
      ∧ EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "raise" = some A
      ∧ (∀ op B, EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ op = some B → op = "raise")
      ∧ e ≤ EffSig.labelEff (Eff := Eff) (Mult := Mult) ℓ ⊔ φ
      ∧ HasStack K φ (CTy.F q A) eo Co := by
  intro h
  cases h with
  | @handleF _ _ _ φ eo q A Co hraise hiface hdis hsub =>
    exact ⟨φ, q, A, rfl, hraise, hiface, hdis, hsub⟩

/-- Invert ANY handler frame (`throws` or `state`): the focus is `F q A`, the handler discharges its
label, and the substack types `F q A` to the whole program. Used by the REDUCE-`handleF`-`ret` case
(the handler return clause is the identity for both handler kinds, ADR-0023 Q6 / ADR-0025). -/
theorem HasStack.handleAny_inv {hdl : Handler} {K : EvalCtx} {e : Eff} {C : CTy Eff Mult}
    {eo : Eff} {Co : CTy Eff Mult} :
    HasStack (Frame.handleF hdl :: K) e C eo Co →
    ∃ φ q A, C = CTy.F q A ∧ ∃ eo', eo' ≤ eo ∧ HasStack K φ (CTy.F q A) eo' Co := by
  intro h
  cases h with
  | @handleF _ _ _ φ eo q A Co hraise hiface hdis hsub => exact ⟨φ, q, A, rfl, eo, le_refl _, hsub⟩
  | @stateF _ _ _ _ φ eo q A S Co hga hgr hpa hpr hif hs hdis hsub =>
    exact ⟨φ, q, A, rfl, eo, le_refl _, hsub⟩
  | @transactionF _ _ _ _ φ eo q A Co hna hnr hra hrr hwa hwr hif hcells hdis hsub =>
    exact ⟨φ, q, A, rfl, eo, le_refl _, hsub⟩

/-- Invert a `state` handler frame (ADR-0025). -/
theorem HasStack.stateF_inv {ℓ : Label} {s : Val} {K : EvalCtx} {e : Eff} {C : CTy Eff Mult}
    {eo : Eff} {Co : CTy Eff Mult} :
    HasStack (Frame.handleF (Handler.state ℓ s) :: K) e C eo Co →
    ∃ φ q A S, C = CTy.F q A
      ∧ EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "get" = some VTy.unit
      ∧ EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "get" = some S
      ∧ EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "put" = some S
      ∧ EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "put" = some VTy.unit
      ∧ (∀ op B, EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ op = some B → op = "get" ∨ op = "put")
      ∧ HasVTy [] [] s S
      ∧ e ≤ EffSig.labelEff (Eff := Eff) (Mult := Mult) ℓ ⊔ φ
      ∧ HasStack K φ (CTy.F q A) eo Co := by
  intro h
  cases h with
  | @stateF _ _ _ _ φ eo q A S Co hga hgr hpa hpr hif hs hdis hsub =>
    exact ⟨φ, q, A, S, rfl, hga, hgr, hpa, hpr, hif, hs, hdis, hsub⟩

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

theorem HasCTy.perform_inv {γ0 : GradeVec Mult} {Γ0 : TyCtx Eff Mult}
    {cap : Nat} {ℓ : Label} {op : OpId} {v : Val} {e : Eff} {C : CTy Eff Mult} :
    HasCTy γ0 Γ0 (Comp.perform cap ℓ op v) e C →
    ∃ γ q A B, C = CTy.F q B ∧ γ0 = q • γ
      ∧ EffSig.labelEff (Eff := Eff) (Mult := Mult) ℓ ≤ e
      ∧ EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ op = some A
      ∧ EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ op = some B
      ∧ HasVTy γ Γ0 v A := by
  intro h
  cases h with
  | @perform γ _ _ _ _ _ _ q A B hmem hopArg hopRes hv =>
    exact ⟨γ, q, A, B, rfl, rfl, hmem, hopArg, hopRes, hv⟩

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
    ∃ e_body q A, C = CTy.F q A
      ∧ EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "raise" = some A
      ∧ (∀ op B, EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ op = some B → op = "raise")
      ∧ HasCTy γ0 Γ0 M e_body (CTy.F q A)
      ∧ e_body ≤ EffSig.labelEff (Eff := Eff) (Mult := Mult) ℓ ⊔ e := by
  intro h
  cases h with
  | @handleThrows _ _ _ _ e_body φ q A hraise hiface hM hle =>
    exact ⟨e_body, q, A, rfl, hraise, hiface, hM, hle⟩

/-- Invert a `handle (state ℓ s₀) M` typing (ADR-0025) — was `handleState_untypable` pre-rung-1. -/
theorem HasCTy.handleState_inv {γ0 : GradeVec Mult} {Γ0 : TyCtx Eff Mult}
    {ℓ : Label} {s₀ : Val} {M : Comp} {e : Eff} {C : CTy Eff Mult} :
    HasCTy γ0 Γ0 (Comp.handle (Handler.state ℓ s₀) M) e C →
    ∃ e_body q S A, C = CTy.F q A
      ∧ EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "get" = some VTy.unit
      ∧ EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "get" = some S
      ∧ EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "put" = some S
      ∧ EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "put" = some VTy.unit
      ∧ (∀ op B, EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ op = some B → op = "get" ∨ op = "put")
      ∧ HasVTy [] [] s₀ S
      ∧ HasCTy γ0 Γ0 M e_body (CTy.F q A)
      ∧ e_body ≤ EffSig.labelEff (Eff := Eff) (Mult := Mult) ℓ ⊔ e := by
  intro h
  cases h with
  | @handleState _ _ _ _ _ e_body φ q S A hga hgr hpa hpr hif hs hM hle =>
    exact ⟨e_body, q, S, A, rfl, hga, hgr, hpa, hpr, hif, hs, hM, hle⟩

/-- Invert a `handle (transaction ℓ Θ₀) M` typing (ADR-0030). -/
theorem HasCTy.handleTransaction_inv {γ0 : GradeVec Mult} {Γ0 : TyCtx Eff Mult}
    {ℓ : Label} {Θ₀ : List Val} {M : Comp} {e : Eff} {C : CTy Eff Mult} :
    HasCTy γ0 Γ0 (Comp.handle (Handler.transaction ℓ Θ₀) M) e C →
    ∃ e_body q A, C = CTy.F q A
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
      ∧ HasCTy γ0 Γ0 M e_body (CTy.F q A)
      ∧ e_body ≤ EffSig.labelEff (Eff := Eff) (Mult := Mult) ℓ ⊔ e := by
  intro h
  cases h with
  | @handleTransaction _ _ _ _ _ e_body φ q A hna hnr hra hrr hwa hwr hif hcells hM hle =>
    exact ⟨e_body, q, A, rfl, hna, hnr, hra, hrr, hwa, hwr, hif, hcells, hM, hle⟩

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
  | @handleF K ℓ e φ eo q A Co hraise hiface hdis hsub ih =>
    intro hle
    -- e' ≤ e ≤ labelEff ℓ ⊔ φ; rebuild same frame, same substack ⇒ same eo
    exact ⟨eo, le_refl _, HasStack.handleF hraise hiface (le_trans hle hdis) hsub⟩
  | @stateF K ℓ s e φ eo q A S Co hga hgr hpa hpr hif hs hdis hsub ih =>
    intro hle
    exact ⟨eo, le_refl _, HasStack.stateF hga hgr hpa hpr hif hs (le_trans hle hdis) hsub⟩
  | @transactionF K ℓ Θ e φ eo q A Co hna hnr hra hrr hwa hwr hif hcells hdis hsub ih =>
    -- rebuild the same transaction frame at the narrowed focus effect (ADR-0030).
    intro hle
    exact ⟨eo, le_refl _,
      HasStack.transactionF hna hnr hra hrr hwa hwr hif hcells (le_trans hle hdis) hsub⟩

/-! ### E.1a `splitAt` / `dispatch` reduction lemmas (ADR-0025)

`dispatch` now routes through `splitAt` (returns the inner prefix `Kᵢ` so `state` can KEEP it).
The throws-soundness lemmas below induct over `HasStack`, whose `handleF` frames are ALWAYS
`throws` (the only stack-typing constructor — `state` is untypable, Q12/ADR-0025), so the `state`
branch of `dispatch` is unreachable in these proofs. These equational lemmas unfold `splitAt`/
`dispatch` over the three frame shapes so the inductions go through as in ADR-0023. -/

@[simp] theorem splitAt_nil (ℓ : Label) (op : OpId) :
    splitAt ([] : EvalCtx) ℓ op = none := rfl

theorem splitAt_letF (N : Comp) (K : EvalCtx) (ℓ : Label) (op : OpId) :
    splitAt (Frame.letF N :: K) ℓ op
      = (splitAt K ℓ op).map (fun (Kᵢ, h', Kₒ) => (Frame.letF N :: Kᵢ, h', Kₒ)) := rfl

theorem splitAt_appF (w : Val) (K : EvalCtx) (ℓ : Label) (op : OpId) :
    splitAt (Frame.appF w :: K) ℓ op
      = (splitAt K ℓ op).map (fun (Kᵢ, h', Kₒ) => (Frame.appF w :: Kᵢ, h', Kₒ)) := rfl

/-- A NON-matching `handleF h` frame is skipped (`hcatch : handlesOp h ℓ op = false`): split the tail
and prepend the frame to the inner prefix. -/
theorem splitAt_handleF_miss {h : Handler} {ℓ : Label} {op : OpId} (K : EvalCtx)
    (hcatch : handlesOp h ℓ op = false) :
    splitAt (Frame.handleF h :: K) ℓ op
      = (splitAt K ℓ op).map (fun (Kᵢ, h', Kₒ) => (Frame.handleF h :: Kᵢ, h', Kₒ)) := by
  show (if handlesOp h ℓ op then some ([], h, K)
        else (splitAt K ℓ op).map (fun (Kᵢ, h', Kₒ) => (Frame.handleF h :: Kᵢ, h', Kₒ))) = _
  rw [if_neg (by rw [hcatch]; simp)]

/-- A MATCHING `handleF h` frame (`hcatch : handlesOp h ℓ op = true`) is the split point. -/
theorem splitAt_handleF_hit {h : Handler} {ℓ : Label} {op : OpId} (K : EvalCtx)
    (hcatch : handlesOp h ℓ op = true) :
    splitAt (Frame.handleF h :: K) ℓ op = some ([], h, K) := by
  show (if handlesOp h ℓ op then some ([], h, K)
        else (splitAt K ℓ op).map (fun (Kᵢ, h', Kₒ) => (Frame.handleF h :: Kᵢ, h', Kₒ))) = _
  rw [if_pos (by rw [hcatch])]

/-- For `op = "raise"`, any catching frame found by `splitAt` is a `throws` handler: `state` catches
only `get`/`put` (`handlesOp (state ..) ℓ "raise" = false`), so the split skips it. Hence `splitAt`'s
handler component is `throws _`. -/
theorem splitAt_raise_throws {K : EvalCtx} {ℓ : Label} {Kᵢ Kₒ : EvalCtx} {h : Handler} :
    splitAt K ℓ "raise" = some (Kᵢ, h, Kₒ) → ∃ ℓ', h = Handler.throws ℓ' := by
  induction K generalizing Kᵢ Kₒ h with
  | nil => intro hd; simp [splitAt] at hd
  | cons fr K ih =>
    cases fr with
    | letF N =>
      intro hd; rw [splitAt_letF, Option.map_eq_some_iff] at hd
      obtain ⟨⟨Kᵢ', h', Kₒ'⟩, hsp, heq⟩ := hd
      simp only [Prod.mk.injEq] at heq
      exact heq.2.1 ▸ ih hsp
    | appF w =>
      intro hd; rw [splitAt_appF, Option.map_eq_some_iff] at hd
      obtain ⟨⟨Kᵢ', h', Kₒ'⟩, hsp, heq⟩ := hd
      simp only [Prod.mk.injEq] at heq
      exact heq.2.1 ▸ ih hsp
    | handleF hh =>
      intro hd
      by_cases hcatch : handlesOp hh ℓ "raise" = true
      · -- this frame catches ⇒ splitAt returns this handler; it must be throws (state ≠ raise)
        rw [splitAt_handleF_hit K hcatch, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hd
        obtain ⟨_, hheq, _⟩ := hd
        subst hheq
        cases hh with
        | throws ℓ' => exact ⟨ℓ', rfl⟩
        | state ℓ' s => simp [handlesOp] at hcatch
        | transaction ℓ' Θ => simp [handlesOp] at hcatch
      · -- does not catch ⇒ recurse
        simp only [Bool.not_eq_true] at hcatch
        rw [splitAt_handleF_miss K hcatch, Option.map_eq_some_iff] at hd
        obtain ⟨⟨Kᵢ', h', Kₒ'⟩, hsp, heq⟩ := hd
        simp only [Prod.mk.injEq] at heq
        exact heq.2.1 ▸ ih hsp

/-- CLOSED FORM for `"raise"` dispatch: since the catching handler is always `throws` (which aborts
to the OUTER stack `Kₒ` with the payload, discarding `Kᵢ`), dispatch is exactly `splitAt`'s outer
stack paired with `ret v`. This collapses all throws reasoning to `splitAt` map-algebra. -/
theorem dispatch_raise_eq (K : EvalCtx) (ℓ : Label) (v : Val) :
    dispatch K ℓ "raise" v
      = (splitAt K ℓ "raise").map (fun (p : EvalCtx × Handler × EvalCtx) => (p.2.2, Comp.ret v)) := by
  unfold dispatch
  cases hsp : splitAt K ℓ "raise" with
  | none => simp
  | some t =>
    obtain ⟨Kᵢ, h, Kₒ⟩ := t
    obtain ⟨ℓ', hℓ'⟩ := splitAt_raise_throws hsp
    subst hℓ'
    simp [dispatchOn]

theorem dispatch_skip_letF {N : Comp} {K : EvalCtx} {ℓ : Label} {v : Val} :
    dispatch (Frame.letF N :: K) ℓ "raise" v = dispatch K ℓ "raise" v := by
  rw [dispatch_raise_eq, dispatch_raise_eq, splitAt_letF]
  cases splitAt K ℓ "raise" with
  | none => rfl
  | some t => obtain ⟨Kᵢ, h, Kₒ⟩ := t; rfl

theorem dispatch_skip_appF {w : Val} {K : EvalCtx} {ℓ : Label} {v : Val} :
    dispatch (Frame.appF w :: K) ℓ "raise" v = dispatch K ℓ "raise" v := by
  rw [dispatch_raise_eq, dispatch_raise_eq, splitAt_appF]
  cases splitAt K ℓ "raise" with
  | none => rfl
  | some t => obtain ⟨Kᵢ, h, Kₒ⟩ := t; rfl

/-- Skipping a NON-matching `handleF hh` frame (`hcatch : handlesOp hh .. = false`) — covers BOTH a
foreign `throws ℓ'` AND any `state ℓ' s` frame (state never catches `"raise"`, ADR-0025). -/
theorem dispatch_skip_handleF {hh : Handler} {K : EvalCtx} {ℓ : Label} {v : Val}
    (hcatch : handlesOp hh ℓ "raise" = false) :
    dispatch (Frame.handleF hh :: K) ℓ "raise" v = dispatch K ℓ "raise" v := by
  rw [dispatch_raise_eq, dispatch_raise_eq, splitAt_handleF_miss K hcatch]
  cases splitAt K ℓ "raise" with
  | none => rfl
  | some t => obtain ⟨Kᵢ, h, Kₒ⟩ := t; rfl

/-- A successful `dispatch` for `"raise"` returns a config whose focus is `ret v` (the catching
handler is `throws`, which aborts with the payload). -/
theorem dispatch_shape (K : EvalCtx) (ℓ : Label) (v : Val) {cfg' : Config} :
    dispatch K ℓ "raise" v = some cfg' → cfg'.2 = Comp.ret v := by
  rw [dispatch_raise_eq]
  cases splitAt K ℓ "raise" with
  | none => simp
  | some t => intro hd; simp only [Option.map_some, Option.some.injEq] at hd; rw [← hd]

/-- The DEEP-DISPATCH decomposition (PRESERVATION direction). GIVEN that `dispatch`
already found a handling frame (`dispatch K ℓ "raise" v = some (Kₒ, ret v)` — supplied
by the `Source.step cfg = some cfg'` hypothesis), the stack typing `HasStack K e_in C_in eo Co`
with `"raise"` in `ℓ`'s interface yields a typing of the outer stack: `Kₒ` carries a
focus `F q_h A` to a whole-program effect `eo' ≤ eo`. No `labelEff ℓ ≤ e_in` premise
is needed — `dispatch`'s success already locates the frame; we only read off its type.

Induction follows the `dispatch` recursion (`nil` is vacuous: `dispatch [] = none`).
At a matching `throws ℓ` frame the answer type matches (`opArg ℓ "raise"` injectivity);
at a skipped frame the result is the IH's. -/
theorem HasStack.dispatch_typed {K Kₒ : EvalCtx} {e_in : Eff} {C_in : CTy Eff Mult}
    {eo : Eff} {Co : CTy Eff Mult} {ℓ : Label} {A : VTy Eff Mult} {v : Val} :
    HasStack K e_in C_in eo Co →
    EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "raise" = some A →
    dispatch K ℓ "raise" v = some (Kₒ, Comp.ret v) →
    ∃ q_h eo', eo' ≤ eo ∧ HasStack Kₒ (⊥ : Eff) (CTy.F q_h A) eo' Co := by
  intro hK hopArg
  induction hK with
  | @nil e0 C0 =>
    intro hd; unfold dispatch at hd; rw [splitAt_nil, Option.bind_none] at hd; exact absurd hd (by simp)
  | @letF K N e₁ e₂ eo q qk A0 B Co hN hsub ih =>
    intro hd
    -- skip the letF frame: dispatch (letF :: K) equals dispatch K (same Kₒ/focus)
    rw [dispatch_skip_letF] at hd
    obtain ⟨q_h, eo', hleo, hsub'⟩ := ih hd
    exact ⟨q_h, eo', hleo, hsub'⟩
  | @appF K w e eo q A0 B Co hv hsub ih =>
    intro hd
    rw [dispatch_skip_appF] at hd
    obtain ⟨q_h, eo', hleo, hsub'⟩ := ih hd
    exact ⟨q_h, eo', hleo, hsub'⟩
  | @handleF K ℓ' e φ eo q Ah Co hraise hiface hdis hsub ih =>
    intro hd
    by_cases hℓ : ℓ' = ℓ
    · -- matching label: this frame catches "raise"; dispatch returned (K, ret v) here.
      subst hℓ
      have hcatch : handlesOp (Handler.throws ℓ') ℓ' "raise" = true := by simp [handlesOp]
      rw [dispatch_raise_eq, splitAt_handleF_hit K hcatch] at hd
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hd
      obtain ⟨hKeq, _⟩ := hd
      subst hKeq
      have hAeq : Ah = A := by
        rw [hraise] at hopArg; exact Option.some.inj hopArg
      subst hAeq
      -- the aborted `ret v` is at ⊥ ≤ φ; effect-weaken the outer substack
      obtain ⟨eo', hleo, hsub'⟩ := hsub.weaken_eff (bot_le)
      exact ⟨q, eo', hleo, hsub'⟩
    · -- non-matching label: dispatch skipped this frame
      have hcatch : handlesOp (Handler.throws ℓ') ℓ "raise" = false := by
        simp [handlesOp, hℓ]
      rw [dispatch_skip_handleF hcatch] at hd
      obtain ⟨q_h, eo', hleo, hsub'⟩ := ih hd
      exact ⟨q_h, eo', hleo, hsub'⟩
  | @stateF K ℓ' s e φ eo q Ah S Co hga hgr hpa hpr hif hs hdis hsub ih =>
    -- a state frame never catches "raise" (ADR-0025) ⇒ dispatch skips it; recurse.
    intro hd
    have hcatch : handlesOp (Handler.state ℓ' s) ℓ "raise" = false := by simp [handlesOp]
    rw [dispatch_skip_handleF hcatch] at hd
    obtain ⟨q_h, eo', hleo, hsub'⟩ := ih hd
    exact ⟨q_h, eo', hleo, hsub'⟩
  | @transactionF K ℓ' Θ e φ eo q Ah Co hna hnr hra hrr hwa hwr hif hcells hdis hsub ih =>
    -- a transaction frame never catches "raise" (ADR-0030) ⇒ dispatch skips it; recurse.
    intro hd
    have hcatch : handlesOp (Handler.transaction ℓ' Θ) ℓ "raise" = false := by simp [handlesOp]
    rw [dispatch_skip_handleF hcatch] at hd
    obtain ⟨q_h, eo', hleo, hsub'⟩ := ih hd
    exact ⟨q_h, eo', hleo, hsub'⟩

/-- DISPATCH must FIRE (PROGRESS direction). When the label is live in the running
effect and the whole-program effect is `⊥`, the stack MUST contain a handling frame:
`dispatch K ℓ "raise" v` returns `some _`. The label cannot escape to `⊥`
(`labelEff ℓ ≰ ⊥`). Skipping `letF`/`appF` keeps the label live; skipping a
non-matching `throws ℓ'` pushes it into the residual via `labelEff_sep`; a matching
`throws ℓ` catches `"raise"` (interface premise). `nil` is impossible: it would force
`labelEff ℓ ≤ ⊥`. -/
theorem HasStack.splitAt_fires {K : EvalCtx} {e_in : Eff} {C_in : CTy Eff Mult}
    {eo : Eff} {Co : CTy Eff Mult} {ℓ : Label} {op : OpId} {A : VTy Eff Mult}
    (hopArg : EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ op = some A) :
    HasStack K e_in C_in eo Co →
    ¬ (EffSig.labelEff (Eff := Eff) (Mult := Mult) ℓ ≤ eo) →
    EffSig.labelEff (Eff := Eff) (Mult := Mult) ℓ ≤ e_in →
    ∃ p, splitAt K ℓ op = some p := by
  -- The label is live and cannot escape to ⊥, so SOME frame discharges ℓ; that frame's interface
  -- (`opArg ℓ op = some A`) forces it to CATCH `op` (throws ⊳ raise / state ⊳ get,put — ADR-0025), so
  -- `splitAt` stops there. Foreign labels are pushed into the residual via `labelEff_sep`.
  intro hK
  induction hK with
  | nil =>
    intro hesc hlive; exact absurd hlive hesc
  | @letF K N e₁ e₂ eo q qk A0 B Co hN hsub ih =>
    intro hesc hlive
    obtain ⟨p, hp⟩ := ih hesc (le_trans hlive le_sup_left)
    exact ⟨_, by rw [splitAt_letF, hp]; rfl⟩
  | @appF K w e eo q A0 B Co hv hsub ih =>
    intro hesc hlive
    obtain ⟨p, hp⟩ := ih hesc hlive
    exact ⟨_, by rw [splitAt_appF, hp]; rfl⟩
  | @handleF K ℓ' e φ eo q Ah Co hraise hiface hdis hsub ih =>
    intro hesc hlive
    by_cases hℓ : ℓ' = ℓ
    · -- throws ℓ frame: it catches iff op = "raise"; the interface forces op = "raise" (since
      -- `opArg ℓ op = some A`, hiface gives op = "raise"), so it catches.
      subst hℓ
      have hop : op = "raise" := hiface op A hopArg
      subst hop
      have hcatch : handlesOp (Handler.throws ℓ') ℓ' "raise" = true := by simp [handlesOp]
      exact ⟨_, splitAt_handleF_hit K hcatch⟩
    · have hcatch : handlesOp (Handler.throws ℓ') ℓ op = false := by simp [handlesOp, hℓ]
      have hlive' : EffSig.labelEff (Eff := Eff) (Mult := Mult) ℓ ≤ φ :=
        EffSig.labelEff_sep ℓ ℓ' φ (le_trans hlive hdis) (fun h => hℓ h.symm)
      obtain ⟨p, hp⟩ := ih hesc hlive'
      exact ⟨_, by rw [splitAt_handleF_miss K hcatch, hp]; rfl⟩
  | @stateF K ℓ' s e φ eo q Ah S Co hga hgr hpa hpr hif hs hdis hsub ih =>
    intro hesc hlive
    by_cases hℓ : ℓ' = ℓ
    · -- state ℓ frame: it catches iff op ∈ {get,put}; the interface `hif` forces that, so it catches.
      subst hℓ
      have hcatch : handlesOp (Handler.state ℓ' s) ℓ' op = true := by
        rcases hif op A hopArg with hg | hp <;> subst_vars <;> simp [handlesOp]
      exact ⟨_, splitAt_handleF_hit K hcatch⟩
    · have hcatch : handlesOp (Handler.state ℓ' s) ℓ op = false := by simp [handlesOp, hℓ]
      have hlive' : EffSig.labelEff (Eff := Eff) (Mult := Mult) ℓ ≤ φ :=
        EffSig.labelEff_sep ℓ ℓ' φ (le_trans hlive hdis) (fun h => hℓ h.symm)
      obtain ⟨p, hp⟩ := ih hesc hlive'
      exact ⟨_, by rw [splitAt_handleF_miss K hcatch, hp]; rfl⟩
  | @transactionF K ℓ' Θ e φ eo q Ah Co hna hnr hra hrr hwa hwr hif hcells hdis hsub ih =>
    intro hesc hlive
    by_cases hℓ : ℓ' = ℓ
    · -- transaction ℓ frame: catches iff op ∈ {newTVar,readTVar,writeTVar}; `hif` forces it (ADR-0030).
      subst hℓ
      have hcatch : handlesOp (Handler.transaction ℓ' Θ) ℓ' op = true := by
        rcases hif op A hopArg with hn | hr | hw <;> subst_vars <;> simp [handlesOp]
      exact ⟨_, splitAt_handleF_hit K hcatch⟩
    · have hcatch : handlesOp (Handler.transaction ℓ' Θ) ℓ op = false := by simp [handlesOp, hℓ]
      have hlive' : EffSig.labelEff (Eff := Eff) (Mult := Mult) ℓ ≤ φ :=
        EffSig.labelEff_sep ℓ ℓ' φ (le_trans hlive hdis) (fun h => hℓ h.symm)
      obtain ⟨p, hp⟩ := ih hesc hlive'
      exact ⟨_, by rw [splitAt_handleF_miss K hcatch, hp]; rfl⟩

/-- `dispatchOn` always succeeds (every catching handler — throws or state — produces a resumed/
aborted config). So `dispatch K ℓ op v` succeeds iff `splitAt K ℓ op` does. -/
theorem dispatchOn_isSome (op : OpId) (v : Val) (p : EvalCtx × Handler × EvalCtx) :
    (dispatchOn op v p).isSome = true := by
  obtain ⟨Kᵢ, h, Kₒ⟩ := p
  -- every branch of `dispatchOn` (throws abort, state resume, the three stm resumes incl. the
  -- oom-on-malformed-payload fall-throughs) returns `some _`, so `isSome` holds. The transaction
  -- arm has nested `if`/`match` (ADR-0030), so split exhaustively then `rfl` each leaf.
  cases h <;> simp only [dispatchOn] <;>
    repeat' first | rfl | split

theorem dispatch_isSome_iff (K : EvalCtx) (ℓ : Label) (op : OpId) (v : Val) :
    (dispatch K ℓ op v).isSome = (splitAt K ℓ op).isSome := by
  show ((splitAt K ℓ op).bind (dispatchOn op v)).isSome = _
  cases splitAt K ℓ op with
  | none => rfl
  | some p => simp only [Option.bind_some]; exact dispatchOn_isSome op v p

/-! ### E.1b STATIC dispatch (ADR-0045 1b) — `staticSplit` reduction + decomposition

`Source.step` now resolves the handler by CAPABILITY (`staticSplit K cap`), not by label search. The
key structural fact: `staticSplit K cap = some (Kᵢ, h, Kₒ)` still yields `K = Kᵢ ++ handleF h :: Kₒ`
(`staticSplit_decomp`), so the throws/state/transaction RE-TYPING reduces to a label-BLIND
decomposition over that append — `HasStack.split_outer_typed` (throws abort) and
`HasStack.split_resume_typed` (state/transaction resume). These are SIMPLER than the `splitAt`-search
versions: no `handlesOp` test, no foreign-frame skip reasoning — the cap already located the frame, so
the induction is plain `Kᵢ`-list-recursion. -/

@[simp] theorem staticSplit_nil (cap : Nat) :
    staticSplit ([] : EvalCtx) cap = none := by cases cap <;> rfl

theorem staticSplit_letF (N : Comp) (K : EvalCtx) (cap : Nat) :
    staticSplit (Frame.letF N :: K) cap
      = (staticSplit K cap).map (fun (Kᵢ, h', Kₒ) => (Frame.letF N :: Kᵢ, h', Kₒ)) := by
  cases cap <;> rfl

theorem staticSplit_appF (w : Val) (K : EvalCtx) (cap : Nat) :
    staticSplit (Frame.appF w :: K) cap
      = (staticSplit K cap).map (fun (Kᵢ, h', Kₒ) => (Frame.appF w :: Kᵢ, h', Kₒ)) := by
  cases cap <;> rfl

theorem staticSplit_handleF_zero (h : Handler) (K : EvalCtx) :
    staticSplit (Frame.handleF h :: K) 0 = some ([], h, K) := rfl

theorem staticSplit_handleF_succ (h : Handler) (K : EvalCtx) (c : Nat) :
    staticSplit (Frame.handleF h :: K) (c + 1)
      = (staticSplit K c).map (fun (Kᵢ, h', Kₒ) => (Frame.handleF h :: Kᵢ, h', Kₒ)) := rfl

/-- **The decomposition.** A successful `staticSplit` certifies the stack is `Kᵢ ++ handleF h :: Kₒ`:
the cap walked `Kᵢ` (any frames) and stopped at `handleF h`, with `Kₒ` below. Induction on `K`/`cap`
mirroring `staticSplit`'s four clauses. This is the label-blind analogue of `splitAt`'s implicit
post-condition; everything downstream rides it. -/
theorem staticSplit_decomp : ∀ (K : EvalCtx) (cap : Nat) {Kᵢ Kₒ : EvalCtx} {h : Handler},
    staticSplit K cap = some (Kᵢ, h, Kₒ) → K = Kᵢ ++ Frame.handleF h :: Kₒ
  | [], cap, _, _, _ => by simp
  | (.handleF h₀ :: K), 0, Kᵢ, Kₒ, h => by
      rw [staticSplit_handleF_zero, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq]
      rintro ⟨rfl, rfl, rfl⟩; rfl
  | (.handleF h₀ :: K), (c + 1), Kᵢ, Kₒ, h => by
      rw [staticSplit_handleF_succ, Option.map_eq_some_iff]
      rintro ⟨⟨Kᵢ', h', Kₒ'⟩, hsp, heq⟩
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      rw [staticSplit_decomp K c hsp]; rfl
  | (.letF N :: K), cap, Kᵢ, Kₒ, h => by
      rw [staticSplit_letF, Option.map_eq_some_iff]
      rintro ⟨⟨Kᵢ', h', Kₒ'⟩, hsp, heq⟩
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      rw [staticSplit_decomp K cap hsp]; rfl
  | (.appF w :: K), cap, Kᵢ, Kₒ, h => by
      rw [staticSplit_appF, Option.map_eq_some_iff]
      rintro ⟨⟨Kᵢ', h', Kₒ'⟩, hsp, heq⟩
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      rw [staticSplit_decomp K cap hsp]; rfl

/-- `staticDispatch` succeeds iff `staticSplit` does (`dispatchOn` is total). -/
theorem staticDispatch_isSome_iff (K : EvalCtx) (cap : Nat) (op : OpId) (v : Val) :
    (staticDispatch K cap op v).isSome = (staticSplit K cap).isSome := by
  show ((staticSplit K cap).bind (dispatchOn op v)).isSome = _
  cases staticSplit K cap with
  | none => rfl
  | some p => simp only [Option.bind_some]; exact dispatchOn_isSome op v p

/-- `staticSplit` SUCCEEDS exactly when the cap RESOLVES (`CapResolves K cap`). The well-scopedness
predicate `CapResolves` is the `Prop` shadow of `staticSplit`'s `isSome`; both recurse identically. -/
theorem staticSplit_isSome_iff_capResolves : ∀ (K : EvalCtx) (cap : Nat),
    (staticSplit K cap).isSome = true ↔ CapResolves K cap
  | [], cap => by cases cap <;> simp [staticSplit, CapResolves]
  | (.handleF h :: K), 0 => by simp [staticSplit, CapResolves]
  | (.handleF h :: K), (c + 1) => by
      rw [staticSplit_handleF_succ, Option.isSome_map]; exact staticSplit_isSome_iff_capResolves K c
  | (.letF N :: K), cap => by
      rw [staticSplit_letF, Option.isSome_map]; exact staticSplit_isSome_iff_capResolves K cap
  | (.appF w :: K), cap => by
      rw [staticSplit_appF, Option.isSome_map]; exact staticSplit_isSome_iff_capResolves K cap

/-- `CapResolves K cap` ⟹ `staticSplit K cap` actually produces a triple. -/
theorem CapResolves.staticSplit_some {K : EvalCtx} {cap : Nat} (h : CapResolves K cap) :
    ∃ p, staticSplit K cap = some p :=
  Option.isSome_iff_exists.mp ((staticSplit_isSome_iff_capResolves K cap).mpr h)

/-- **THE KIND BRIDGE.** A KIND-correct cap (`CapResolvesKind K cap ℓ op`) forces the statically
resolved handler `h` to CATCH `(ℓ, op)` — exactly the `handlesOp h ℓ op = true` fact that dynamic
`splitAt` guaranteed by construction. This is the single lemma that lets the static path reuse all the
`splitAt`-era typed decomposition lemmas: feed them this `handlesOp` and the `staticSplit_decomp`
concatenation. Induction on `K`/`cap` mirrors `staticSplit`/`CapResolvesKind`'s shared recursion. -/
theorem staticSplit_kind : ∀ (K : EvalCtx) (cap : Nat) {Kᵢ Kₒ : EvalCtx} {h : Handler}
    {ℓ : Label} {op : OpId},
    staticSplit K cap = some (Kᵢ, h, Kₒ) → CapResolvesKind K cap ℓ op → handlesOp h ℓ op = true
  | [], cap, _, _, _, _, _ => by simp
  | (.handleF h₀ :: K), 0, Kᵢ, Kₒ, h, ℓ, op => by
      rw [staticSplit_handleF_zero, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq]
      rintro ⟨_, rfl, _⟩ hkind
      exact hkind
  | (.handleF h₀ :: K), (c + 1), Kᵢ, Kₒ, h, ℓ, op => by
      rw [staticSplit_handleF_succ, Option.map_eq_some_iff]
      rintro ⟨⟨Kᵢ', h', Kₒ'⟩, hsp, heq⟩ hkind
      simp only [Prod.mk.injEq] at heq
      obtain ⟨_, rfl, _⟩ := heq
      exact staticSplit_kind K c hsp hkind
  | (.letF N :: K), cap, Kᵢ, Kₒ, h, ℓ, op => by
      rw [staticSplit_letF, Option.map_eq_some_iff]
      rintro ⟨⟨Kᵢ', h', Kₒ'⟩, hsp, heq⟩ hkind
      simp only [Prod.mk.injEq] at heq
      obtain ⟨_, rfl, _⟩ := heq
      exact staticSplit_kind K cap hsp hkind
  | (.appF w :: K), cap, Kᵢ, Kₒ, h, ℓ, op => by
      rw [staticSplit_appF, Option.map_eq_some_iff]
      rintro ⟨⟨Kᵢ', h', Kₒ'⟩, hsp, heq⟩ hkind
      simp only [Prod.mk.injEq] at heq
      obtain ⟨_, rfl, _⟩ := heq
      exact staticSplit_kind K cap hsp hkind

/-- If `dispatch` succeeds for `(ℓ, op)` over a well-typed stack, then `op` is `"raise"`, `"get"`, or
`"put"` (ADR-0025): the catching frame is either a `throws ℓ` (interface `{raise}`) or a `state ℓ`
(interface `{get,put}`); both interface premises constrain `op`. -/
theorem HasStack.dispatch_op_handled {K : EvalCtx} {e_in : Eff} {C_in : CTy Eff Mult}
    {eo : Eff} {Co : CTy Eff Mult} {ℓ : Label} {op : OpId} {A : VTy Eff Mult} :
    HasStack K e_in C_in eo Co →
    EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ op = some A →
    (splitAt K ℓ op).isSome = true →
      op = "raise" ∨ op = "get" ∨ op = "put"
        ∨ op = "newTVar" ∨ op = "readTVar" ∨ op = "writeTVar" := by
  intro hK hopArg
  induction hK with
  | nil => intro hd; simp [splitAt] at hd
  | @letF K N e₁ e₂ eo q qk A0 B Co hN hsub ih =>
    intro hd; rw [splitAt_letF, Option.isSome_map] at hd; exact ih hd
  | @appF K w e eo q A0 B Co hv hsub ih =>
    intro hd; rw [splitAt_appF, Option.isSome_map] at hd; exact ih hd
  | @handleF K ℓ' e φ eo q Ah Co hraise hiface hdis hsub ih =>
    intro hd
    by_cases hℓ : ℓ' = ℓ
    · subst hℓ; exact Or.inl (hiface op A hopArg)
    · have hcatch : handlesOp (Handler.throws ℓ') ℓ op = false := by simp [handlesOp, hℓ]
      rw [splitAt_handleF_miss K hcatch, Option.isSome_map] at hd
      exact ih hd
  | @stateF K ℓ' s e φ eo q Ah S Co hga hgr hpa hpr hif hs hdis hsub ih =>
    intro hd
    by_cases hℓ : ℓ' = ℓ
    · subst hℓ; exact Or.inr (Or.imp_right Or.inl (hif op A hopArg))
    · have hcatch : handlesOp (Handler.state ℓ' s) ℓ op = false := by simp [handlesOp, hℓ]
      rw [splitAt_handleF_miss K hcatch, Option.isSome_map] at hd
      exact ih hd
  | @transactionF K ℓ' Θ e φ eo q Ah Co hna hnr hra hrr hwa hwr hif hcells hdis hsub ih =>
    intro hd
    by_cases hℓ : ℓ' = ℓ
    · -- transaction ℓ frame: `hif` forces op ∈ {newTVar,readTVar,writeTVar} (ADR-0030).
      subst hℓ
      rcases hif op A hopArg with hn | hr | hw
      · exact Or.inr (Or.inr (Or.inr (Or.inl hn)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hr))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hw))))
    · have hcatch : handlesOp (Handler.transaction ℓ' Θ) ℓ op = false := by simp [handlesOp, hℓ]
      rw [splitAt_handleF_miss K hcatch, Option.isSome_map] at hd
      exact ih hd

/-- The STATE-KEEPING dispatch decomposition (PRESERVATION direction, ADR-0025). The resumptive
analogue of `dispatch_typed`: where `throws` DISCARDS the captured continuation `Kᵢ` (aborting to
`Kₒ`), `state` KEEPS `Kᵢ` and re-installs a deep `state ℓ s'` frame, so the resumed stack is
`Kᵢ ++ handleF (state ℓ s') :: Kₒ`. GIVEN the original `HasStack K e (F q B) eo Co` and that `splitAt`
located a `state ℓ s` frame for `(ℓ, op)`, we re-type the resumed stack at the SAME focus type
`F q B` and an outer effect `eo' ≤ eo`, for ANY new closed state `s'` (`HasVTy [] [] s' S`).

The induction follows the `splitAt` recursion (mirrors `dispatch_typed`): each skipped frame
(`letF`/`appF`/non-matching `handleF`) is rebuilt onto the front of the resumed stack via its own
`HasStack` constructor (so `Kᵢ` is reconstructed frame-by-frame), and at the matching `state ℓ`
frame the reinstalled `stateF` constructor splices `s'` in front of the original outer substack.
`nil` is vacuous (`splitAt [] = none`). Foreign `state ℓ'`/`throws ℓ'` frames are skipped exactly as
in `dispatch_op_handled`. The resumed focus effect is the original `e`; the caller plugs the closed
`ret s'` (effect `⊥ ≤ e`) via `weaken_eff`. -/
theorem HasStack.dispatch_state_typed {K Kᵢ Kₒ : EvalCtx} {e : Eff}
    {C : CTy Eff Mult} {S : VTy Eff Mult} {eo : Eff} {Co : CTy Eff Mult}
    {ℓ : Label} {op : OpId} {s s' : Val} :
    HasStack K e C eo Co →
    EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "get" = some S →
    (op = "get" ∨ op = "put") →
    HasVTy [] [] s' S →
    splitAt K ℓ op = some (Kᵢ, Handler.state ℓ s, Kₒ) →
    ∃ eo', eo' ≤ eo ∧
      HasStack (Kᵢ ++ Frame.handleF (Handler.state ℓ s') :: Kₒ) e C eo' Co := by
  intro hK hgetRes hop hs'
  induction hK generalizing Kᵢ Kₒ s with
  | @nil e0 C0 => intro hd; simp [splitAt] at hd
  | @letF K N e₁ e₂ eo q qk A0 B0 Co hN hsub ih =>
    intro hd
    rw [splitAt_letF, Option.map_eq_some_iff] at hd
    obtain ⟨⟨Kᵢ', h', Kₒ'⟩, hsp, heq⟩ := hd
    simp only [Prod.mk.injEq] at heq
    obtain ⟨hKᵢ, hh, hKₒ⟩ := heq
    subst hKᵢ; subst hh; subst hKₒ
    obtain ⟨eo', hleo, hsub'⟩ := ih hsp
    exact ⟨eo', hleo, by simpa using HasStack.letF hN hsub'⟩
  | @appF K w e eo q A0 B0 Co hv hsub ih =>
    intro hd
    rw [splitAt_appF, Option.map_eq_some_iff] at hd
    obtain ⟨⟨Kᵢ', h', Kₒ'⟩, hsp, heq⟩ := hd
    simp only [Prod.mk.injEq] at heq
    obtain ⟨hKᵢ, hh, hKₒ⟩ := heq
    subst hKᵢ; subst hh; subst hKₒ
    obtain ⟨eo', hleo, hsub'⟩ := ih hsp
    exact ⟨eo', hleo, by simpa using HasStack.appF hv hsub'⟩
  | @handleF K ℓ' e φ eo q A0 Co hraise hiface hdis hsub ih =>
    intro hd
    -- a `throws ℓ'` frame never catches get/put (op ∈ {get,put}); dispatch skips it.
    have hcatch : handlesOp (Handler.throws ℓ') ℓ op = false := by
      rcases hop with h | h <;> subst h <;> simp [handlesOp]
    rw [splitAt_handleF_miss K hcatch, Option.map_eq_some_iff] at hd
    obtain ⟨⟨Kᵢ', h', Kₒ'⟩, hsp, heq⟩ := hd
    simp only [Prod.mk.injEq] at heq
    obtain ⟨hKᵢ, hh, hKₒ⟩ := heq
    subst hKᵢ; subst hh; subst hKₒ
    obtain ⟨eo', hleo, hsub'⟩ := ih hsp
    exact ⟨eo', hleo, by simpa using HasStack.handleF hraise hiface hdis hsub'⟩
  | @stateF K ℓ' s₀ e φ eo q A0 S0 Co hga hgr hpa hpr hif hs hdis hsub ih =>
    intro hd
    by_cases hℓ : ℓ' = ℓ
    · -- matching state frame: this is the split point. Reinstall `state ℓ s'` over the same `Kₒ`.
      subst hℓ
      have hcatch : handlesOp (Handler.state ℓ' s₀) ℓ' op = true := by
        rcases hop with h | h <;> subst h <;> simp [handlesOp]
      rw [splitAt_handleF_hit K hcatch, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hd
      obtain ⟨hKᵢ, hstateEq, hKₒ⟩ := hd
      subst hKᵢ; subst hKₒ
      -- the matching frame's stored state has type `S0`; `s'` must inhabit the SAME `S0`.
      -- `opRes ℓ' "get" = some S0` (frame) and `= some S` (hyp) ⇒ S = S0.
      have hSeq : S = S0 := by rw [hgr] at hgetRes; exact (Option.some.inj hgetRes).symm
      subst hSeq
      refine ⟨eo, le_refl _, ?_⟩
      simpa using HasStack.stateF hga hgr hpa hpr hif hs' hdis hsub
    · -- foreign state frame (different label): dispatch skips it.
      have hcatch : handlesOp (Handler.state ℓ' s₀) ℓ op = false := by simp [handlesOp, hℓ]
      rw [splitAt_handleF_miss K hcatch, Option.map_eq_some_iff] at hd
      obtain ⟨⟨Kᵢ', h', Kₒ'⟩, hsp, heq⟩ := hd
      simp only [Prod.mk.injEq] at heq
      obtain ⟨hKᵢ, hh, hKₒ⟩ := heq
      subst hKᵢ; subst hh; subst hKₒ
      obtain ⟨eo', hleo, hsub'⟩ := ih hsp
      exact ⟨eo', hleo, by simpa using HasStack.stateF hga hgr hpa hpr hif hs hdis hsub'⟩
  | @transactionF K ℓ' Θ e φ eo q A0 Co hna hnr hra hrr hwa hwr hif hcells hdis hsub ih =>
    -- a transaction frame never catches get/put (op ∈ {get,put}) ⇒ dispatch skips it; recurse.
    intro hd
    have hcatch : handlesOp (Handler.transaction ℓ' Θ) ℓ op = false := by
      rcases hop with h | h <;> subst h <;> simp [handlesOp]
    rw [splitAt_handleF_miss K hcatch, Option.map_eq_some_iff] at hd
    obtain ⟨⟨Kᵢ', h', Kₒ'⟩, hsp, heq⟩ := hd
    simp only [Prod.mk.injEq] at heq
    obtain ⟨hKᵢ, hh, hKₒ⟩ := heq
    subst hKᵢ; subst hh; subst hKₒ
    obtain ⟨eo', hleo, hsub'⟩ := ih hsp
    exact ⟨eo', hleo, by simpa using
      HasStack.transactionF hna hnr hra hrr hwa hwr hif hcells hdis hsub'⟩

/-- The stored state at the matched `state ℓ s` frame is CLOSED of type `S = opRes ℓ "get"`
(ADR-0025 grade discipline: the CK focus is always closed, so the threaded state is too). Same
`splitAt`-recursion induction as `dispatch_state_typed`; only the matched frame's `hs`/`hgr` are
read off. Supplies the get-resume's reinstall typing (`ret s` re-stores the same closed `s`). -/
theorem HasStack.splitAt_state_closed {K Kᵢ Kₒ : EvalCtx} {e : Eff}
    {C : CTy Eff Mult} {eo : Eff} {Co : CTy Eff Mult} {ℓ : Label} {op : OpId} {s : Val} :
    HasStack K e C eo Co →
    (op = "get" ∨ op = "put") →
    splitAt K ℓ op = some (Kᵢ, Handler.state ℓ s, Kₒ) →
    ∃ S, EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "get" = some S
      ∧ EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "put" = some S
      ∧ EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "put" = some VTy.unit
      ∧ HasVTy [] [] s S := by
  intro hK hop
  induction hK generalizing Kᵢ Kₒ s with
  | @nil e0 C0 => intro hd; simp [splitAt] at hd
  | @letF K N e₁ e₂ eo q qk A0 B0 Co hN hsub ih =>
    intro hd
    rw [splitAt_letF, Option.map_eq_some_iff] at hd
    obtain ⟨⟨Kᵢ', h', Kₒ'⟩, hsp, heq⟩ := hd
    simp only [Prod.mk.injEq] at heq
    obtain ⟨_, hh, _⟩ := heq; subst hh
    exact ih hsp
  | @appF K w e eo q A0 B0 Co hv hsub ih =>
    intro hd
    rw [splitAt_appF, Option.map_eq_some_iff] at hd
    obtain ⟨⟨Kᵢ', h', Kₒ'⟩, hsp, heq⟩ := hd
    simp only [Prod.mk.injEq] at heq
    obtain ⟨_, hh, _⟩ := heq; subst hh
    exact ih hsp
  | @handleF K ℓ' e φ eo q A0 Co hraise hiface hdis hsub ih =>
    intro hd
    have hcatch : handlesOp (Handler.throws ℓ') ℓ op = false := by
      rcases hop with h | h <;> subst h <;> simp [handlesOp]
    rw [splitAt_handleF_miss K hcatch, Option.map_eq_some_iff] at hd
    obtain ⟨⟨Kᵢ', h', Kₒ'⟩, hsp, heq⟩ := hd
    simp only [Prod.mk.injEq] at heq
    obtain ⟨_, hh, _⟩ := heq; subst hh
    exact ih hsp
  | @stateF K ℓ' s₀ e φ eo q A0 S0 Co hga hgr hpa hpr hif hs hdis hsub ih =>
    intro hd
    by_cases hℓ : ℓ' = ℓ
    · subst hℓ
      have hcatch : handlesOp (Handler.state ℓ' s₀) ℓ' op = true := by
        rcases hop with h | h <;> subst h <;> simp [handlesOp]
      rw [splitAt_handleF_hit K hcatch, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hd
      obtain ⟨_, hstateEq, _⟩ := hd
      -- `state ℓ' s₀ = state ℓ' s` ⇒ s = s₀
      rw [Handler.state.injEq] at hstateEq
      obtain ⟨_, hseq⟩ := hstateEq; subst hseq
      exact ⟨S0, hgr, hpa, hpr, hs⟩
    · have hcatch : handlesOp (Handler.state ℓ' s₀) ℓ op = false := by simp [handlesOp, hℓ]
      rw [splitAt_handleF_miss K hcatch, Option.map_eq_some_iff] at hd
      obtain ⟨⟨Kᵢ', h', Kₒ'⟩, hsp, heq⟩ := hd
      simp only [Prod.mk.injEq] at heq
      obtain ⟨_, hh, _⟩ := heq; subst hh
      exact ih hsp
  | @transactionF K ℓ' Θ e φ eo q A0 Co hna hnr hra hrr hwa hwr hif hcells hdis hsub ih =>
    -- transaction never catches get/put ⇒ foreign-skip (the matched frame is elsewhere).
    intro hd
    have hcatch : handlesOp (Handler.transaction ℓ' Θ) ℓ op = false := by
      rcases hop with h | h <;> subst h <;> simp [handlesOp]
    rw [splitAt_handleF_miss K hcatch, Option.map_eq_some_iff] at hd
    obtain ⟨⟨Kᵢ', h', Kₒ'⟩, hsp, heq⟩ := hd
    simp only [Prod.mk.injEq] at heq
    obtain ⟨_, hh, _⟩ := heq; subst hh
    exact ih hsp

/-- For `op ∈ {get, put}`, any catching frame found by `splitAt` is a `state ℓ` handler at the
SAME label `ℓ`: `throws` catches only `raise` (`handlesOp (throws ..) ℓ get/put = false`), and a
`state ℓ'` catches `get`/`put` only when `ℓ' = ℓ`. So `splitAt`'s handler component is `state ℓ _`. -/
theorem splitAt_getput_state {K : EvalCtx} {ℓ : Label} {op : OpId} {Kᵢ Kₒ : EvalCtx} {h : Handler}
    (hop : op = "get" ∨ op = "put") :
    splitAt K ℓ op = some (Kᵢ, h, Kₒ) → ∃ s, h = Handler.state ℓ s := by
  induction K generalizing Kᵢ Kₒ h with
  | nil => intro hd; simp [splitAt] at hd
  | cons fr K ih =>
    cases fr with
    | letF N =>
      intro hd; rw [splitAt_letF, Option.map_eq_some_iff] at hd
      obtain ⟨⟨Kᵢ', h', Kₒ'⟩, hsp, heq⟩ := hd
      simp only [Prod.mk.injEq] at heq
      exact heq.2.1 ▸ ih hsp
    | appF w =>
      intro hd; rw [splitAt_appF, Option.map_eq_some_iff] at hd
      obtain ⟨⟨Kᵢ', h', Kₒ'⟩, hsp, heq⟩ := hd
      simp only [Prod.mk.injEq] at heq
      exact heq.2.1 ▸ ih hsp
    | handleF hh =>
      intro hd
      by_cases hcatch : handlesOp hh ℓ op = true
      · rw [splitAt_handleF_hit K hcatch, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hd
        obtain ⟨_, hheq, _⟩ := hd
        subst hheq
        cases hh with
        | throws ℓ' => rcases hop with h | h <;> subst h <;> simp [handlesOp] at hcatch
        | state ℓ' s =>
          -- catches get/put ⇒ ℓ' = ℓ
          rcases hop with h | h <;> subst h <;>
            (simp only [handlesOp, Bool.and_eq_true, decide_eq_true_eq] at hcatch
             obtain ⟨hℓ', _⟩ := hcatch; subst hℓ'; exact ⟨s, rfl⟩)
        | transaction ℓ' Θ =>
          -- a transaction frame never catches get/put ⇒ contradiction.
          rcases hop with h | h <;> subst h <;> simp [handlesOp] at hcatch
      · simp only [Bool.not_eq_true] at hcatch
        rw [splitAt_handleF_miss K hcatch, Option.map_eq_some_iff] at hd
        obtain ⟨⟨Kᵢ', h', Kₒ'⟩, hsp, heq⟩ := hd
        simp only [Prod.mk.injEq] at heq
        exact heq.2.1 ▸ ih hsp

/-- The TRANSACTION resume-typing lemma (ADR-0030 preservation), the multi-cell generalization of
`dispatch_state_typed`: where `state` reinstalls `state ℓ s'`, a `transaction` reinstalls
`transaction ℓ Θ'` over the KEPT inner prefix `Kᵢ`, so the resumed stack is
`Kᵢ ++ handleF (transaction ℓ Θ') :: Kₒ`. GIVEN the original `HasStack K e (F q A) eo Co`, that
`splitAt` located a `transaction ℓ Θ` frame for `(ℓ, op)`, the stm interface signatures, and that
the NEW heap `Θ'` is all-cells-closed of type `S` (`∀ cell ∈ Θ', HasVTy [] [] cell S`), re-type the
resumed stack at the SAME focus type `F q A`. The induction follows the `splitAt` recursion exactly
as `dispatch_state_typed`: skipped frames are rebuilt frame-by-frame; at the matching `transaction ℓ`
frame the reinstalled `transactionF` constructor splices `Θ'` in. The interface premises (passed in)
re-discharge the new frame's interface obligations (they are facts about `ℓ`'s `EffSig`, invariant
under the heap change). -/
theorem HasStack.dispatch_transaction_typed {K Kᵢ Kₒ : EvalCtx} {e : Eff}
    {C : CTy Eff Mult} {S TVarRef : VTy Eff Mult} {eo : Eff} {Co : CTy Eff Mult}
    {ℓ : Label} {op : OpId} {Θ Θ' : Store} :
    HasStack K e C eo Co →
    EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "newTVar" = some S →
    EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "newTVar" = some TVarRef →
    EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "readTVar" = some TVarRef →
    EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "readTVar" = some S →
    EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "writeTVar" = some (VTy.prod TVarRef S) →
    EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "writeTVar" = some VTy.unit →
    (∀ op B, EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ op = some B →
      op = "newTVar" ∨ op = "readTVar" ∨ op = "writeTVar") →
    (op = "newTVar" ∨ op = "readTVar" ∨ op = "writeTVar") →
    (∀ cell ∈ Θ', HasVTy [] [] cell S) →
    splitAt K ℓ op = some (Kᵢ, Handler.transaction ℓ Θ, Kₒ) →
    ∃ eo', eo' ≤ eo ∧
      HasStack (Kᵢ ++ Frame.handleF (Handler.transaction ℓ Θ') :: Kₒ) e C eo' Co := by
  intro hK hna hnr hra hrr hwa hwr hiface hop hcells'
  induction hK generalizing Kᵢ Kₒ Θ with
  | @nil e0 C0 => intro hd; simp [splitAt] at hd
  | @letF K N e₁ e₂ eo q qk A0 B0 Co hN hsub ih =>
    intro hd
    rw [splitAt_letF, Option.map_eq_some_iff] at hd
    obtain ⟨⟨Kᵢ', h', Kₒ'⟩, hsp, heq⟩ := hd
    simp only [Prod.mk.injEq] at heq
    obtain ⟨hKᵢ, hh, hKₒ⟩ := heq
    subst hKᵢ; subst hh; subst hKₒ
    obtain ⟨eo', hleo, hsub'⟩ := ih hsp
    exact ⟨eo', hleo, by simpa using HasStack.letF hN hsub'⟩
  | @appF K w e eo q A0 B0 Co hv hsub ih =>
    intro hd
    rw [splitAt_appF, Option.map_eq_some_iff] at hd
    obtain ⟨⟨Kᵢ', h', Kₒ'⟩, hsp, heq⟩ := hd
    simp only [Prod.mk.injEq] at heq
    obtain ⟨hKᵢ, hh, hKₒ⟩ := heq
    subst hKᵢ; subst hh; subst hKₒ
    obtain ⟨eo', hleo, hsub'⟩ := ih hsp
    exact ⟨eo', hleo, by simpa using HasStack.appF hv hsub'⟩
  | @handleF K ℓ' e φ eo q A0 Co hraise hifaceT hdis hsub ih =>
    intro hd
    -- a `throws ℓ'` frame never catches an stm op; dispatch skips it.
    have hcatch : handlesOp (Handler.throws ℓ') ℓ op = false := by
      rcases hop with h | h | h <;> subst h <;> simp [handlesOp]
    rw [splitAt_handleF_miss K hcatch, Option.map_eq_some_iff] at hd
    obtain ⟨⟨Kᵢ', h', Kₒ'⟩, hsp, heq⟩ := hd
    simp only [Prod.mk.injEq] at heq
    obtain ⟨hKᵢ, hh, hKₒ⟩ := heq
    subst hKᵢ; subst hh; subst hKₒ
    obtain ⟨eo', hleo, hsub'⟩ := ih hsp
    exact ⟨eo', hleo, by simpa using HasStack.handleF hraise hifaceT hdis hsub'⟩
  | @stateF K ℓ' s₀ e φ eo q A0 S0 Co hga hgr hpa hpr hif hs hdis hsub ih =>
    intro hd
    -- a `state ℓ'` frame never catches an stm op (interface is get/put); dispatch skips it.
    have hcatch : handlesOp (Handler.state ℓ' s₀) ℓ op = false := by
      rcases hop with h | h | h <;> subst h <;> simp [handlesOp]
    rw [splitAt_handleF_miss K hcatch, Option.map_eq_some_iff] at hd
    obtain ⟨⟨Kᵢ', h', Kₒ'⟩, hsp, heq⟩ := hd
    simp only [Prod.mk.injEq] at heq
    obtain ⟨hKᵢ, hh, hKₒ⟩ := heq
    subst hKᵢ; subst hh; subst hKₒ
    obtain ⟨eo', hleo, hsub'⟩ := ih hsp
    exact ⟨eo', hleo, by simpa using HasStack.stateF hga hgr hpa hpr hif hs hdis hsub'⟩
  | @transactionF K ℓ' Θ₀ e φ eo q A0 Co hna0 hnr0 hra0 hrr0 hwa0 hwr0 hif hcells hdis hsub ih =>
    intro hd
    by_cases hℓ : ℓ' = ℓ
    · -- matching transaction frame: the split point. Reinstall `transaction ℓ Θ'` over the same `Kₒ`.
      subst hℓ
      have hcatch : handlesOp (Handler.transaction ℓ' Θ₀) ℓ' op = true := by
        rcases hop with h | h | h <;> subst h <;> simp [handlesOp]
      rw [splitAt_handleF_hit K hcatch, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hd
      obtain ⟨hKᵢ, htxEq, hKₒ⟩ := hd
      subst hKᵢ; subst hKₒ
      -- The new heap `Θ'`'s cells inhabit `S` (helper's generic premise); the int-pinned frame stores
      -- `int` (ADR-0030 amendment). Tie `S = int` from `opArg newTVar`, so `hcells' : ∀ cell, .. int`.
      have hSeq : S = VTy.int := by rw [hna0] at hna; exact (Option.some.inj hna).symm
      subst hSeq
      refine ⟨eo, le_refl _, ?_⟩
      simpa using HasStack.transactionF hna0 hnr0 hra0 hrr0 hwa0 hwr0 hif hcells' hdis hsub
    · -- foreign transaction frame (different label): dispatch skips it.
      have hcatch : handlesOp (Handler.transaction ℓ' Θ₀) ℓ op = false := by simp [handlesOp, hℓ]
      rw [splitAt_handleF_miss K hcatch, Option.map_eq_some_iff] at hd
      obtain ⟨⟨Kᵢ', h', Kₒ'⟩, hsp, heq⟩ := hd
      simp only [Prod.mk.injEq] at heq
      obtain ⟨hKᵢ, hh, hKₒ⟩ := heq
      subst hKᵢ; subst hh; subst hKₒ
      obtain ⟨eo', hleo, hsub'⟩ := ih hsp
      exact ⟨eo', hleo, by simpa using
        HasStack.transactionF hna0 hnr0 hra0 hrr0 hwa0 hwr0 hif hcells hdis hsub'⟩

/-- The matched `transaction ℓ Θ` frame found by `splitAt` for an stm op carries a CLOSED heap (all
cells closed of type `int`) and the full monomorphic-`int` stm interface signatures (ADR-0030
int-pinned amendment, the multi-cell analogue of `splitAt_state_closed`). Read off the matched
`transactionF` frame's `hcells`/interface fields; the int-pinning makes the signatures concrete. -/
theorem HasStack.splitAt_transaction_store {K Kᵢ Kₒ : EvalCtx} {e : Eff}
    {C : CTy Eff Mult} {eo : Eff} {Co : CTy Eff Mult} {ℓ : Label} {op : OpId} {Θ : Store} :
    HasStack K e C eo Co →
    (op = "newTVar" ∨ op = "readTVar" ∨ op = "writeTVar") →
    splitAt K ℓ op = some (Kᵢ, Handler.transaction ℓ Θ, Kₒ) →
      EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "newTVar" = some VTy.int
      ∧ EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "newTVar" = some VTy.int
      ∧ EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "readTVar" = some VTy.int
      ∧ EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "readTVar" = some VTy.int
      ∧ EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ "writeTVar" = some (VTy.prod VTy.int VTy.int)
      ∧ EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ "writeTVar" = some VTy.unit
      ∧ (∀ op B, EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ op = some B →
          op = "newTVar" ∨ op = "readTVar" ∨ op = "writeTVar")
      ∧ (∀ cell ∈ Θ, HasVTy [] [] cell (VTy.int : VTy Eff Mult)) := by
  intro hK hop
  induction hK generalizing Kᵢ Kₒ Θ with
  | @nil e0 C0 => intro hd; simp [splitAt] at hd
  | @letF K N e₁ e₂ eo q qk A0 B0 Co hN hsub ih =>
    intro hd
    rw [splitAt_letF, Option.map_eq_some_iff] at hd
    obtain ⟨⟨Kᵢ', h', Kₒ'⟩, hsp, heq⟩ := hd
    simp only [Prod.mk.injEq] at heq
    obtain ⟨_, hh, _⟩ := heq; subst hh
    exact ih hsp
  | @appF K w e eo q A0 B0 Co hv hsub ih =>
    intro hd
    rw [splitAt_appF, Option.map_eq_some_iff] at hd
    obtain ⟨⟨Kᵢ', h', Kₒ'⟩, hsp, heq⟩ := hd
    simp only [Prod.mk.injEq] at heq
    obtain ⟨_, hh, _⟩ := heq; subst hh
    exact ih hsp
  | @handleF K ℓ' e φ eo q A0 Co hraise hiface hdis hsub ih =>
    intro hd
    have hcatch : handlesOp (Handler.throws ℓ') ℓ op = false := by
      rcases hop with h | h | h <;> subst h <;> simp [handlesOp]
    rw [splitAt_handleF_miss K hcatch, Option.map_eq_some_iff] at hd
    obtain ⟨⟨Kᵢ', h', Kₒ'⟩, hsp, heq⟩ := hd
    simp only [Prod.mk.injEq] at heq
    obtain ⟨_, hh, _⟩ := heq; subst hh
    exact ih hsp
  | @stateF K ℓ' s₀ e φ eo q A0 S0 Co hga hgr hpa hpr hif hs hdis hsub ih =>
    intro hd
    have hcatch : handlesOp (Handler.state ℓ' s₀) ℓ op = false := by
      rcases hop with h | h | h <;> subst h <;> simp [handlesOp]
    rw [splitAt_handleF_miss K hcatch, Option.map_eq_some_iff] at hd
    obtain ⟨⟨Kᵢ', h', Kₒ'⟩, hsp, heq⟩ := hd
    simp only [Prod.mk.injEq] at heq
    obtain ⟨_, hh, _⟩ := heq; subst hh
    exact ih hsp
  | @transactionF K ℓ' Θ₀ e φ eo q A0 Co hna hnr hra hrr hwa hwr hif hcells hdis hsub ih =>
    intro hd
    by_cases hℓ : ℓ' = ℓ
    · subst hℓ
      have hcatch : handlesOp (Handler.transaction ℓ' Θ₀) ℓ' op = true := by
        rcases hop with h | h | h <;> subst h <;> simp [handlesOp]
      rw [splitAt_handleF_hit K hcatch, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hd
      obtain ⟨_, htxEq, _⟩ := hd
      rw [Handler.transaction.injEq] at htxEq
      obtain ⟨_, hΘeq⟩ := htxEq; subst hΘeq
      -- the int-pinned frame stores `int` for both cell type and TVarRef (ADR-0030 amendment).
      exact ⟨hna, hnr, hra, hrr, hwa, hwr, hif, hcells⟩
    · have hcatch : handlesOp (Handler.transaction ℓ' Θ₀) ℓ op = false := by simp [handlesOp, hℓ]
      rw [splitAt_handleF_miss K hcatch, Option.map_eq_some_iff] at hd
      obtain ⟨⟨Kᵢ', h', Kₒ'⟩, hsp, heq⟩ := hd
      simp only [Prod.mk.injEq] at heq
      obtain ⟨_, hh, _⟩ := heq; subst hh
      exact ih hsp

/-- For an stm op, any catching frame found by `splitAt` is a `transaction ℓ` handler at the SAME
label (the analogue of `splitAt_getput_state`): `throws`/`state` never catch stm ops; a foreign
`transaction ℓ'` catches only when `ℓ' = ℓ`. -/
theorem splitAt_stm_transaction {K : EvalCtx} {ℓ : Label} {op : OpId} {Kᵢ Kₒ : EvalCtx}
    {h : Handler} (hop : op = "newTVar" ∨ op = "readTVar" ∨ op = "writeTVar") :
    splitAt K ℓ op = some (Kᵢ, h, Kₒ) → ∃ Θ, h = Handler.transaction ℓ Θ := by
  induction K generalizing Kᵢ Kₒ h with
  | nil => intro hd; simp [splitAt] at hd
  | cons fr K ih =>
    cases fr with
    | letF N =>
      intro hd; rw [splitAt_letF, Option.map_eq_some_iff] at hd
      obtain ⟨⟨Kᵢ', h', Kₒ'⟩, hsp, heq⟩ := hd
      simp only [Prod.mk.injEq] at heq
      exact heq.2.1 ▸ ih hsp
    | appF w =>
      intro hd; rw [splitAt_appF, Option.map_eq_some_iff] at hd
      obtain ⟨⟨Kᵢ', h', Kₒ'⟩, hsp, heq⟩ := hd
      simp only [Prod.mk.injEq] at heq
      exact heq.2.1 ▸ ih hsp
    | handleF hh =>
      intro hd
      by_cases hcatch : handlesOp hh ℓ op = true
      · rw [splitAt_handleF_hit K hcatch, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hd
        obtain ⟨_, hheq, _⟩ := hd
        subst hheq
        cases hh with
        | throws ℓ' => rcases hop with h | h | h <;> subst h <;> simp [handlesOp] at hcatch
        | state ℓ' s => rcases hop with h | h | h <;> subst h <;> simp [handlesOp] at hcatch
        | transaction ℓ' Θ =>
          rcases hop with h | h | h <;> subst h <;>
            (simp only [handlesOp, Bool.and_eq_true, decide_eq_true_eq] at hcatch
             obtain ⟨hℓ', _⟩ := hcatch; subst hℓ'; exact ⟨Θ, rfl⟩)
      · simp only [Bool.not_eq_true] at hcatch
        rw [splitAt_handleF_miss K hcatch, Option.map_eq_some_iff] at hd
        obtain ⟨⟨Kᵢ', h', Kₒ'⟩, hsp, heq⟩ := hd
        simp only [Prod.mk.injEq] at heq
        exact heq.2.1 ▸ ih hsp

/-- CLOSED FORM for `"newTVar"` dispatch (ADR-0030 alloc resume): allocation NEVER ooms — it appends
the closed initial value `v` and returns the fresh index `vint Θ.length`. The catching handler is a
`transaction ℓ Θ`, resumed with the extended heap `Θ ++ [v]` over the kept inner prefix. -/
theorem dispatch_new_shape {K : EvalCtx} {ℓ : Label} {v : Val} {cfg' : Config} :
    dispatch K ℓ "newTVar" v = some cfg' →
    ∃ Kᵢ Θ Kₒ, splitAt K ℓ "newTVar" = some (Kᵢ, Handler.transaction ℓ Θ, Kₒ)
      ∧ cfg' = (Kᵢ ++ Frame.handleF (Handler.transaction ℓ (Θ ++ [v])) :: Kₒ,
                Comp.ret (Val.vint Θ.length)) := by
  unfold dispatch
  cases hsp : splitAt K ℓ "newTVar" with
  | none => simp
  | some t =>
    obtain ⟨Kᵢ, h, Kₒ⟩ := t
    obtain ⟨Θ, hh⟩ := splitAt_stm_transaction (Or.inl rfl) hsp
    subst hh
    simp only [Option.bind_some, dispatchOn, beq_self_eq_true, if_true, Option.some.injEq]
    intro hd; exact ⟨Kᵢ, Θ, Kₒ, rfl, hd.symm⟩

/-- CLOSED FORM for `"readTVar"` dispatch (ADR-0030 read resume, TOTAL store): the catching handler is
a `transaction ℓ Θ`, resumed with the UNCHANGED heap and focus `ret (Θ.getD ((tvarIdx v).getD 0)
(vint 0))` — the `getD` default makes read total (never ooms), so this is the SINGLE shape. -/
theorem dispatch_read_shape {K : EvalCtx} {ℓ : Label} {v : Val} {cfg' : Config} :
    dispatch K ℓ "readTVar" v = some cfg' →
    ∃ Kᵢ Θ Kₒ, splitAt K ℓ "readTVar" = some (Kᵢ, Handler.transaction ℓ Θ, Kₒ)
      ∧ cfg' = (Kᵢ ++ Frame.handleF (Handler.transaction ℓ Θ) :: Kₒ,
                Comp.ret (Θ.getD ((tvarIdx v).getD 0) (Val.vint 0))) := by
  unfold dispatch
  cases hsp : splitAt K ℓ "readTVar" with
  | none => simp
  | some t =>
    obtain ⟨Kᵢ, h, Kₒ⟩ := t
    obtain ⟨Θ, hh⟩ := splitAt_stm_transaction (Or.inr (Or.inl rfl)) hsp
    subst hh
    simp only [Option.bind_some, dispatchOn, show ("readTVar" == "newTVar") = false by decide,
      Bool.false_eq_true, if_false, beq_self_eq_true, if_true, Option.some.injEq]
    intro hd; exact ⟨Kᵢ, Θ, Kₒ, rfl, hd.symm⟩

/-- CLOSED FORM for `"writeTVar"` dispatch (ADR-0030 write resume, TOTAL store): the catching handler
is a `transaction ℓ Θ`, resumed with focus `ret unit` and a heap Θ' that is EITHER `storeSet Θ i w`
(a `pair (vint i) w` payload — the in-bounds/no-op write, `storeSet`=`List.set` total) OR Θ unchanged
(a malformed payload). The disjunction is read off below; `w` is exactly the pair's second component. -/
theorem dispatch_write_shape {K : EvalCtx} {ℓ : Label} {v : Val} {cfg' : Config} :
    dispatch K ℓ "writeTVar" v = some cfg' →
    ∃ Kᵢ Θ Θ' Kₒ, splitAt K ℓ "writeTVar" = some (Kᵢ, Handler.transaction ℓ Θ, Kₒ)
      ∧ (Θ' = Θ ∨ ∃ iv w, v = Val.pair iv w ∧ Θ' = storeSet Θ ((tvarIdx iv).getD 0) w)
      ∧ cfg' = (Kᵢ ++ Frame.handleF (Handler.transaction ℓ Θ') :: Kₒ, Comp.ret Val.vunit) := by
  unfold dispatch
  cases hsp : splitAt K ℓ "writeTVar" with
  | none => simp
  | some t =>
    obtain ⟨Kᵢ, h, Kₒ⟩ := t
    obtain ⟨Θ, hh⟩ := splitAt_stm_transaction (Or.inr (Or.inr rfl)) hsp
    subst hh
    simp only [Option.bind_some, dispatchOn, show ("writeTVar" == "newTVar") = false by decide,
      show ("writeTVar" == "readTVar") = false by decide, Bool.false_eq_true, if_false]
    cases v with
    | pair iv w =>
      simp only [Option.some.injEq]
      intro hd
      exact ⟨Kᵢ, Θ, storeSet Θ ((tvarIdx iv).getD 0) w, Kₒ, rfl,
        Or.inr ⟨iv, w, rfl, rfl⟩, hd.symm⟩
    | vunit => simp only [Option.some.injEq]; intro hd; exact ⟨Kᵢ, Θ, Θ, Kₒ, rfl, Or.inl rfl, hd.symm⟩
    | vint n => simp only [Option.some.injEq]; intro hd; exact ⟨Kᵢ, Θ, Θ, Kₒ, rfl, Or.inl rfl, hd.symm⟩
    | vvar i => simp only [Option.some.injEq]; intro hd; exact ⟨Kᵢ, Θ, Θ, Kₒ, rfl, Or.inl rfl, hd.symm⟩
    | vthunk M => simp only [Option.some.injEq]; intro hd; exact ⟨Kᵢ, Θ, Θ, Kₒ, rfl, Or.inl rfl, hd.symm⟩
    | inl a => simp only [Option.some.injEq]; intro hd; exact ⟨Kᵢ, Θ, Θ, Kₒ, rfl, Or.inl rfl, hd.symm⟩
    | inr a => simp only [Option.some.injEq]; intro hd; exact ⟨Kᵢ, Θ, Θ, Kₒ, rfl, Or.inl rfl, hd.symm⟩
    | fold a => simp only [Option.some.injEq]; intro hd; exact ⟨Kᵢ, Θ, Θ, Kₒ, rfl, Or.inl rfl, hd.symm⟩

/-! ### E.3′ all-or-nothing atomicity — the rung-3 VERIFIED moat law (ADR-0030)

The correctness theorem ADR-0030 promised — `abort ⟹ store unchanged (modulo fresh allocations)` —
discharged as a VERIFIED law (climbing the ADR-0026 ladder above rung 2's `plausible`-tested stack
laws). The mechanism is the throws-discard machinery (ADR-0023): an abort is a `raise` whose dispatch
DROPS the captured continuation `Kᵢ` — and the transaction frame, with its written heap `Θ`, lives in
that dropped `Kᵢ`. `dispatch_raise_eq` already proves the abort config is `(Kₒ, ret v)`, reading ONLY
the OUTER context `Kₒ` and the payload `v`. So no write the transaction performed (any heap `Θ`) can
reach the outer observer: the observable abort result is HEAP-INDEPENDENT. This is exactly Harris's
(ATHROW) discard rule and opacity's single-threaded degenerate case (ADR-0030 §"Why this model"). -/

/-- A `transaction` frame never catches `raise` (its interface is the three stm ops), so abort
dispatch SKIPS it — for ANY label, op-irrelevant heap `Θ`, and exception label `ℓₑ`. -/
theorem transaction_no_catch_raise (ℓ ℓₑ : Label) (Θ : Store) :
    handlesOp (Handler.transaction ℓ Θ) ℓₑ "raise" = false := by
  simp [handlesOp]

/-- **ALL-OR-NOTHING (verified, ADR-0030).** Aborting a transaction body via `raise ℓₑ` produces a
configuration that is INDEPENDENT of the heap threaded inside the transaction frame: for any two heaps
`Θ Θ'` (the "before" heap and any "after writes" heap), the abort dispatch through a stack carrying a
`transaction ℓ Θ` (resp. `Θ'`) frame yields the SAME config. The writes are discarded with `Kᵢ`; the
outer observer at `Kₒ` cannot distinguish them. (`storeSet`-driven write-deltas live entirely in the
`Θ` slot, so heap-independence ⟹ write-delta-invisibility — the moat law.) Allocations are likewise
discarded with the frame, so this is "store unchanged" in the strongest sense: the post-abort config
is the SAME as if the transaction had never run, save the payload `v`. -/
theorem all_or_nothing_abort (K : EvalCtx) (ℓ ℓₑ : Label) (Θ Θ' : Store) (v : Val) :
    dispatch (Frame.handleF (Handler.transaction ℓ Θ) :: K) ℓₑ "raise" v
      = dispatch (Frame.handleF (Handler.transaction ℓ Θ') :: K) ℓₑ "raise" v := by
  -- abort dispatch reads only `(splitAt _).2.2 = Kₒ` + `v` (`dispatch_raise_eq`); a transaction frame
  -- is SKIPPED (it never catches raise), and skipping is a `cons`-map that leaves `Kₒ` untouched.
  rw [dispatch_raise_eq, dispatch_raise_eq,
      splitAt_handleF_miss K (transaction_no_catch_raise ℓ ℓₑ Θ),
      splitAt_handleF_miss K (transaction_no_catch_raise ℓ ℓₑ Θ')]
  -- both sides now map over the SAME `splitAt K ℓₑ "raise"`; the abort projection `(·.2.2, ret v)`
  -- ignores the `Kᵢ` component the two `cons`-maps differ in, so the results are definitionally equal.
  cases splitAt K ℓₑ "raise" with
  | none => rfl
  | some t => obtain ⟨Kᵢ, h, Kₒ⟩ := t; rfl

/-- CLOSED FORM for `"get"` dispatch (ADR-0025 resume): the catching handler is a `state ℓ s`, which
RESUMES with the stored `s` over the KEPT inner prefix, reinstalling itself: the resumed config is
`(Kᵢ ++ handleF (state ℓ s) :: Kₒ, ret s)`. -/
theorem dispatch_get_shape {K : EvalCtx} {ℓ : Label} {v : Val} {cfg' : Config} :
    dispatch K ℓ "get" v = some cfg' →
    ∃ Kᵢ s Kₒ, splitAt K ℓ "get" = some (Kᵢ, Handler.state ℓ s, Kₒ)
      ∧ cfg' = (Kᵢ ++ Frame.handleF (Handler.state ℓ s) :: Kₒ, Comp.ret s) := by
  unfold dispatch
  cases hsp : splitAt K ℓ "get" with
  | none => simp
  | some t =>
    obtain ⟨Kᵢ, h, Kₒ⟩ := t
    obtain ⟨s, hs⟩ := splitAt_getput_state (Or.inl rfl) hsp
    subst hs
    simp only [Option.bind_some, dispatchOn, beq_self_eq_true, if_true, Option.some.injEq]
    intro hd; exact ⟨Kᵢ, s, Kₒ, rfl, hd.symm⟩

/-- CLOSED FORM for `"put"` dispatch (ADR-0025 resume): the catching `state ℓ s` STORES the payload
`v` (state ← v), returns `unit` over the kept inner prefix, reinstalling `state ℓ v`: the resumed
config is `(Kᵢ ++ handleF (state ℓ v) :: Kₒ, ret unit)`. -/
theorem dispatch_put_shape {K : EvalCtx} {ℓ : Label} {v : Val} {cfg' : Config} :
    dispatch K ℓ "put" v = some cfg' →
    ∃ Kᵢ s Kₒ, splitAt K ℓ "put" = some (Kᵢ, Handler.state ℓ s, Kₒ)
      ∧ cfg' = (Kᵢ ++ Frame.handleF (Handler.state ℓ v) :: Kₒ, Comp.ret Val.vunit) := by
  unfold dispatch
  cases hsp : splitAt K ℓ "put" with
  | none => simp
  | some t =>
    obtain ⟨Kᵢ, h, Kₒ⟩ := t
    obtain ⟨s, hs⟩ := splitAt_getput_state (Or.inr rfl) hsp
    subst hs
    simp only [Option.bind_some, dispatchOn, show ("put" == "get") = false by decide,
      Bool.false_eq_true, if_false, Option.some.injEq]
    intro hd; exact ⟨Kᵢ, s, Kₒ, rfl, hd.symm⟩

/-! ### E.1c label-blind concat decomposition (the STATIC re-typing core, ADR-0045 1b)

Given `HasStack (Kᵢ ++ handleF h :: Kₒ) e C eo Co`, peel `Kᵢ` frame-by-frame to expose the boundary
`handleF h` frame's typing and re-type either the OUTER `Kₒ` (throws abort) or the RESUMED stack
`Kᵢ ++ handleF h' :: Kₒ` (state/transaction resume). These are LABEL-BLIND (`Kᵢ` is rebuilt by its own
`HasStack` constructors regardless of what it contains) and are the static analogues of
`dispatch_typed` / `dispatch_state_typed` / `dispatch_transaction_typed` — simpler, because the cap
already located the boundary, so no `handlesOp`-driven search/skip recursion is needed. -/

/-- THROWS abort re-typing (static). The boundary handler is a `throws ℓ'` frame; type the outer `Kₒ`
at the throws answer type `A_h = opArg ℓ' "raise"`, whole-program effect `eo' ≤ eo`. Induct on `Kᵢ`. -/
theorem HasStack.concat_throws_typed {Kᵢ Kₒ : EvalCtx} {ℓ' : Label} {e : Eff} {C : CTy Eff Mult}
    {eo : Eff} {Co : CTy Eff Mult} :
    HasStack (Kᵢ ++ Frame.handleF (Handler.throws ℓ') :: Kₒ) e C eo Co →
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
    | @handleF _ ℓ'' _ φ _ q A _ hraise hiface hle hsub => exact ih hsub
    | @stateF _ ℓ'' s₀ _ φ _ q A S₀ _ hga hgr hpa hpr hif hs hle hsub => exact ih hsub
    | @transactionF _ ℓ'' Θ₀ _ φ _ q A _ hna hnr hra hrr hwa hwr hif hcells hle hsub => exact ih hsub

/-- STATE resume re-typing (static). The boundary handler is a `state ℓ' s` frame; reinstall a
`state ℓ' s'` frame (any closed `s' : S`, `S = opRes ℓ' "get"`) over the same `Kᵢ`/`Kₒ`, re-typing the
resumed stack at the SAME `e C`. Each `Kᵢ` frame is rebuilt by `cases hK` (so the exact constructor —
incl. nested `state`/`transaction` frames — is preserved, not lost to `handleAny_inv`). This is the
WellCapped-under-resume core: the resumed stack has the IDENTICAL frame skeleton (only `s↦s'` at one
`handleF`), which is why the static cap of every buried perform still resolves. -/
theorem HasStack.concat_state_resume {Kᵢ Kₒ : EvalCtx} {ℓ' : Label} {s s' : Val} {S : VTy Eff Mult}
    {e : Eff} {C : CTy Eff Mult} {eo : Eff} {Co : CTy Eff Mult} :
    HasStack (Kᵢ ++ Frame.handleF (Handler.state ℓ' s) :: Kₒ) e C eo Co →
    EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ' "get" = some S →
    HasVTy [] [] s' S →
    ∃ eo', eo' ≤ eo
      ∧ HasStack (Kᵢ ++ Frame.handleF (Handler.state ℓ' s') :: Kₒ) e C eo' Co := by
  intro hK hgetRes hs'
  induction Kᵢ generalizing e C with
  | nil =>
    simp only [List.nil_append] at hK ⊢
    cases hK with
    | @stateF _ _ _ _ φ _ q A S0 _ hga hgr hpa hpr hif hs hle hsub =>
      have hSeq : S = S0 := by rw [hgr] at hgetRes; exact (Option.some.inj hgetRes).symm
      subst hSeq
      exact ⟨eo, le_refl _, HasStack.stateF hga hgr hpa hpr hif hs' hle hsub⟩
  | cons fr Kᵢ ih =>
    simp only [List.cons_append] at hK ⊢
    cases hK with
    | @letF _ _ _ e₂ _ q qk A B _ hN hsub =>
      obtain ⟨eo', hleo, hsub'⟩ := ih hsub
      exact ⟨eo', hleo, HasStack.letF hN hsub'⟩
    | @appF _ _ _ _ q A B _ hv hsub =>
      obtain ⟨eo', hleo, hsub'⟩ := ih hsub
      exact ⟨eo', hleo, HasStack.appF hv hsub'⟩
    | @handleF _ ℓ'' _ φ _ q A _ hraise hiface hle hsub =>
      obtain ⟨eo', hleo, hsub'⟩ := ih hsub
      exact ⟨eo', hleo, HasStack.handleF hraise hiface hle hsub'⟩
    | @stateF _ ℓ'' s₀ _ φ _ q A S₀ _ hga hgr hpa hpr hif hs hle hsub =>
      obtain ⟨eo', hleo, hsub'⟩ := ih hsub
      exact ⟨eo', hleo, HasStack.stateF hga hgr hpa hpr hif hs hle hsub'⟩
    | @transactionF _ ℓ'' Θ₀ _ φ _ q A _ hna hnr hra hrr hwa hwr hif hcells hle hsub =>
      obtain ⟨eo', hleo, hsub'⟩ := ih hsub
      exact ⟨eo', hleo, HasStack.transactionF hna hnr hra hrr hwa hwr hif hcells hle hsub'⟩

/-- TRANSACTION resume re-typing (static), the multi-cell analogue of `concat_state_resume`. The
boundary `transaction ℓ' Θ` frame is reinstalled as `transaction ℓ' Θ'` (any all-`int`-cells heap `Θ'`)
over the same `Kᵢ`/`Kₒ`. The interface premises (facts about `ℓ'`'s `EffSig`, heap-invariant) are
passed in to re-discharge the reinstalled frame. -/
theorem HasStack.concat_transaction_resume {Kᵢ Kₒ : EvalCtx} {ℓ' : Label} {Θ Θ' : Store}
    {e : Eff} {C : CTy Eff Mult} {eo : Eff} {Co : CTy Eff Mult} :
    HasStack (Kᵢ ++ Frame.handleF (Handler.transaction ℓ' Θ) :: Kₒ) e C eo Co →
    (∀ cell ∈ Θ', HasVTy [] [] cell (VTy.int : VTy Eff Mult)) →
    ∃ eo', eo' ≤ eo
      ∧ HasStack (Kᵢ ++ Frame.handleF (Handler.transaction ℓ' Θ') :: Kₒ) e C eo' Co := by
  intro hK hcells'
  induction Kᵢ generalizing e C with
  | nil =>
    simp only [List.nil_append] at hK ⊢
    cases hK with
    | @transactionF _ _ _ _ φ _ q A _ hna hnr hra hrr hwa hwr hif hcells hle hsub =>
      exact ⟨eo, le_refl _, HasStack.transactionF hna hnr hra hrr hwa hwr hif hcells' hle hsub⟩
  | cons fr Kᵢ ih =>
    simp only [List.cons_append] at hK ⊢
    cases hK with
    | @letF _ _ _ e₂ _ q qk A B _ hN hsub =>
      obtain ⟨eo', hleo, hsub'⟩ := ih hsub
      exact ⟨eo', hleo, HasStack.letF hN hsub'⟩
    | @appF _ _ _ _ q A B _ hv hsub =>
      obtain ⟨eo', hleo, hsub'⟩ := ih hsub
      exact ⟨eo', hleo, HasStack.appF hv hsub'⟩
    | @handleF _ ℓ'' _ φ _ q A _ hraise hiface hle hsub =>
      obtain ⟨eo', hleo, hsub'⟩ := ih hsub
      exact ⟨eo', hleo, HasStack.handleF hraise hiface hle hsub'⟩
    | @stateF _ ℓ'' s₀ _ φ _ q A S₀ _ hga hgr hpa hpr hif hs hle hsub =>
      obtain ⟨eo', hleo, hsub'⟩ := ih hsub
      exact ⟨eo', hleo, HasStack.stateF hga hgr hpa hpr hif hs hle hsub'⟩
    | @transactionF _ ℓ'' Θ₀ _ φ _ q A _ hna hnr hra hrr hwa hwr hif hcells hle hsub =>
      obtain ⟨eo', hleo, hsub'⟩ := ih hsub
      exact ⟨eo', hleo, HasStack.transactionF hna hnr hra hrr hwa hwr hif hcells hle hsub'⟩

/-- The boundary `state ℓ' s` frame (located by the cap) carries a CLOSED stored state of type
`S = opRes ℓ' "get"` and the get/put interface signatures — read off by peeling `Kᵢ` to the boundary
(`cases hK`). The static analogue of `splitAt_state_closed`, over the concat. -/
theorem HasStack.concat_state_closed {Kᵢ Kₒ : EvalCtx} {ℓ' : Label} {s : Val} {e : Eff}
    {C : CTy Eff Mult} {eo : Eff} {Co : CTy Eff Mult} :
    HasStack (Kᵢ ++ Frame.handleF (Handler.state ℓ' s) :: Kₒ) e C eo Co →
    ∃ S, EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ' "get" = some S
      ∧ EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ' "put" = some S
      ∧ EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ' "put" = some VTy.unit
      ∧ HasVTy [] [] s S := by
  induction Kᵢ generalizing e C with
  | nil =>
    intro hK; simp only [List.nil_append] at hK
    cases hK with
    | @stateF _ _ _ _ φ _ q A S0 _ hga hgr hpa hpr hif hs hle hsub => exact ⟨S0, hgr, hpa, hpr, hs⟩
  | cons fr Kᵢ ih =>
    intro hK; simp only [List.cons_append] at hK
    cases hK with
    | @letF _ _ _ e₂ _ q qk A B _ hN hsub => exact ih hsub
    | @appF _ _ _ _ q A B _ hv hsub => exact ih hsub
    | @handleF _ ℓ'' _ φ _ q A _ hraise hiface hle hsub => exact ih hsub
    | @stateF _ ℓ'' s₀ _ φ _ q A S₀ _ hga hgr hpa hpr hif hs hle hsub => exact ih hsub
    | @transactionF _ ℓ'' Θ₀ _ φ _ q A _ hna hnr hra hrr hwa hwr hif hcells hle hsub => exact ih hsub

/-- The boundary `transaction ℓ' Θ` frame (located by the cap) carries a CLOSED all-`int` heap and the
monomorphic-`int` stm interface signatures — read off by peeling `Kᵢ` to the boundary. The static
analogue of `splitAt_transaction_store`, over the concat. -/
theorem HasStack.concat_transaction_store {Kᵢ Kₒ : EvalCtx} {ℓ' : Label} {Θ : Store} {e : Eff}
    {C : CTy Eff Mult} {eo : Eff} {Co : CTy Eff Mult} :
    HasStack (Kᵢ ++ Frame.handleF (Handler.transaction ℓ' Θ) :: Kₒ) e C eo Co →
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
    | @transactionF _ _ _ _ φ _ q A _ hna hnr hra hrr hwa hwr hif hcells hle hsub =>
      exact ⟨hna, hnr, hra, hrr, hwa, hwr, hif, hcells⟩
  | cons fr Kᵢ ih =>
    intro hK; simp only [List.cons_append] at hK
    cases hK with
    | @letF _ _ _ e₂ _ q qk A B _ hN hsub => exact ih hsub
    | @appF _ _ _ _ q A B _ hv hsub => exact ih hsub
    | @handleF _ ℓ'' _ φ _ q A _ hraise hiface hle hsub => exact ih hsub
    | @stateF _ ℓ'' s₀ _ φ _ q A S₀ _ hga hgr hpa hpr hif hs hle hsub => exact ih hsub
    | @transactionF _ ℓ'' Θ₀ _ φ _ q A _ hna hnr hra hrr hwa hwr hif hcells hle hsub => exact ih hsub

theorem preservation_proof
    {cfg cfg' : Config} {eo : Eff} {Co : CTy Eff Mult} :
    HasConfig cfg eo Co → Source.step cfg = some cfg' →
    ∃ eo', eo' ≤ eo ∧ HasConfig cfg' eo' Co := by
  -- ADR-0045 R1: `HasConfig = HasConfigTy ∧ LWConfig`. `hlw : LWConfig cfg` carries the cap-invariant;
  -- each case must re-establish `LWConfig cfg'` alongside the typing core. The DECISIVE handleF-ret
  -- case (where `WellCapped` failed) goes through BY CONSTRUCTION (`LWConfig.handleF_ret`). The
  -- remaining cases' `LWConfig` re-establishment is the post-checkpoint grind (LWT.subst + dispatch
  -- threading); marked `sorry` with `-- R1-TODO` and NOT yet discharged (honest red).
  rintro ⟨⟨e, C, hfocus, hstack⟩, hlw⟩ hstep
  obtain ⟨K, M⟩ := cfg
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
        refine ⟨eo, le_refl _, ⟨e₂, B, hsubst, hsub⟩, ?_⟩
        -- R1-TODO: LWConfig (K', subst v N) from the letF stack + focus — needs LWT.subst.
        sorry
      | appF w => simp [Source.step] at hstep
      | handleF h =>
        -- REDUCE handler-return = identity (both throws and state, ADR-0023 Q6 / ADR-0025).
        obtain ⟨φ, q', A', hCeq, eo₀, hleo₀, hsub⟩ := hstack.handleAny_inv
        simp only [Source.step, Option.some.injEq] at hstep
        subst hstep
        rw [CTy.F.injEq] at hCeq; obtain ⟨hqq, hAA⟩ := hCeq; subst hAA
        obtain ⟨eo', hleo, hsub'⟩ := hsub.weaken_eff (bot_le)
        -- ★ THE DECISIVE CASE — handleF-ret preservation BY CONSTRUCTION (R1). ★
        exact ⟨eo', le_trans hleo hleo₀,
          ⟨⊥, CTy.F q' A, HasCTy.ret hwv (by simp [hsmul_eq_smul, GradeVec.smul]), hsub'⟩,
          LWConfig.handleF_ret h K' v hlw⟩
  | perform cap ℓ op v =>
    -- DISPATCH. Classify the performed op by the catching handler's interface.
    --
    -- ★ R1 CHECKPOINT SCOPE — the perform DISPATCH case is the post-checkpoint grind, NOT the crux. ★
    -- The B1 progress wall is DISCHARGED (see `progress_proof`): `LWConfig` now supplies
    -- `CapResolvesKind`, so `staticDispatch` resolves. The remaining preservation obligation here is to
    -- TYPE the resolved reduct.
    -- This is the B1/B3 wall now UNBLOCKED by `hlw`: `LWConfig` gives `CapResolvesKind K cap ℓ op`
    -- (the focus `LWT (handlersOf K) _ (perform …)` unfolds to it), so `staticSplit K cap` resolves and
    -- the static-dispatch reduct can be typed by re-deriving the 6-path resume-typing (the `splitAt`-era
    -- body, preserved in git @ b59242c) onto `staticSplit`/`CapResolvesKind`. The TYPING core
    -- (`concat_*`, `dispatch_*_typed`) is GREEN; the rewiring is `dispatch K ℓ op v` ↦ `staticDispatch
    -- K cap op v` + the matching `staticSplit_decomp`/`staticSplit_kind` (also GREEN). LWConfig
    -- preservation across resume rides `capResolves_skel_inv` (resume swaps only a boundary payload).
    -- Deferred to the post-checkpoint STD grind per the lead's checkpoint instruction; honest `sorry`.
    sorry
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
    -- R1-TODO: LWConfig (letF N :: K, M) from LWConfig (K, letC M N) — PUSH-letF, structural.
    exact ⟨eo, le_refl _, ⟨φ₁, CTy.F q1 A, hM, HasStack.letF hN hstack⟩, by sorry⟩
  | app M w =>
    -- PUSH app
    simp only [Source.step, Option.some.injEq] at hstep
    subst hstep
    obtain ⟨γ₁, γ₂, q, A, hγ, hM, hw⟩ := hfocus.app_inv
    have hγ₁ : γ₁ = [] := by have := hM.length_eq; simpa using this
    have hγ₂ : γ₂ = [] := by have := hw.length_eq; simpa using this
    subst hγ₁; subst hγ₂
    -- R1-TODO: LWConfig (appF w :: K, M) — PUSH-appF, structural.
    exact ⟨eo, le_refl _, ⟨e, CTy.arr q A C, hM, HasStack.appF hw hstack⟩, by sorry⟩
  | handle h M =>
    -- PUSH handle: push the handler frame; both throws and state are typable (ADR-0025).
    cases h with
    | throws ℓ =>
      simp only [Source.step, Option.some.injEq] at hstep
      subst hstep
      obtain ⟨e_body, q, A, hC, hraise, hiface, hM, hle⟩ := hfocus.handleThrows_inv
      subst hC
      -- R1-TODO: LWConfig (handleF (throws ℓ) :: K, M) — PUSH-handle.
      exact ⟨eo, le_refl _, ⟨e_body, CTy.F q A, hM, HasStack.handleF hraise hiface hle hstack⟩, by sorry⟩
    | state ℓ s =>
      simp only [Source.step, Option.some.injEq] at hstep
      subst hstep
      obtain ⟨e_body, q, S, A, hC, hga, hgr, hpa, hpr, hif, hs, hM, hle⟩ := hfocus.handleState_inv
      subst hC
      exact ⟨eo, le_refl _,
        ⟨e_body, CTy.F q A, hM, HasStack.stateF hga hgr hpa hpr hif hs hle hstack⟩, by sorry⟩
    | transaction ℓ Θ =>
      -- PUSH transaction: push the frame (ADR-0030); fully typable like state.
      simp only [Source.step, Option.some.injEq] at hstep
      subst hstep
      obtain ⟨e_body, q, A, hC, hna, hnr, hra, hrr, hwa, hwr, hif, hcells, hM, hle⟩ :=
        hfocus.handleTransaction_inv
      subst hC
      exact ⟨eo, le_refl _,
        ⟨e_body, CTy.F q A, hM,
          HasStack.transactionF hna hnr hra hrr hwa hwr hif hcells hle hstack⟩, by sorry⟩
  | force w =>
    -- PUSH force: focus typing forces w = vthunk M
    rcases hfocus.force_inv.U_inv with ⟨MT, hweq, hMT⟩ | ⟨i, hweq, hget, _⟩
    · subst hweq
      simp only [Source.step, Option.some.injEq] at hstep
      subst hstep
      -- R1-TODO: LWConfig (K, MT) from force (vthunk MT) — the thunk body's LWT at the ambient ctx.
      exact ⟨eo, le_refl _, ⟨e, C, hMT, hstack⟩, by sorry⟩
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
      | handleF h =>
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
        -- R1-TODO: LWConfig (K', subst w M) — β-redex, needs LWT.subst.
        exact ⟨eo, le_refl _, ⟨e, B, hsubst, hsub⟩, by sorry⟩
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
      -- R1-TODO: LWConfig (K, subst a N₁) — case-inl, needs LWT.subst.
      exact ⟨eo, le_refl _, ⟨e, C, hsubst, hstack⟩, by sorry⟩
    · subst hveq
      simp only [Source.step, Option.some.injEq] at hstep
      subst hstep
      have hsubst := subst_value_proof q ha hN₂
      simp only [hsmul_eq_smul, GradeVec.smul_nil, hadd_eq_add,
        GradeVec.add_nil_left] at hsubst
      -- R1-TODO: LWConfig (K, subst a N₂) — case-inr, needs LWT.subst.
      exact ⟨eo, le_refl _, ⟨e, C, hsubst, hstack⟩, by sorry⟩
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
    -- R1-TODO: LWConfig (K, subst a (subst (shift b) N)) — split, needs LWT.subst (double).
    exact ⟨eo, le_refl _, ⟨e, C, hsubst_outer, hstack⟩, by sorry⟩
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
    -- R1-TODO: LWConfig (K, ret a) — unfold, structural (a is a sub-value of the focus).
    exact ⟨eo, le_refl _, ⟨⊥, CTy.F 1 (VTy.unrollMu A), HasCTy.ret ha (by simp [hsmul_eq_smul]), hstack⟩, by sorry⟩
  | oom => exact absurd hfocus HasCTy.oom_untypable
  | wrong s => exact absurd hfocus HasCTy.wrong_untypable

/-! ### E.3 progress (config level, ADR-0023) -/

theorem progress_proof
    {cfg : Config} {q : Mult} {A : VTy Eff Mult} :
    HasConfig cfg ⊥ (CTy.F q A) →
    isReturnConfig cfg ∨ ∃ cfg', Source.step cfg = some cfg' := by
  -- ADR-0045 R1: `hlw : LWConfig cfg` carries the cap-invariant — it is what UNBLOCKS the B1 progress
  -- wall (the perform case): the focus `LWT (handlersOf K) _ (perform …)` gives `CapResolvesKind`,
  -- so `staticSplit` resolves and `staticDispatch` STEPS (cf. spike `perform_progress`).
  rintro ⟨⟨e, C, hfocus, hstack⟩, hlw⟩
  obtain ⟨K, M⟩ := cfg
  cases M with
  | letC M N => exact Or.inr ⟨(Frame.letF N :: K, M), by simp [Source.step]⟩
  | app M w => exact Or.inr ⟨(Frame.appF w :: K, M), by simp [Source.step]⟩
  | handle h M => exact Or.inr ⟨(Frame.handleF h :: K, M), by simp [Source.step]⟩
  | force w =>
    rcases hfocus.force_inv.U_inv with ⟨MT, hweq, hMT⟩ | ⟨i, hweq, hget, _⟩
    · subst hweq; exact Or.inr ⟨(K, MT), by simp [Source.step]⟩
    · simp at hget
  | perform cap ℓ op v =>
    -- ★ B1 WALL DISCHARGED (ADR-0045 R1) — `LWConfig` supplies the missing `CapResolvesKind`. ★
    -- Under static dispatch the config STEPS iff `staticSplit K cap` succeeds. The frozen `HasConfig`
    -- premise NOW carries `LWConfig` (R1): its focus part `LWT (handlersOf K) _ (perform …)` unfolds to
    -- `CapResolvesKind (handlersOf K) cap ℓ op`, which (cap reads only handler kinds —
    -- `CapResolvesKind_handlersOf`) gives `CapResolvesKind K cap ℓ op`, hence `staticSplit K cap` is
    -- `some` (`staticSplit_isSome_of_resolvesKind`), hence `staticDispatch` is `some`
    -- (`staticDispatch_isSome_iff`) — the config STEPS. This is the spike's `perform_progress`, now the
    -- kernel progress case. The cap-IRRELEVANCE of typing no longer matters: cap-scoping rides
    -- `LWConfig`, not `HasCTy`.
    have hres0 : CapResolvesKind (handlersOf K) cap ℓ op := by
      simp only [LWConfig, LWT] at hlw; exact hlw.1.1
    have hres : CapResolvesKind K cap ℓ op := (CapResolvesKind_handlersOf K cap ℓ op).mp hres0
    have hsome : (staticSplit K cap).isSome := staticSplit_isSome_of_resolvesKind K cap ℓ op hres
    have hd : (staticDispatch K cap op v).isSome = true := by
      rw [staticDispatch_isSome_iff]; exact hsome
    obtain ⟨cfg', hcfg'⟩ := Option.isSome_iff_exists.mp hd
    exact Or.inr ⟨cfg', by simpa [Source.step] using hcfg'⟩
  | ret v =>
    cases K with
    | nil => exact Or.inl (by simp [isReturnConfig])
    | cons fr K' =>
      cases fr with
      | letF N => exact Or.inr ⟨(K', Comp.subst v N), by simp [Source.step]⟩
      | handleF h =>
        -- REDUCE handler-return = identity for BOTH throws and state (ADR-0023 Q6 / ADR-0025).
        cases h with
        | throws ℓ => exact Or.inr ⟨(K', Comp.ret v), by simp [Source.step]⟩
        | state ℓ s => exact Or.inr ⟨(K', Comp.ret v), by simp [Source.step]⟩
        | transaction ℓ Θ => exact Or.inr ⟨(K', Comp.ret v), by simp [Source.step]⟩
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
      | appF w => exact Or.inr ⟨(K', Comp.subst w M), by simp [Source.step]⟩
      | letF N =>
        obtain ⟨q'', A'', e₂, qk, B'', hCeq, _⟩ := hstack.letF_inv
        exact absurd hCeq (by simp)
      | handleF h =>
        obtain ⟨φ, q'', A'', hCeq, _⟩ := hstack.handleAny_inv
        exact absurd hCeq (by simp)
  | case v N₁ N₂ =>
    -- closed `v : sum A B` is `inl a`/`inr a` (canonical forms); each fires its branch.
    obtain ⟨γ_v, γ_N, q, A, B, hγ, hv, hN₁, hN₂⟩ := hfocus.case_inv
    rcases hv.sum_canonical with ⟨a, hveq, _⟩ | ⟨a, hveq, _⟩
    · subst hveq; exact Or.inr ⟨(K, Comp.subst a N₁), by simp [Source.step]⟩
    · subst hveq; exact Or.inr ⟨(K, Comp.subst a N₂), by simp [Source.step]⟩
  | split v N =>
    -- closed `v : prod A B` is `pair a b`; split reduces.
    obtain ⟨γ_v, γ_N, q, A, B, hγ, hv, hN⟩ := hfocus.split_inv
    obtain ⟨γ_a, γ_b, a, b, hveq, _, _, _⟩ := hv.prod_canonical
    subst hveq
    exact Or.inr ⟨(K, Comp.subst a (Comp.subst (Val.shift b) N)), by simp [Source.step]⟩
  | unfold v =>
    -- closed `v : mu A` is `fold a`; `unfold (fold a) ↦ ret a`.
    obtain ⟨A, _, _, hv⟩ := hfocus.unfold_inv
    obtain ⟨a, hveq, _⟩ := hv.mu_canonical
    subst hveq
    exact Or.inr ⟨(K, Comp.ret a), by simp [Source.step]⟩
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
    · -- isReturnConfig cfg ⇒ cfg = ([], ret v) ⇒ Config.run hits the `done` arm.
      obtain ⟨K, M⟩ := cfg
      cases K with
      | cons fr K' => cases M <;> simp only [isReturnConfig] at hret
      | nil =>
        cases M with
        | ret v => simp [Config.run]
        | letC _ _ => simp only [isReturnConfig] at hret
        | app _ _ => simp only [isReturnConfig] at hret
        | handle _ _ => simp only [isReturnConfig] at hret
        | force _ => simp only [isReturnConfig] at hret
        | perform _ _ _ _ => simp only [isReturnConfig] at hret
        | lam _ => simp only [isReturnConfig] at hret
        | case _ _ _ => simp only [isReturnConfig] at hret
        | split _ _ => simp only [isReturnConfig] at hret
        | unfold _ => simp only [isReturnConfig] at hret
        | oom => simp only [isReturnConfig] at hret
        | wrong _ => simp only [isReturnConfig] at hret
    · -- cfg steps; preservation gives eo' ≤ ⊥ ⇒ eo' = ⊥; re-establish IH on cfg'.
      obtain ⟨eo', hle, hcfg'⟩ := preservation_proof hcfg hstep
      rw [le_bot_iff] at hle; subst hle
      obtain ⟨K, M⟩ := cfg
      have hrun : Config.run (n + 1) (K, M) = Config.run n cfg' := by
        cases K with
        | cons fr K' => simp only [Config.run]; rw [hstep]
        | nil =>
          cases M with
          | ret v => simp [Source.step] at hstep
          | letC M N => simp only [Config.run]; rw [hstep]
          | app M w => simp only [Config.run]; rw [hstep]
          | handle hh M => simp only [Config.run]; rw [hstep]
          | force w => simp only [Config.run]; rw [hstep]
          | perform _ l o w => simp only [Config.run]; rw [hstep]
          | lam M => simp [Source.step] at hstep
          | case v N₁ N₂ => simp only [Config.run]; rw [hstep]
          | split v N => simp only [Config.run]; rw [hstep]
          | unfold v => simp only [Config.run]; rw [hstep]
          | oom => simp [Source.step] at hstep
          | wrong s => simp [Source.step] at hstep
      rw [hrun]
      exact ih cfg' hcfg'

/-- ADR-0045 R1: `type_safety` gains an `LWConfig ([], c)` premise (the lexical-capability invariant),
exactly as the `WellCapped` fold required (the amendment in ADR-0045). `LWConfig ([], c)` unfolds to
`LWT [] [] c ∧ True` (`handlersOf [] = []`, `retCtx [] = []`, `LWStack [] = True`) — the program is
lexically well-scoped at top level (no escaping capability). This is the closed-well-typed ⟹
well-capped obligation the shell elaborator discharges. -/
theorem type_safety_proof
    {c : Comp} {q : Mult} {A : VTy Eff Mult} :
    HasCTy [] [] c ⊥ (CTy.F q A) → LWConfig ([], c) → ∀ fuel, Source.eval fuel c ≠ Result.stuck := by
  intro h hlw fuel
  rw [show Source.eval fuel c = Config.run fuel ([], c) from rfl]
  exact run_safe fuel ([], c) ⟨⟨⊥, CTy.F q A, h, HasStack.nil⟩, hlw⟩

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
