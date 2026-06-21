/-
  Bang/Metatheory.lean — syntactic metatheory: weakening + graded substitution.
  ──────────────────────────────────────────────────────────────────────────────
  Auxiliary lemmas backing the frozen `subst_value` statement in Bang/Spec.lean.

  Ported (shape only) from plclub/cbpv-effects-coeffects `resource/CBPV/`:
    - typing.v       (the resource-enforcing rules we induct over)
    - renaming.v     (their `type_pres_renaming` — the mutual weakening shape)
  They are de-Bruijn + autosubst2; we are named + Finsupp, so the grade
  bookkeeping uses `Finsupp.add_apply`/`single_apply` where they use `q .: γ`.

    shape: torczon-oopsla24-effects-coeffects §graded-subst (T_App arithmetic)
-/

import Bang.Core
import Bang.Syntax
import Bang.Operational
import Mathlib.Tactic.Abel

namespace Bang

open Finsupp

variable {Eff  : Type} [Lattice Eff] [OrderBot Eff]
variable {Mult : Type} [Semiring Mult] [DecidableEq Mult]


/-! ### Weakening — insert one binder anywhere in the ambient type context.

The grade vector is unchanged (weakening adds a `0`-graded variable; the
Finsupp default off-support IS `0`, so there is nothing to add). We only
need to thread the membership through `List.append`. Mutual over the two
judgments, following `renaming.v`'s `type_pres_renaming`. -/

mutual
theorem HasVTy.weaken_mem
    {γ : GradeVec Mult} {Γ Γ' : TyCtx Eff Mult} {v : Val} {A : VTy Eff Mult}
    (sub : ∀ {z C}, (z, C) ∈ Γ → (z, C) ∈ Γ')
    (h : HasVTy γ Γ v A) : HasVTy γ Γ' v A := by
  cases h with
  | vunit => exact .vunit
  | vint  => exact .vint
  | vvar hmem => exact .vvar (sub hmem)
  | vthunk hM => exact .vthunk (HasCTy.weaken_mem sub hM)

theorem HasCTy.weaken_mem
    {γ : GradeVec Mult} {Γ Γ' : TyCtx Eff Mult} {c : Comp} {e : Eff} {B : CTy Eff Mult}
    (sub : ∀ {z C}, (z, C) ∈ Γ → (z, C) ∈ Γ')
    (h : HasCTy γ Γ c e B) : HasCTy γ Γ' c e B := by
  cases h with
  | ret hv heq => exact .ret (HasVTy.weaken_mem sub hv) heq
  | letC hy0 hM hN heq =>
      refine .letC hy0 (HasCTy.weaken_mem sub hM) (HasCTy.weaken_mem ?_ hN) heq
      intro z C hmem
      rcases List.mem_cons.mp hmem with h0 | h1
      · exact h0 ▸ List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (sub h1)
  | force hv => exact .force (HasVTy.weaken_mem sub hv)
  | lam hy0 hM =>
      refine .lam hy0 (HasCTy.weaken_mem ?_ hM)
      intro z C hmem
      rcases List.mem_cons.mp hmem with h0 | h1
      · exact h0 ▸ List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (sub h1)
  | app hM hv heq => exact .app (HasCTy.weaken_mem sub hM) (HasVTy.weaken_mem sub hv) heq
  | handle hM => exact .handle (HasCTy.weaken_mem sub hM)
end

/-- Weaken a CLOSED derivation (empty type context) into any context. -/
theorem HasVTy.weaken_closed
    {γ : GradeVec Mult} {Γ : TyCtx Eff Mult} {v : Val} {A : VTy Eff Mult}
    (h : HasVTy γ [] v A) : HasVTy γ Γ v A :=
  HasVTy.weaken_mem (fun hmem => absurd hmem List.not_mem_nil) h


/-! ### Grade support ⊆ context keys.

A variable `z` absent from the type context carries `0` grade. Proved by
mutual induction; the binder cases (`lam`/`letC`) use the new bound-var-grade
invariant (`γ y = 0` / `γ₂ y = 0`, Syntax.lean §1.6). Corollary: a CLOSED
derivation (`Γ = []`) is `0`-graded — so the substituted value's grade
`γ_Δ` in `subst_value` is forced to `0`. -/

mutual
theorem HasVTy.grade_support
    {γ : GradeVec Mult} {Γ : TyCtx Eff Mult} {v : Val} {A : VTy Eff Mult}
    (h : HasVTy γ Γ v A) {z : Var} (hz : ∀ C, (z, C) ∉ Γ) : γ z = 0 := by
  cases h with
  | vunit => rfl
  | vint => rfl
  | @vvar _ x A hmem =>
      have hzx : z ≠ x := by rintro rfl; exact hz A hmem
      exact Finsupp.single_eq_of_ne hzx
  | vthunk hM => exact HasCTy.grade_support hM hz
theorem HasCTy.grade_support
    {γ : GradeVec Mult} {Γ : TyCtx Eff Mult} {c : Comp} {e : Eff} {B : CTy Eff Mult}
    (h : HasCTy γ Γ c e B) {z : Var} (hz : ∀ C, (z, C) ∉ Γ) : γ z = 0 := by
  cases h with
  | ret hv heq => subst heq; rw [Finsupp.smul_apply, HasVTy.grade_support hv hz, smul_zero]
  | @letC g g1 g2 _ y M N φ1 φ2 q1 q2 A B hy0 hM hN heq =>
      subst heq
      rw [Finsupp.add_apply, Finsupp.smul_apply, HasCTy.grade_support hM hz, smul_zero, zero_add]
      by_cases hzy : z = y
      · subst hzy; exact hy0
      · have hzN := HasCTy.grade_support hN (z := z) (by
          intro C hmem
          rcases List.mem_cons.mp hmem with h0 | h1
          · exact hzy (Prod.mk.injEq .. ▸ h0).1
          · exact hz C h1)
        rwa [Finsupp.add_apply, Finsupp.single_eq_of_ne hzy, zero_add] at hzN
  | force hv => exact HasVTy.grade_support hv hz
  | @lam g _ y M φ q A B hy0 hM =>
      by_cases hzy : z = y
      · subst hzy; exact hy0
      · have hzM := HasCTy.grade_support hM (z := z) (by
          intro C hmem
          rcases List.mem_cons.mp hmem with h0 | h1
          · exact hzy (Prod.mk.injEq .. ▸ h0).1
          · exact hz C h1)
        rwa [Finsupp.add_apply, Finsupp.single_eq_of_ne hzy, zero_add] at hzM
  | app hM hv heq =>
      subst heq
      rw [Finsupp.add_apply, Finsupp.smul_apply, HasCTy.grade_support hM hz,
        HasVTy.grade_support hv hz, smul_zero, add_zero]
  | handle hM => exact HasCTy.grade_support hM hz
end

/-- A closed value is `0`-graded (corollary of `grade_support`). -/
theorem HasVTy.closed_grade_zero
    {γ : GradeVec Mult} {v : Val} {A : VTy Eff Mult}
    (h : HasVTy γ ([] : TyCtx Eff Mult) v A) : γ = 0 := by
  ext z; exact HasVTy.grade_support h (fun _ => List.not_mem_nil)



/-! ### Grade arithmetic for substitution (Finsupp `erase`/`single`/`smul`).

The substitution lemma threads the bound variable's multiplicity as `γ x`
(the coefficient at `x`) and rebuilds the remaining grade as `γ.erase x`.
These four facts are all the Finsupp algebra the induction needs. -/

omit [Lattice Eff] [OrderBot Eff] in
theorem smul_erase (q : Mult) (x : Var) (g : GradeVec Mult) :
    (q • g).erase x = q • (g.erase x) := by
  ext y
  by_cases h : y = x
  · subst h; rw [Finsupp.erase_same, Finsupp.smul_apply, Finsupp.erase_same, smul_zero]
  · rw [Finsupp.erase_ne h, Finsupp.smul_apply, Finsupp.smul_apply, Finsupp.erase_ne h]

omit [Lattice Eff] [OrderBot Eff] in
theorem add_erase (x : Var) (a b : GradeVec Mult) :
    (a + b).erase x = a.erase x + b.erase x := by
  ext y
  by_cases h : y = x
  · subst h; simp [Finsupp.erase_same]
  · simp [Finsupp.erase_ne h]

-- `g = single x (g x) + g.erase x` — peel the `x`-coefficient off `g`.
omit [Lattice Eff] [OrderBot Eff] in
theorem single_add_erase (x : Var) (g : GradeVec Mult) :
    Finsupp.single x (g x) + g.erase x = g := by
  ext y
  by_cases h : y = x
  · subst h; simp
  · simp [Finsupp.single_apply, Finsupp.erase_ne h, h]

omit [Lattice Eff] [OrderBot Eff] in
theorem single_erase_self (x : Var) (q : Mult) :
    (Finsupp.single x q).erase x = 0 := by
  ext y; by_cases h : y = x
  · subst h; rw [Finsupp.erase_same]; rfl
  · rw [Finsupp.erase_ne h]; simp [Finsupp.single_apply, h]

omit [Lattice Eff] [OrderBot Eff] in
theorem single_erase_of_ne {x z : Var} (h : x ≠ z) (q : Mult) :
    (Finsupp.single z q).erase x = Finsupp.single z q := by
  ext y; by_cases hy : y = x
  · subst hy; rw [Finsupp.erase_same, Finsupp.single_apply, if_neg (fun he => h he.symm)]
  · rw [Finsupp.erase_ne hy]


/-! ### Membership helper: drop the designated `(x,A)` slot when looking up `z ≠ x`. -/

omit [Lattice Eff] [OrderBot Eff] [Semiring Mult] [DecidableEq Mult] in
theorem mem_drop_mid {pre Γ : TyCtx Eff Mult} {x z : Var} {A C : VTy Eff Mult}
    (hzx : z ≠ x) (hmem : (z, C) ∈ pre ++ (x, A) :: Γ) :
    (z, C) ∈ pre ++ Γ := by
  rcases List.mem_append.mp hmem with hin | hin
  · exact List.mem_append_left _ hin
  · rcases List.mem_cons.mp hin with h0 | h1
    · exact absurd (Prod.mk.injEq .. ▸ h0).1 hzx
    · exact List.mem_append_right _ h1


/-! ### Graded substitution — generalized over a binder prefix `pre`.

`subst_value` substitutes `x` at the HEAD of the context. To recurse under
binders (`lam`/`letC`), `x` slides deeper, so we generalize over a prefix
`pre` of binders crossed. The bound variable's multiplicity is read off as
`γ x`; the remaining grade is `γ.erase x`; the conclusion grade is
`γ.erase x + (γ x) • γ_Δ`. Scaling (`ret`/`app`/`letC`) threads through
because `erase` and `(· x)` both commute with `•` and `+`.

Side-conditions (named-encoding analogue of de Bruijn's positional
uniqueness `q .: γ`, `typing.v`):

  - `hfp : ∀ C, (x, C) ∉ pre` — no crossed binder shadows `x`.
  - `hfg : ∀ C, (x, C) ∉ Γ`  — `x` not rebound in the residual context;
    THIS is the `x ∉ keys Γ` well-formedness hypothesis that `subst_value`
    LACKS (without it `Γ` may legally rebind `x` at a different type, so the
    looked-up `A'` differs from the substituted `v`'s `A` — machine-checked
    counterexample in the proof-engineer report, 2026-06-21).

  shape: cbpv-effects-coeffects renaming.v (mutual `type_pres_renaming`) -/

mutual
theorem HasVTy.subst_gen
    {γ γ_Δ : GradeVec Mult} {pre Γ : TyCtx Eff Mult}
    {x : Var} {v : Val} {A : VTy Eff Mult} {w : Val} {A' : VTy Eff Mult}
    (hv : HasVTy γ_Δ [] v A)
    (hfp : ∀ C, (x, C) ∉ pre) (hfg : ∀ C, (x, C) ∉ Γ)
    (hw : HasVTy γ (pre ++ (x, A) :: Γ) w A') :
    HasVTy (γ.erase x + (γ x) • γ_Δ) (pre ++ Γ) (Val.subst x v w) A' := by
  cases hw with
  | vunit =>
      -- γ = 0 ⇒ erase 0 + 0 • γ_Δ = 0
      simp only [Val.subst, Finsupp.erase_zero, Finsupp.coe_zero, Pi.zero_apply,
        zero_smul, add_zero]
      exact .vunit
  | vint =>
      simp only [Val.subst, Finsupp.erase_zero, Finsupp.coe_zero, Pi.zero_apply,
        zero_smul, add_zero]
      exact .vint
  | @vvar _ z _ hmem =>
      by_cases hzx : x = z
      · -- substituted variable. γ = single x 1; γ x = 1; γ.erase x = 0; A' = A.
        subst hzx
        have hAeq : A' = A := by
          rcases List.mem_append.mp hmem with hin | hin
          · exact absurd hin (hfp A')
          · rcases List.mem_cons.mp hin with h0 | h1
            · exact (Prod.mk.injEq .. ▸ h0).2
            · exact absurd h1 (hfg A')
        subst hAeq
        rw [Finsupp.single_eq_same, single_erase_self, one_smul, zero_add]
        simp only [Val.subst, if_pos]
        exact HasVTy.weaken_closed hv
      · -- different variable. γ = single z 1; γ x = 0; γ.erase x = single z 1.
        have hzx' : z ≠ x := fun he => hzx he.symm
        rw [single_erase_of_ne hzx]
        rw [show (Finsupp.single z (1:Mult)) x = 0 from Finsupp.single_eq_of_ne hzx]
        rw [zero_smul, add_zero]
        simp only [Val.subst, if_neg hzx]
        exact HasVTy.vvar (mem_drop_mid hzx' hmem)
  | @vthunk _ _ _ _ _ hM =>
      simp only [Val.subst]
      exact .vthunk (HasCTy.subst_gen hv hfp hfg hM)

theorem HasCTy.subst_gen
    {γ γ_Δ : GradeVec Mult} {pre Γ : TyCtx Eff Mult}
    {x : Var} {v : Val} {A : VTy Eff Mult} {c : Comp} {e : Eff} {B : CTy Eff Mult}
    (hv : HasVTy γ_Δ [] v A)
    (hfp : ∀ C, (x, C) ∉ pre) (hfg : ∀ C, (x, C) ∉ Γ)
    (hc : HasCTy γ (pre ++ (x, A) :: Γ) c e B) :
    HasCTy (γ.erase x + (γ x) • γ_Δ) (pre ++ Γ) (Comp.subst x v c) e B := by
  cases hc with
  | @ret g g' _ w A_r q hw hgeq =>
      -- γ = q • g'. ret rebuilds at the value's grade.
      subst hgeq
      simp only [Comp.subst]
      have ih := HasVTy.subst_gen hv hfp hfg hw
      refine .ret ih ?_
      -- (q•g').erase x + (q•g') x • γ_Δ = q • (g'.erase x + g' x • γ_Δ)
      rw [smul_erase, Finsupp.smul_apply, smul_add, smul_assoc]
  | @force g _ w φ B' hw =>
      simp only [Comp.subst]
      exact .force (HasVTy.subst_gen hv hfp hfg hw)
  | @app g g1 g2 _ M' w φ q A_a B' hM hw hgeq =>
      subst hgeq
      simp only [Comp.subst]
      have ihM := HasCTy.subst_gen hv hfp hfg hM
      have ihw := HasVTy.subst_gen hv hfp hfg hw
      refine .app ihM ihw ?_
      -- (g1 + q•g2).erase x + (g1+q•g2) x • γ_Δ
      --   = (g1.erase x + g1 x • γ_Δ) + q • (g2.erase x + g2 x • γ_Δ)
      rw [add_erase, Finsupp.add_apply, add_smul, smul_erase, Finsupp.smul_apply,
        smul_add, smul_assoc]
      abel
  | @handle g _ h M' φ B' hM =>
      simp only [Comp.subst]
      exact .handle (HasCTy.subst_gen hv hfp hfg hM)
  | @lam g _ y M' φ q A_l B' hy0 hM =>
      by_cases hxy : x = y
      · -- SHADOWED (x = y): `Comp.subst` stops; `lam x M'` is returned unchanged.
        -- BLOCKED — FOURTH FALSITY (survives BOTH kernel fixes). `subst_value` is
        -- FALSE in this case: the body's `vvar x` may be typed via the (deep,
        -- substituted) slot `(x,A)` at a type `A ≠ A_l` (the lam binder type),
        -- because the named `vvar` rule's lookup is NON-DETERMINISTIC and the
        -- shadowing binder `(x,A_l)` is introduced INSIDE `c`, not in `Γ` (so
        -- neither `hfg`/no-dup nor the `γ y = 0` lam invariant rules it out).
        -- Substituting then changes the conclusion type `B`, which `subst_value`
        -- fixes. Machine-checked `example : False` (Bang/CexSubst3.lean, 2026-06-21)
        -- with c = `lam x (ret (vvar x))`, deep `(x,unit)`, binder `(x,int)`.
        -- FIX: make `vvar` lookup deterministic (first-match), OR forbid a binder
        -- from shadowing a context variable. Kernel-rule concern — see report.
        sorry
      · -- not shadowed: descend into the body under the extended prefix (y,A_l)::pre.
        simp only [Comp.subst, if_neg hxy]
        have hfp' : ∀ C, (x, C) ∉ (y, A_l) :: pre := by
          intro C hmem
          rcases List.mem_cons.mp hmem with h0 | h1
          · exact hxy (Prod.mk.injEq .. ▸ h0).1
          · exact hfp C h1
        have ih := HasCTy.subst_gen (pre := (y, A_l) :: pre) hv hfp' hfg hM
        -- body grade rewrites: (single y q + g).erase x = single y q + g.erase x,
        -- and (single y q + g) x = g x.  Reassemble the lam.
        rw [add_erase, single_erase_of_ne hxy, Finsupp.add_apply,
          Finsupp.single_eq_of_ne hxy, zero_add, add_assoc] at ih
        -- new lam-rule premise `(g.erase x + g x • γ_Δ) y = 0`:
        refine .lam ?_ ih
        have hΔ0 : γ_Δ = 0 := HasVTy.closed_grade_zero hv
        rw [hΔ0, smul_zero, add_zero]
        rw [Finsupp.erase_ne (fun he => hxy he.symm), hy0]
  | @letC g g1 g2 _ y M' N' φ1 φ2 q1 q2 A_l B' hy0 hM hN hgeq =>
      subst hgeq
      by_cases hxy : x = y
      · -- SHADOWED (x = y): subst into M' descends, but N' is left unchanged.
        -- BLOCKED — same FOURTH FALSITY as `lam` (continuation `N'` under the
        -- shadowing binder `(x,A_l)` may use the deep `(x,A)` at a divergent type).
        -- See `lam` comment + Bang/CexSubst3.lean. Kernel-rule concern.
        sorry
      · -- not shadowed.
        simp only [Comp.subst, if_neg hxy]
        have hfp' : ∀ C, (x, C) ∉ (y, A_l) :: pre := by
          intro C hmem
          rcases List.mem_cons.mp hmem with h0 | h1
          · exact hxy (Prod.mk.injEq .. ▸ h0).1
          · exact hfp C h1
        have ihM := HasCTy.subst_gen hv hfp hfg hM
        have ihN := HasCTy.subst_gen (pre := (y, A_l) :: pre) hv hfp' hfg hN
        -- N-binder grade: (single y (q1*q_or_1 q2) + g2).erase x reassembles
        rw [add_erase, single_erase_of_ne hxy, Finsupp.add_apply,
          Finsupp.single_eq_of_ne hxy, zero_add, add_assoc] at ihN
        -- new letC-rule premise `(g2.erase x + g2 x • γ_Δ) y = 0`:
        refine .letC ?_ ihM ihN ?_
        · have hΔ0 : γ_Δ = 0 := HasVTy.closed_grade_zero hv
          rw [hΔ0, smul_zero, add_zero, Finsupp.erase_ne (fun he => hxy he.symm), hy0]
        -- (q_or_1 q2 • g1 + g2).erase x + (q_or_1 q2•g1 + g2) x • γ_Δ
        --   = q_or_1 q2 • (g1.erase x + g1 x•γ_Δ) + (g2.erase x + g2 x•γ_Δ)
        · rw [add_erase, smul_erase, Finsupp.add_apply, Finsupp.smul_apply,
            add_smul, smul_add, smul_assoc]
          abel
end


/-! ### `subst_value` — the frozen Spec statement, specialized from `subst_gen`.

Mirrors `Bang/Spec.lean`'s `subst_value` exactly (incl. the `∀ C, (x,C) ∉ Γ`
hypothesis, Gap A). Discharges via `HasCTy.subst_gen` at `pre = []`, then a
grade rewrite. NOTE: `subst_gen` is itself blocked on the FOURTH falsity in its
shadowed-binder cases (`lam`/`letC` with `x = y`), so this proof transitively
carries those `sorry`s until the kernel makes `vvar` lookup deterministic. -/

theorem subst_value_proof
    (ρ : Mult) {γ_Γ γ_Δ : GradeVec Mult} {Γ : TyCtx Eff Mult}
    {x : Var} {v : Val} {A : VTy Eff Mult}
    {c : Comp} {e : Eff} {B : CTy Eff Mult}
    (hv : HasVTy γ_Δ [] v A)
    (hx0 : γ_Γ x = 0)
    (hfg : ∀ C, (x, C) ∉ Γ)
    (hc : HasCTy (Finsupp.single x ρ + γ_Γ) ((x, A) :: Γ) c e B) :
    HasCTy (γ_Γ + ρ • γ_Δ) Γ (Comp.subst x v c) e B := by
  have key := HasCTy.subst_gen (pre := []) hv (by simp) hfg (by simpa using hc)
  -- grade: (single x ρ + γ_Γ).erase x = γ_Γ  and  (single x ρ + γ_Γ) x = ρ.
  have he : (Finsupp.single x ρ + γ_Γ).erase x = γ_Γ := by
    rw [add_erase, single_erase_self]
    rw [show γ_Γ.erase x = γ_Γ from by
      ext y; by_cases h : y = x
      · subst h; rw [Finsupp.erase_same, hx0]
      · rw [Finsupp.erase_ne h]]
    rw [zero_add]
  have ha : (Finsupp.single x ρ + γ_Γ) x = ρ := by
    rw [Finsupp.add_apply, Finsupp.single_eq_same, hx0, add_zero]
  rw [he, ha] at key
  simpa using key

end Bang
