/-
  Compat.lean — the Phase-B target list.
  `lr_fundamental` (Spec.lean) = induction over the typing derivation, one case
  per rule, each discharged by the matching lemma below. Proving all of these
  (in PROOF_ORDER) IS proving the fundamental theorem.

  Source map: value/computation compat = standard CBPV; the three effect lemmas
  mirror Biernacki et al. Lemmas 5–7 (compat-op / compat-lift / compat-handle),
  here with `lift`/`ρ` DROPPED because bang-lang rows are idempotent `Finset`s
  (REFERENCES §C, paper §5.4). The graded structural lemmas are the QTT/coeffect
  content: `·` scales the argument context, `+` splits it.

  Risk: all [STD]/recipe EXCEPT `compat_handle`, which is [KEY] — it is the heart
  of the effect side and where `Srel` (the 𝒮 half of `Krel`) is actually used.
-/
import Bang.Spec
namespace Bang

variable {Eff : Type} [OrderedSemiring Eff]
variable {Mult : Type} [OrderedSemiring Mult]

/-! ## Open logical relation (their |=, Fig 9): close `Crel`/`Vrel` over related
    substitutions `GSubst` (their 𝒢⟦Γ⟧). Equivalence = approximation both ways. -/

opaque Subst         : Type
opaque Subst.onComp  : Subst → Comp → Comp
opaque Subst.onVal   : Subst → Val → Val
opaque GSubst        : Nat → Ctx → Subst → Subst → Prop

def OpenC (Γ : Ctx) (B : CTy) (c₁ c₂ : Comp) : Prop :=
  ∀ n γ₁ γ₂, GSubst n Γ γ₁ γ₂ → Crel n B (Subst.onComp γ₁ c₁) (Subst.onComp γ₂ c₂)
def OpenV (Γ : Ctx) (A : VTy) (v₁ v₂ : Val) : Prop :=
  ∀ n γ₁ γ₂, GSubst n Γ γ₁ γ₂ → Vrel n A (Subst.onVal γ₁ v₁) (Subst.onVal γ₂ v₂)

/-! ## Term constructors (stubs — Phase A makes these real inductives) -/

opaque var    : Var → Val
opaque unit   : Val
opaque lamC   : Var → Comp → Comp          -- A →^ρ B  introduction
opaque appC   : Comp → Val → Comp          -- application
opaque forceC : Val → Comp                 -- U-elimination
opaque bindC  : Comp → Var → Comp → Comp   -- x ← c ; d   (F-elimination / seq)
opaque opC    : Eff → Val → Comp           -- operation invocation (= `raise`)
opaque handleC : Eff → Comp → Handler → Comp → Comp  -- handle body {h} return x.er

/-! ## Value compatibility -/

-- [STD] variable: look up its graded binding.
theorem compat_var {Γ : Ctx} {x : Var} {ρ : Mult} {A : VTy} :
    OpenV (Ctx.bind x ρ A Γ) A (var x) (var x) := sorry

-- [STD] unit / base introduction.
theorem compat_unit {Γ : Ctx} {A : VTy} : OpenV Γ A unit unit := sorry

-- [STD] thunk (U-intro): a related computation thunks to a related value; the
-- grade ρ rides along (and `ρ = 0` makes the goal trivial — erasability).
theorem compat_thunk {Γ : Ctx} {ρ : Mult} {B : CTy} {c₁ c₂ : Comp} :
    OpenC Γ B c₁ c₂ → OpenV Γ (U ρ B) (thunk c₁) (thunk c₂) := sorry

/-! ## Computation compatibility -/

-- [STD] force (U-elim): needs the thunk usable (ρ ≥ 1).
theorem compat_force {Γ : Ctx} {ρ : Mult} {B : CTy} {v₁ v₂ : Val} :
    1 ≤ ρ → OpenV Γ (U ρ B) v₁ v₂ → OpenC Γ B (forceC v₁) (forceC v₂) := sorry

-- [STD] return (F-intro): pure, identity effect grade.
theorem compat_ret {Γ : Ctx} {A : VTy} {v₁ v₂ : Val} :
    OpenV Γ A v₁ v₂ → OpenC Γ (F 1 A) (ret v₁) (ret v₂) := sorry  -- `1` = ι, identity effect

-- [STD] bind / sequencing (F-elim): effects compose by the semiring product `·`.
theorem compat_bind {Γ : Ctx} {x : Var} {e e' : Eff} {A : VTy} {B : CTy}
    {c₁ c₂ d₁ d₂ : Comp} :
    OpenC Γ (F e A) c₁ c₂ →
    OpenC (Ctx.bind x 1 A Γ) (F e' B) d₁ d₂ →
    OpenC Γ (F (e * e') B) (bindC c₁ x d₁) (bindC c₂ x d₂) := sorry

-- [STD] λ (computation-arrow intro): coeffect grade ρ records the argument's use.
theorem compat_lam {Γ : Ctx} {x : Var} {ρ : Mult} {A : VTy} {B : CTy}
    {c₁ c₂ : Comp} :
    OpenC (Ctx.bind x ρ A Γ) B c₁ c₂ →
    OpenC Γ B (lamC x c₁) (lamC x c₂) := sorry   -- B is the arrow type A →^ρ B'

-- [STD] application: the argument context is SCALED by ρ (QTT multiplication),
-- then added — this is where `Ctx.scale`/`Ctx.add` carry the multiplicity.
theorem compat_app {Γ Δ : Ctx} {ρ : Mult} {A : VTy} {B : CTy}
    {c₁ c₂ : Comp} {v₁ v₂ : Val} :
    OpenC Γ B c₁ c₂ → OpenV Δ A v₁ v₂ →
    OpenC (Ctx.add Γ (Ctx.scale ρ Δ)) B (appC c₁ v₁) (appC c₂ v₂) := sorry

/-! ## Effect compatibility (Biernacki Lemmas 5–7, lift/ρ dropped) -/

-- [STD] compat-op (their Lemma 5): an operation in row `e` is related to itself.
theorem compat_op {Γ : Ctx} {e : Eff} {v₁ v₂ : Val} {A : VTy} :
    OpenV Γ A v₁ v₂ → OpenC Γ (F e A) (opC e v₁) (opC e v₂) := sorry

-- (compat-lift, their Lemma 6, is OMITTED: `lift` does not exist for set-rows.)

-- [KEY] compat-handle (their Lemma 7): body related at `F⟨l|e⟩`, each handler
-- clause related, return clause related ⇒ the two handlers are related at `F e`.
-- This is the lemma that consumes `Srel` — the capstone of the whole proof.
theorem compat_handle {Γ : Ctx} {x : Var} {l e : Eff} {A : VTy} {B : CTy}
    {body₁ body₂ ret₁ ret₂ : Comp} {h₁ h₂ : Handler} :
    OpenC Γ (F (l * e) A) body₁ body₂ →
    HandlerRelated Γ l e B h₁ h₂ →                         -- clause-wise relatedness
    OpenC (Ctx.bind x 1 A Γ) (F e B) ret₁ ret₂ →
    OpenC Γ (F e B) (handleC l body₁ h₁ ret₁) (handleC l body₂ h₂ ret₂) := sorry

opaque HandlerRelated : Ctx → Eff → Eff → CTy → Handler → Handler → Prop

/-! ## Graded structural compatibility (QTT/coeffect content) -/

-- [STD] sub-effecting + sub-usaging: `≤` on grades preserves relatedness
-- (monotone; the semilattice/order structure of `Eff` and `Mult`).
theorem compat_sub_eff {Γ : Ctx} {e e' : Eff} {A : VTy} {c₁ c₂ : Comp} :
    e ≤ e' → OpenC Γ (F e A) c₁ c₂ → OpenC Γ (F e' A) c₁ c₂ := sorry

-- [STD] 0-graded weakening: an unused (0-use) binder can be added freely.
theorem compat_weaken {Γ : Ctx} {x : Var} {A B : VTy} {v₁ v₂ : Val} :
    OpenV Γ B v₁ v₂ → OpenV (Ctx.bind x 0 A Γ) B v₁ v₂ := sorry

-- [STD] resource split: the additive context structure `Γ = Γ₁ + Γ₂`.
theorem compat_split {Γ₁ Γ₂ : Ctx} {A : VTy} {v₁ v₂ : Val} :
    OpenV Γ₁ A v₁ v₂ → OpenV Γ₂ A v₁ v₂ →
    OpenV (Ctx.add Γ₁ Γ₂) A v₁ v₂ := sorry

/-! ## Assembly: `lr_fundamental` (Spec.lean) is the induction that, at each
    typing rule, invokes the matching lemma above. Discharging this file (in
    PROOF_ORDER) proves the fundamental theorem; `lr_sound` then yields `⊑`. -/

end Bang
