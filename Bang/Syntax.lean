/-
  Bang/Syntax.lean — typing judgments + resource arithmetic + row well-formedness.
  ─────────────────────────────────────────────────────────────────────────────
  Sits between Bang.Core (raw types) and Bang.Operational (executes terms).

    §1.5 Ctx.scale + Ctx.add (QTT-style resource arithmetic)
    §1.6 HasVTy, HasCTy (mutual inductive Props — per-rule constructors)
    §0.5 Effect-row well-formedness: Disjoint, RowAll, WfInst, HandlesIntended

  Theorem STATEMENTS live in Bang/Spec.lean.
-/

import Bang.Core

namespace Bang

variable {Eff  : Type} [Semiring Eff] [PartialOrder Eff]
variable {Mult : Type} [Semiring Mult] [DecidableEq Mult]


/-! ### 1.5 Resource arithmetic on Ctx (QTT-style)

  Ctx.scale ρ Γ      = each binding's multiplicity scaled by ρ
  Ctx.add   Γ₁ Γ₂    = pointwise sum (zipWith)

CAVEAT: `add` uses `List.zipWith` → assumes Γ₁, Γ₂ have matching variable
lists in matching order. Phase B may need a FinMap representation; see
`docs/notes/OPEN_QUESTIONS.md` Q3. -/

def Ctx.scale {Eff Mult : Type} [Semiring Mult] (ρ : Mult)
    (Γ : Ctx Eff Mult) : Ctx Eff Mult :=
  Γ.map (fun b => (b.1, ρ * b.2.1, b.2.2))

def Ctx.add {Eff Mult : Type} [Semiring Mult]
    (Γ₁ Γ₂ : Ctx Eff Mult) : Ctx Eff Mult :=
  List.zipWith (fun b₁ b₂ => (b₁.1, b₁.2.1 + b₂.2.1, b₁.2.2)) Γ₁ Γ₂


/-! ### 1.6 Typing judgments

HasVTy : values are inert (no effect grade); judged at VTy
HasCTy : computations carry an explicit running effect grade `e`;
         inhabit CTy (whose `F q A` annotation is consumer-side coeffect)

PHASE A part 2 first-cut rules — refinements in `docs/notes/OPEN_QUESTIONS.md`
Q4 (handle), Q5 (up). -/

mutual
inductive HasVTy : Ctx Eff Mult → Val → VTy Eff Mult → Prop where
  | vunit  : ∀ {Γ}, HasVTy Γ Val.vunit VTy.unit
  | vint   : ∀ {Γ n}, HasVTy Γ (Val.vint n) VTy.int
  | vvar   : ∀ {Γ x A}, (∃ ρ, (x, ρ, A) ∈ Γ) → HasVTy Γ (Val.vvar x) A
  | vthunk : ∀ {Γ M φ B}, HasCTy Γ M φ B → HasVTy Γ (Val.vthunk M) (VTy.U φ B)
inductive HasCTy : Ctx Eff Mult → Comp → Eff → CTy Eff Mult → Prop where
  | ret    : ∀ {Γ v A q}, HasVTy Γ v A → HasCTy Γ (Comp.ret v) 0 (CTy.F q A)
  | letC   : ∀ {Γ y M N φ₁ φ₂ ρ A q B},
      HasCTy Γ M φ₁ (CTy.F q A) →
      HasCTy ((y, ρ, A) :: Γ) N φ₂ B →
      HasCTy Γ (Comp.letC y M N) (φ₁ + φ₂) B
  | force  : ∀ {Γ v φ B},
      HasVTy Γ v (VTy.U φ B) →
      HasCTy Γ (Comp.force v) φ B
  | lam    : ∀ {Γ y M φ ρ A B},
      HasCTy ((y, ρ, A) :: Γ) M φ B →
      HasCTy Γ (Comp.lam y M) 0 (CTy.arr A B)
  | app    : ∀ {Γ M v φ A B},
      HasCTy Γ M φ (CTy.arr A B) →
      HasVTy Γ v A →
      HasCTy Γ (Comp.app M v) φ B
  | handle : ∀ {Γ h M φ B},
      HasCTy Γ M φ B →
      HasCTy Γ (Comp.handle h M) φ B
end


/-! ### 0.5 Effect-row well-formedness — keeps rows SET-shaped (ADR-0018)

The lacks-constraint discipline that licenses dropping Biernacki's ρ-maps.
Currently axiomatized; concretization depends on Eff algebra choice
(see `docs/notes/OPEN_QUESTIONS.md` Q1). -/

axiom Disjoint {Eff : Type} : Eff → Eff → Prop
axiom RowAll {Eff Mult : Type} :
    (Eff → CTy Eff Mult) → Eff → CTy Eff Mult
axiom WfInst {Eff Mult : Type} :
    CTy Eff Mult → Eff → CTy Eff Mult → Prop
axiom HandlesIntended {Eff : Type} : Eff → Comp → Handler → Prop

end Bang
