import Bang.Meta.LR
import Bang.Core.Soundness

/-! # CrelKUpVacuityProbe — item-2 refute-first probe (task #29 / #32)

HYPOTHESIS: `crelK_fund_up` closes WITHOUT any NonEscape / HasConfigTy⟹NonEscape / frozen change,
because `CoApproxC_le` is VACUOUS in the cap-ESCAPE case: `Config.run n` on an escaped-cap focus
returns `.escapedCap ≠ .done`, so `ConvergesC_le n` is FALSE. Isolated escape-case vacuity here. -/

namespace Bang
open Bang.EffectRow (Label)
variable {Eff  : Type} [Lattice Eff] [OrderBot Eff]
variable {Mult : Type} [CommSemiring Mult] [DecidableEq Mult]
variable [EffSig Eff Mult]

/-- ESCAPE-CASE VACUITY: if the LEFT cap escapes, the LEFT config does NOT converge. -/
theorem convergesC_le_escape_false {n : Nat} {g : Nat} {K₁ : Stack} {m : Nat} {ℓ : Label}
    {op : OpId} {v₁ : Val}
    (hesc : Bang.idDispatch K₁ m ℓ op v₁ = none) :
    ¬ ConvergesC_le n (g, K₁, Comp.perform (Val.vcap m ℓ) op v₁) := by
  rintro ⟨w, hw⟩
  have hde : IsDefinedEscape (g, K₁, Comp.perform (Val.vcap m ℓ) op v₁) := hesc
  cases n with
  | zero => rw [show Config.run 0 _ = Result.oom from rfl] at hw; exact absurd hw (by simp)
  | succ k =>
      rw [run_escapedCap_of_definedEscape hde] at hw
      exact absurd hw (by simp)

end Bang
