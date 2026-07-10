import Bang.Meta.BinaryLR
import Bang.Core.Semantics.Invariants

/-! # StackBelowInsufficientProbe — does `StackBelow g K ∧ nid < g` give `splitAtId K nid = none`?
The ADR-0096 (i′) recommended carrier is `StackBelow g Kᵢ` (ids < g). But the strip needs
`splitAtId Kᵢ nid = none` where `nid` is a LIVE deep-catcher id (nid < g). REFUTE-FIRST: an
upper-bound `StackBelow g` does NOT exclude a live `nid < g` from appearing in Kᵢ. -/

namespace Bang
open Bang.EffectRow (Label)
variable {Eff  : Type} [Lattice Eff] [OrderBot Eff]
variable {Mult : Type} [CommSemiring Mult] [DecidableEq Mult]
variable [EffSig Eff Mult]

-- REFUTATION: StackBelow 5 [handleF 2 (throws 0)] holds, 2 < 5, yet splitAtId … 2 = some (…), NOT none.
theorem stackBelow_does_not_give_fresh_for_live_id :
    ∃ (g nid : Nat) (K : EvalCtx),
      Bang.StackBelow g K ∧ nid < g ∧ Bang.splitAtId K nid ≠ none := by
  refine ⟨5, 2, [Frame.handleF 2 (Handler.throws 0)], ?_, by decide, ?_⟩
  · exact ⟨by decide, trivial⟩
  · simp [splitAtId]

end Bang
#print axioms Bang.stackBelow_does_not_give_fresh_for_live_id
