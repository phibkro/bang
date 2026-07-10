import Bang.Meta.BinaryLR
import Bang.Core.Semantics.Invariants

/-! # KrelSAppendPremiseProbe — the clean krelS_append premise shape (task #37).
The nested-handleF case needs `StackBelow mh₁ (Kᵢrest ++ handleF nh h :: K₁)` — NOT locally derivable
from piecemeal `StackBelow nh K₁`. CLEANER: take `StackInc (Kᵢ ++ handleF nh h :: K₁)` (the full
appended stack) as the premise. Probe: does it deliver BOTH (a) the nil-base `StackBelow nh K₁` and
(b) the nested `StackBelow mh₁ (Kᵢrest ++ handleF nh h :: K₁)` after peeling a handleF head off Kᵢ? -/

namespace Bang
open Bang.EffectRow (Label)
variable {Eff  : Type} [Lattice Eff] [OrderBot Eff]
variable {Mult : Type} [CommSemiring Mult] [DecidableEq Mult]
variable [EffSig Eff Mult]

-- (a) nil base: StackInc (handleF nh h :: K₁) gives StackBelow nh K₁ directly (def head clause).
example {nh : Nat} {h : Handler} {K₁ : Stack}
    (hinc : StackInc (Frame.handleF nh h :: K₁)) : StackBelow nh K₁ := hinc.2

-- (b) nested: peel a handleF mh₁ head — StackInc (handleF mh₁ hh :: (Kᵢrest ++ handleF nh h :: K₁))
-- gives StackInc (Kᵢrest ++ handleF nh h :: K₁) [.1] AND StackBelow mh₁ (Kᵢrest ++ handleF nh h :: K₁) [.2].
example {mh₁ nh : Nat} {hh h : Handler} {Kᵢrest K₁ : Stack}
    (hinc : StackInc (Frame.handleF mh₁ hh :: (Kᵢrest ++ Frame.handleF nh h :: K₁))) :
    StackInc (Kᵢrest ++ Frame.handleF nh h :: K₁) ∧ StackBelow mh₁ (Kᵢrest ++ Frame.handleF nh h :: K₁) :=
  ⟨hinc.1, hinc.2⟩

-- (c) the letF/appF peel: StackInc (letF :: rest) = StackInc rest — passes the appended-stack invariant down.
example {N : Comp} {rest : Stack} (hinc : StackInc (Frame.letF N :: rest)) : StackInc rest := hinc

end Bang
