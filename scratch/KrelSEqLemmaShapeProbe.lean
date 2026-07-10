import Bang.Meta.LR
import Bang.Core.Semantics.Invariants

/-! # KrelSEqLemmaShapeProbe — slice-2 DESIGN FINDING (task #37, ADR-0096 (i′) StackInc).

The (i′) outer conjunct `(StackInc K₁ ∧ StackInc K₂) ∧ (match…)` on KrelS CANNOT be extracted
generically from an abstract-stack `KrelS n C D ε g K₁ K₂`: `rw [KrelS] at h` on all-variable
stacks fires the catch-all `| _, _ => False` arm (h : False), because the `match K₁ K₂` is stuck and
the equation compiler's all-variable equation is the last arm. So a generic
`krelS_gives_stackInc : KrelS … → StackInc K₁ ∧ StackInc K₂` is NOT available by unfold/projection.

CONSEQUENCE: the 4 eq-lemmas (krelS_nil/letF/appF/handleF) CANNOT stay byte-identical by "deriving the
outer conjunct from the tail-KrelS" (the derivation needs exactly that stuck extraction). The conjunct
must be EXPOSED explicitly in each eq-lemma's RHS → every destructure/construct consumer (the ~77 sites
across LR.lean+BinaryLR.lean) threads it. This is the confirmed slice-2 cost.

EXCEPTION that IS free: krelS_nil — StackInc [] = True on both sides, so `(True ∧ True) ∧ RHS`
simplifies to `RHS` by `simp only [StackInc, true_and, and_true]`; the nil eq-lemma stays
byte-identical, nil consumers unaffected. Only letF/appF/handleF (concrete non-empty heads) carry the
real conjunct.

The design is pinned: expose `(StackInc K₁' ∧ StackInc K₂')`-shaped conjuncts on letF/appF/handleF
eq-lemmas (the per-frame tail form, since StackInc(fr::K)=StackInc K for letF/appF and
=StackInc K ∧ StackBelow n K for handleF), thread through the ~77 consumers. -/

namespace Bang
open Bang.EffectRow (Label)
variable {Eff  : Type} [Lattice Eff] [OrderBot Eff]
variable {Mult : Type} [CommSemiring Mult] [DecidableEq Mult]
variable [EffSig Eff Mult]

-- the per-frame StackInc reductions the eq-lemmas will use (all definitional).
example {N : Comp} {K : Stack} : StackInc (Frame.letF N :: K) = StackInc K := rfl
example {w : Val} {K : Stack} : StackInc (Frame.appF w :: K) = StackInc K := rfl
example {nid : Nat} {h : Handler} {K : Stack} :
    StackInc (Frame.handleF nid h :: K) = (StackInc K ∧ StackBelow nid K) := rfl
example : StackInc ([] : Stack) = True := rfl

end Bang
