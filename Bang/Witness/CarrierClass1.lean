module

public import Bang.Meta.BinaryLR
public import Bang.Core.Semantics.Invariants

/-! # CarrierClass1 — Q3: does the class-2 fork resolve the class-1 reinstall/append `StackInc`
obligation, or does class-1 need its OWN carrier addition regardless?

## The class-1 obligation

The reinstall sites (`BinaryLR.lean:736/755/876/907/941/1432` and the deep `krelS_append` nested-arm
`671/672`) must feed `krelS_append` its explicit premise `StackInc (Kᵢ ++ handleF nh h :: K₁)`, where
`Kᵢ` is the resume conjunct's UNIVERSALLY-bound captured continuation (`hKi : KrelS m' Cᵢ C εᵢ g Kᵢ
Kᵢ'`). The clean combinator is `stackInc_append_of_above` (`Invariants.lean:357`):

    StackAbove nh Kᵢ  ∧  StackInc Kᵢ  ∧  StackInc K₁  ∧  StackBelow nh K₁  →  StackInc (Kᵢ ++ handleF nh h :: K₁)

Of the four antecedents, three are already in scope at the reinstall sites:
- `StackInc Kᵢ`  — `krelS_stackInc hKi` (the outer conjunct on the resume continuation)
- `StackInc K₁`  — `krelS_stackInc hK`  (the reinstalled tail)
- `StackBelow nh K₁` — `hsbK₁` (the reinstall lemma's threaded premise, `state_reinstall:708`)

The ONE missing antecedent is `StackAbove nh Kᵢ` — "every id in the captured continuation `Kᵢ`
exceeds the reinstalled catcher id `nh`."

## Q3 verdict (this file)

`StackAbove nh Kᵢ` is a fact about the resume conjunct's `Kᵢ` RELATIVE to the frame id `nh`. It is
NOT among the resume conjunct's hypotheses (which carry only `StackInc Kᵢ`, `nh`-agnostic), and it is
NOT supplied by either class-2 fork (both forks concern the MINT `StackBelow g` on the AMBIENT tail,
a different stack). So class-1 needs its OWN carrier addition — a per-frame conjunct on the resume
clause — INDEPENDENT of the class-2 (a)/(b) ruling. The witnesses:

1. `stackInc_not_above` — `StackInc Kᵢ` does NOT imply `StackAbove nh Kᵢ` (a `Kᵢ` with a small id
   `≤ nh` is `StackInc` yet not `StackAbove nh`). So the existing carrier is insufficient for class-1.

2. `class1_closes_given_above` — but GIVEN `StackAbove nh Kᵢ` (the missing per-frame fact), the
   `stackInc_append_of_above` combinator DOES close the class-1 obligation from the three in-scope
   antecedents. So the ONLY thing class-1 needs is the per-frame `StackAbove nh Kᵢ` on the resume
   conjunct. This is the shape-(i″) per-frame conjunct the ADR names — SELF-PROPAGATING once added
   (the recursive resume `KrelS m Cᵢ C εᵢ g Kᵢ Kᵢ'` would carry `StackAbove nh Kᵢ` for the nested
   arm, matching the `stackInc_gives_above` delivery from a machine-reached `StackInc`). -/

namespace Bang.Witness

open Bang
open Bang.EffectRow (Label)

variable {Eff  : Type} [Lattice Eff] [OrderBot Eff]
variable {Mult : Type} [CommSemiring Mult] [DecidableEq Mult]
variable [EffSig Eff Mult]

/-- **Witness 1 (`StackInc` ⇏ `StackAbove nh`).** The existing carrier gives `StackInc Kᵢ`, but the
class-1 append needs `StackAbove nh Kᵢ`. These are independent: `Kᵢ = [handleF 1 _]` is `StackInc`
(trivially — a singleton), yet for the reinstalled catcher `nh = 3` it is NOT `StackAbove 3`
(`¬ 3 < 1`). So class-1's missing antecedent is genuinely absent from the current carrier. -/
theorem stackInc_not_above :
    ∃ (nh : Nat) (Kᵢ : EvalCtx),
      Bang.StackInc Kᵢ ∧ ¬ Bang.StackAbove nh Kᵢ := by
  refine ⟨3, [Frame.handleF 1 (Handler.throws 0)], ?_, ?_⟩
  · exact ⟨trivial, trivial⟩   -- StackInc [handleF 1 _] = StackInc [] ∧ StackBelow 1 [] = True
  · intro h; exact absurd h.1 (by decide)   -- StackAbove 3 [handleF 1 _] = 3 < 1 ∧ … , FALSE

/-- **Witness 2 (`StackAbove nh Kᵢ` is EXACTLY the missing piece — class-1 then closes).** Given the
per-frame fact `StackAbove nh Kᵢ` plus the three in-scope antecedents, `stackInc_append_of_above`
discharges the class-1 obligation. This confirms: adding `StackAbove nh` to the resume conjunct's
`Kᵢ` (shape (i″) per-frame) closes ALL class-1 sites via the ALREADY-BANKED combinator — no new
strip infrastructure. Uses the real kernel combinator, so this is the genuine discharge shape. -/
theorem class1_closes_given_above
    {nh : Nat} {Kᵢ Kₒ : EvalCtx} {h : Handler}
    (habove : Bang.StackAbove nh Kᵢ)          -- the MISSING per-frame fact (add to resume conjunct)
    (hincI : Bang.StackInc Kᵢ)                -- krelS_stackInc hKi (in scope)
    (hincO : Bang.StackInc Kₒ)                -- krelS_stackInc hK  (in scope)
    (hsbO : Bang.StackBelow nh Kₒ) :          -- hsbK₁ (threaded reinstall premise, in scope)
    Bang.StackInc (Kᵢ ++ Frame.handleF nh h :: Kₒ) :=   -- exactly the class-1 `krelS_append` premise
  Bang.stackInc_append_of_above habove hincI hincO hsbO

end Bang.Witness

#print axioms Bang.Witness.stackInc_not_above
#print axioms Bang.Witness.class1_closes_given_above
