module

public import Bang.Meta.BinaryLR
public import Bang.Core.Semantics.Invariants

/-! # AnswerForkDecomp — the DECISIVE experiment: does the FULL `krelS_splitAtId_decomp` (inner
relation `hin` at answer `Dᵢ` + resume conjunct `hres2`) discharge the `crelK_fund_up` resume arm,
or does an ANSWER-TYPE obligation remain?

The census wall claims `crelK_fund_up` needs `KrelS m' Cᵢ' Dᵢ g K₁ᵢ K₂ᵢ` (inner, answer `Dᵢ`) and
re-answering `D → Dᵢ` is the route-A refutation. BUT `krelS_splitAtId_decomp` ALREADY produces an
inner relation `hin : KrelS n C Dᵢ e g K₁ᵢ K₂ᵢ` at answer `Dᵢ` (its own existential). This file tests
whether that inner + the decomp's resume conjunct COMPOSE — isolating the residual obligation as a
`sorry`, so its SHAPE is machine-visible. -/

namespace Bang.Witness.AnswerForkDecomp

open Bang
open Bang.EffectRow (Label)

variable {Eff  : Type} [Lattice Eff] [OrderBot Eff]
variable {Mult : Type} [CommSemiring Mult] [DecidableEq Mult]
variable [EffSig Eff Mult]

/-! ## The decomp OUTPUT shape (re-stated from `krelS_splitAtId_decomp`).

From `KrelS n C D e g K₁ K₂` + `splitAtId K₁ nid = some (K₁ᵢ, h, K₁ₒ)`:
  `∃ K₂ᵢ K₂ₒ h' Dᵢ C' e',  splitAtId K₂ nid = some (K₂ᵢ, h', K₂ₒ) ∧ HandlerRel n h h'
     ∧ KrelS n C Dᵢ e g K₁ᵢ K₂ᵢ            -- hin: INNER at hole C, answer Dᵢ
     ∧ KrelS n C' D e' g K₁ₒ K₂ₒ           -- htail2: OUTER at answer D
     ∧ (resume conjunct at answer Dᵢ → ... → KrelS m (F qᵣ Aᵣ) D eₛ g Sᵢ Sᵢ')`

The resume conjunct's PREMISE (to fire it): `KrelS m Cᵢ' Dᵢ εᵢ' g Kᵢ Kᵢ'` with `Kᵢ = K₁ᵢ` (the
dispatch's captured continuation IS the inner prefix). SO the premise's inner is at answer `Dᵢ` — and
`hin` IS at answer `Dᵢ`. THE TEST: are `hin`'s hole `C` and the premise's hole `Cᵢ'` reconcilable?

In `crelK_fund_up` the focus is `perform … op v : F q B` with `B = opRes ℓ op`, so `C = F q B` = the
op-result returner. The resume premise's hole `Cᵢ' = F qᵣ Aᵣ` with `Aᵣ = opRes ℓ op = B` (the same op).
SO `Cᵢ' = F qᵣ B` and `C = F q B` — they agree UP TO the returner grade `qᵣ` vs `q`. Is that grade
forced equal? Test below. -/

/-- **THE DECISIVE CHECK.** Given the decomp's inner `hin : KrelS m (CTy.F q B) Dᵢ e g K₁ᵢ K₂ᵢ` (hole
`F q B`, answer `Dᵢ`), can it serve the resume conjunct's premise `KrelS m (CTy.F qᵣ B) Dᵢ εᵢ' g K₁ᵢ
K₂ᵢ` (hole `F qᵣ B`, answer `Dᵢ`)? The hole grades `q` vs `qᵣ` are the ONLY difference; the answer
`Dᵢ` and the type `B` and the stacks MATCH. If `KrelS` is invariant under the hole GRADE (a returner
grade re-cast on the FIRST arg) then the decomp inner directly serves — NO answer-type wall, the
census diagnosis is REFINED. Isolate the obligation as a sorry to see if that grade-recast is the
ONLY residual. -/
theorem decomp_inner_serves_resume_premise
    {m : Nat} {q qᵣ : Mult} {B : VTy Eff Mult} {Dᵢ : CTy Eff Mult} {e εᵢ' : Eff} {g : Nat}
    {K₁ᵢ K₂ᵢ : Stack}
    (hin : KrelS m (CTy.F q B) Dᵢ e g K₁ᵢ K₂ᵢ) :
    KrelS m (CTy.F qᵣ B) Dᵢ εᵢ' g K₁ᵢ K₂ᵢ := by
  -- If this closes with NO answer-type hypothesis, the census "answer-type wall" is DISSOLVED for the
  -- decomp route — the residual is only a hole-GRADE + row recast, not a `D → Dᵢ` re-answering.
  -- If it does NOT close (grade/row genuinely gate the KrelS content), the residual is characterized.
  sorry

/-! ## Interpretation harness — the grade/row recast, isolated.

`KrelS`'s FIRST arg (hole `C`) is CONSUMED in the match: at nil `C = D`; at letF `∃ q A, C = F q A`;
at appF `∃ q A B, C = arr …`; at handleF the hole is THREADED unchanged. So changing the hole from
`F q B` to `F qᵣ B` at a NON-nil, non-letF/appF stack (a handleF-headed or empty-after-frames) MAY be
free; at a nil `K₁ᵢ = []` it forces `F q B = Dᵢ` AND `F qᵣ B = Dᵢ`, hence `q = qᵣ`. So the grade
recast is FREE iff `q = qᵣ` OR `K₁ᵢ` is non-nil. Record the nil-forced grade equality below. -/

/-- At a NIL inner prefix, `hin` forces `F q B = Dᵢ` (nil base `C = D`), and the premise forces
`F qᵣ B = Dᵢ`. Chaining: `q = qᵣ`. So the grade recast is nil-forced — NOT free in general, but the
obstruction is a GRADE equality `q = qᵣ`, NOT an answer-type re-answering `D → Dᵢ`. This REFINES the
census wall: the residual (if any) is a returner-grade coherence, in the same tractability class as
the state/txn reinstall (which fix the grade by `rfl`), not the refuted cross-answer equation. -/
theorem nil_forces_grade_equality
    {m : Nat} {q qᵣ : Mult} {B : VTy Eff Mult} {Dᵢ : CTy Eff Mult} {e εᵢ' : Eff} {g : Nat}
    (hin : KrelS m (CTy.F q B) Dᵢ e g [] [])
    (hprem : KrelS m (CTy.F qᵣ B) Dᵢ εᵢ' g [] []) :
    q = qᵣ := by
  rw [krelS_nil] at hin hprem
  -- hin.1 : F q B = Dᵢ ; hprem.1 : F qᵣ B = Dᵢ
  have h1 := hin.1
  have h2 := hprem.1
  rw [← h2] at h1
  rw [CTy.F.injEq] at h1
  exact h1.1

end Bang.Witness.AnswerForkDecomp
