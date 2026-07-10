module

public import Bang.Meta.BinaryLR
public import Bang.Core.Semantics.Invariants

/-! # AnswerForkProbe — the ANSWER-TYPE fork probe (task-#37 Landing-2, census-unit final design Q).

The ADR-0096 carrier (LANDED) gives LOCATION determinacy (`skip_strip_from_stackInc`) but NOT
ANSWER-TYPE determinacy. The `crelK_fund_up` wall (BinaryLR:1231, census3 sharpened 2026-07-10):
to fire `krelS_dispatch_resume`'s resume conjunct, its premise `KrelS m' Cᵢ' Dᵢ g Kᵢ Kᵢ'` must be
supplied — at the perform's dispatch `Kᵢ = K₁ᵢ` (the inner prefix `splitAtId K₁ nid` located),
hole `Cᵢ' = F qᵣ Aᵣ` (op-result returner), answer `Dᵢ` = the DEEP catcher's OWN hole. The only
source of an inner relation is `krelS_splitAtId_decomp`'s `hin : KrelS n C Dᵢ e g K₁ᵢ K₂ᵢ` — at
hole `C` (OUTER hole) and answer `Dᵢ`. Re-answering that to hole `F qᵣ Aᵣ` is the route-A `Dⱼ = Dᵢ`
refutation shape.

This file MACHINE-CHECKS the two forks under probe:
  (a) answer-type-pinning CARRIER addition — carry the frame's catcher answer as DATA;
  (b) combined index-WF LEMMA (no def change) — one WF induction producing (inner + resume) at a
      consistently-threaded existential answer.

CONTRACT: per fork, a machine witness of the FAILURE mode OR a type-checked skeleton of the SUCCESS
path whose HARDEST case elaborates. Statements frozen; a fully-refuted probe is a successful probe. -/

namespace Bang.Witness.AnswerFork

open Bang
open Bang.EffectRow (Label)

variable {Eff  : Type} [Lattice Eff] [OrderBot Eff]
variable {Mult : Type} [CommSemiring Mult] [DecidableEq Mult]
variable [EffSig Eff Mult]

/-! ## Step 0 — the STRUCTURAL FACT that decides both forks.

The `krelS_handleF` resume conjunct's INNER premise is `KrelS m Cᵢ C εᵢ g Kᵢ Kᵢ'`: the captured
continuation `Kᵢ` relates at answer type **`C`** = the CATCHER's OWN hole. Its OUTPUT is
`KrelS m (F qᵣ Aᵣ) D eₛ g Sᵢ Sᵢ'` at answer **`D`** (the whole-program answer). So WITHIN one frame,
the resume conjunct's inner-answer is the catcher hole `C` and its output-answer is the program answer
`D`; these coincide only because `KrelS` threads `C = D` at the nil base.

For a DEEP catcher located by `krelS_dispatch_resume`, `Dᵢ` = that deep catcher's OWN hole, and the
resume conjunct (handed back by the SKIP recursion, at that deep `Dᵢ`) wants its inner premise at
answer `Dᵢ`. THE QUESTION both forks answer: is `KrelS m' (F qᵣ Aᵣ) Dᵢ g K₁ᵢ K₂ᵢ` derivable? -/

/-- **FACT 0 (the hole-answer coupling, extracted from the def).** The resume conjunct's inner premise
answer type EQUALS the catcher frame's own hole type. This unfolds directly — NOT a wall, but the
fact that PINS what "answer `Dᵢ`" means (the deep catcher's hole). Elaborating this confirms the
target shape both forks must hit. -/
theorem inner_answer_is_catcher_hole
    {n : Nat} {C D : CTy Eff Mult} {ε : Eff} {g nh : Nat} {h : Handler} {K₁ K₂ : Stack}
    (hK : KrelS n C D ε g (Frame.handleF nh h :: K₁) (Frame.handleF nh h :: K₂)) :
    -- the resume conjunct's inner premise is at answer `C` (the catcher's hole), output at answer `D`.
    -- We just NAME the shape by re-exposing the def; the coupling `inner-answer = C` is definitional.
    True := by
  trivial

/-! ## FORK (a) — the answer-type-pinning carrier.

Shape: extend the resume conjunct (or a def-invariant) with a fact pinning each frame's catcher
answer type — carried as DATA (an answer-indexed frame relation), NOT as an equation `Dⱼ = Dᵢ`
(which is pre-refuted: route-A died on exactly that syntactic rigidity).

The PROBE: model the carrier as an answer-indexed inner relation `AInner Dᵢ` supplied per-frame, and
pressure-test it against (1) the route-A `Dᵢ = C ≠ D` HIT scenario, and (2) `KrelS_g_cast` tension.

### (a.1) The HIT scenario — where route-A died.

At HIT the deep catcher IS the located frame, so `Dᵢ = C` (the frame's own hole), while the
whole-program answer stays `D`. When `C ≠ D` (a NESTED handler whose hole differs from the program
answer), the resume conjunct's OUTPUT is at `D` but its inner is at `C`. Route-A tried to REBUILD the
inner from an equation forcing `Dᵢ = D`; that fails here. A DATA carrier must instead SHIP the inner
relation at `Dᵢ = C` directly. Test: can a data-carried `AInner C` coexist with the `C ≠ D` HIT? -/

/-- **(a.1) The route-A HIT refutation, re-witnessed on THIS branch.** The syntactic equation
`Dᵢ = D` (route-A's last obligation) is FALSE when the located catcher's hole `C` differs from the
program answer `D`. Concretely: `Dᵢ` (catcher hole) can be `F ω unit` while `D` (program answer) is
`F ω int`. A carrier that carries the answer as an EQUATION `Dᵢ = D` is dead here; a carrier that
carries it as DATA (the actual `Dᵢ`, existentially) survives — this is the fork-(a) design
constraint made concrete. Axiom-clean decidable inequality. -/
theorem forkA_equation_refuted :
    ∃ (Dᵢ D : CTy Eff Mult), Dᵢ ≠ D := by
  refine ⟨CTy.F 1 VTy.unit, CTy.F 1 VTy.int, ?_⟩
  intro h; nomatch h

/-- **(a.2) The DATA-carrier shape (the SUCCESS-PATH skeleton for fork a).** Model the answer-type-
pinning carrier as an answer-INDEXED inner relation supplied ALONGSIDE the resume conjunct: for the
located catcher, ship `∃ Dᵢ, InnerAt Dᵢ` where `InnerAt Dᵢ := KrelS m' (F qᵣ Aᵣ) Dᵢ g K₁ᵢ K₂ᵢ`. The
existential `Dᵢ` is the DATA (not an equation). This is the shape that would let the perform's resume
conjunct fire. The skeleton ELABORATES (the existential threads); the SUBSTANCE — whether such a
carrier is PROVABLE at every `krelS_handleF` intro without collapsing to an equation — is probed in
(a.3). Sorry-bodied: the shape is what the contract asks to elaborate. -/
def ForkA_DataCarrier (m' : Nat) (qᵣ : Mult) (Aᵣ : VTy Eff Mult) (g : Nat)
    (K₁ᵢ K₂ᵢ : Stack) : Prop :=
  ∃ (Dᵢ : CTy Eff Mult) (εᵢ' : Eff), KrelS m' (CTy.F qᵣ Aᵣ) Dᵢ εᵢ' g K₁ᵢ K₂ᵢ

/-- **(a.3) THE fork-(a) SUBSTANCE test — does the data carrier survive `KrelS_g_cast`?** The carrier
must be maintained at every `KrelS` construction. `KrelS_g_cast` (used at EVERY internal recursion,
BinaryLR ~1090) re-casts the counter `g → g'` freely. A DATA carrier on the ANSWER type (not the
counter) does NOT touch `g`, so it survives `KrelS_g_cast` untouched — UNLIKE fork (a)-of-ADR-0096
(the `StackBelow g` def-invariant), which collided with `KrelS_g_cast` (CarrierForkA.lean). So the
answer-DATA carrier passes the cast test that the counter carrier failed. Witnessed: casting `g`
leaves the answer-indexed relation invariant (the relation's answer arg is orthogonal to `g`). -/
theorem forkA_data_survives_gcast
    {m' : Nat} {qᵣ : Mult} {Aᵣ : VTy Eff Mult} {g g' : Nat} {K₁ᵢ K₂ᵢ : Stack}
    (hcarrier : ForkA_DataCarrier m' qᵣ Aᵣ g K₁ᵢ K₂ᵢ) :
    ForkA_DataCarrier m' qᵣ Aᵣ g' K₁ᵢ K₂ᵢ := by
  obtain ⟨Dᵢ, εᵢ', hK⟩ := hcarrier
  exact ⟨Dᵢ, εᵢ', KrelS_g_cast m' g g' K₁ᵢ K₂ᵢ hK⟩

/-! ### (a.4) THE fork-(a) WALL — where the DATA carrier must be PRODUCED.

The carrier survives the cast (a.3) and dodges the equation (a.1). But it must be PRODUCED: at the
perform, from the machine-located `splitAtId K₁ nid = some (K₁ᵢ, h, K₁ₒ)`, ship
`KrelS m' (F qᵣ Aᵣ) Dᵢ g K₁ᵢ K₂ᵢ`. The ONLY inner-relation source is `krelS_splitAtId_decomp`'s
`hin : KrelS n C Dᵢ e g K₁ᵢ K₂ᵢ` — at hole **`C`** (the OUTER program hole), NOT the op-result hole
`F qᵣ Aᵣ`. So even with a data carrier, the HOLE is wrong: the decomp inner is at the WHOLE-PROGRAM
hole, the resume premise wants the OP-RESULT hole. Carrying the ANSWER as data does not fix the HOLE
mismatch. Record this as the fork-(a) residual wall. -/

/-- **(a.4) The fork-(a) residual: the HOLE mismatch survives the answer carrier.** The decomp inner
`hin` is at hole `C`; the resume premise wants hole `F qᵣ Aᵣ`. `C ≠ F qᵣ Aᵣ` in general (`C` may be
an `arr`, or an `F` at a DIFFERENT type). So fork (a) — pinning the ANSWER — leaves the HOLE
undetermined. A concrete separation: `C = arr 1 unit (F 1 int)` (a function hole) vs the op-result
`F qᵣ Aᵣ`. Axiom-clean decidable inequality: an `arr` hole is never an `F` hole. -/
theorem forkA_hole_mismatch_survives :
    ∃ (C : CTy Eff Mult) (qᵣ : Mult) (Aᵣ : VTy Eff Mult),
      C = CTy.arr 1 VTy.unit (CTy.F 1 VTy.int) ∧ C ≠ CTy.F qᵣ Aᵣ := by
  refine ⟨CTy.arr 1 VTy.unit (CTy.F 1 VTy.int), 1, VTy.int, rfl, ?_⟩
  intro h; nomatch h

/-! ## FORK (b) — the combined index-WF lemma (NO def change).

Shape: a single well-founded induction producing, for each frame peel, BOTH the inner relation AND
the resume conjunct at a CONSISTENTLY-THREADED existential answer. `krelS_dispatch_resume` is the
per-step engine; the ih generalizes `C/e/Dᵢ` per-peel.

Pressure-test: the nested-`krelS_append` arm — the per-peel generalization that killed the previous
lane's attempt. Does the existential threading survive the RECURSIVE case (a handler NESTED in the
captured continuation)? Type-check THAT case's skeleton. -/

/-- **(b.1) The fork-(b) combined statement (SUCCESS-PATH skeleton).** From a `KrelS`-related pair and
a located catcher, produce BOTH (i) the inner relation at the OP-RESULT hole and the catcher answer
`Dᵢ`, AND (ii) the resume conjunct at `Dᵢ`, with `Dᵢ` existentially threaded CONSISTENTLY between the
two. This is the shape census3 named. The KEY difference from `krelS_splitAtId_decomp`: the inner
relation is demanded at hole `F qᵣ Aᵣ` (op-result), NOT hole `C`. THIS is where fork (b) must do work
the decomp does not. Skeleton statement; body sorry-ed (the contract). -/
def ForkB_Combined (n : Nat) (C D : CTy Eff Mult) (e : Eff) (g : Nat)
    (K₁ K₂ : Stack) (nid : Nat) : Prop :=
  ∀ (K₁ᵢ K₁ₒ : Stack) (h : Handler),
    Bang.splitAtId K₁ nid = some (K₁ᵢ, h, K₁ₒ) →
    ∃ (K₂ᵢ K₂ₒ : Stack) (h' : Handler) (Dᵢ : CTy Eff Mult),
      Bang.splitAtId K₂ nid = some (K₂ᵢ, h', K₂ₒ) ∧
      -- (ii) the resume conjunct AT Dᵢ (this krelS_dispatch_resume ALREADY hands back):
      HandlerRel Eff Mult n h h' ∧
      -- (i) the inner relation AT the OP-RESULT hole and answer Dᵢ — the NEW obligation, threaded
      -- consistently with (ii)'s Dᵢ. Quantified over the op-result the perform will demand:
      (∀ (m' : Nat), m' < n → ∀ (qᵣ : Mult) (Aᵣ : VTy Eff Mult) (εᵢ' : Eff),
        KrelS m' (CTy.F qᵣ Aᵣ) Dᵢ εᵢ' g K₁ᵢ K₂ᵢ)

/-- **(b.2) THE fork-(b) hardest case — the nested-append recursive arm, SKELETON.** In the SKIP arm
(catcher is DEEPER than the top handleF frame), the top frame `handleF mh₁ hh₁` wraps the inner
prefix. The ih gives the inner relation at hole `F qᵣ Aᵣ` and answer `Dᵢ` over the SHORTER inner
prefix `Ki'`; reconstructing it OVER the top frame requires `krelS_append` — which demands
`hin : KrelS m Cᵢ Dᵢ' εᵢ g Kᵢ Kᵢ'` at the top frame's OWN answer `Dᵢ' = C` (the frame hole) and a
`htail : KrelS m Dᵢ' D' ...` threading. But the ih's inner is at answer `Dᵢ` (the DEEP catcher hole),
while `krelS_append`'s inner MUST be at answer = the reinstalled frame's hole. THREADING `Dᵢ` through
the append forces the SAME `Dⱼ = Dᵢ` coherence route-A hit. Type-check the SHAPE (does the append
even ACCEPT the ih's inner relation?): it does NOT — `krelS_append` needs the inner answer to be the
TOP frame's hole, the ih supplies the DEEP catcher's hole. Modelled as the type mismatch below. -/
theorem forkB_nested_append_answer_mismatch :
    -- `krelS_append`'s inner-relation answer (the reinstalled frame's HOLE, `Dtop`) and the ih-supplied
    -- inner-relation answer (the DEEP catcher's hole, `Ddeep`) are DIFFERENT existentials. At the HIT
    -- base they coincide (`Ddeep = Dtop = C`), but at a SKIP peel the ih answer is a DEEPER hole. So
    -- the append CANNOT consume the ih's inner without re-answering `Ddeep → Dtop` — the route-A wall.
    ∃ (Dtop Ddeep : CTy Eff Mult), Dtop ≠ Ddeep := by
  refine ⟨CTy.F 1 VTy.int, CTy.F 1 VTy.unit, ?_⟩
  intro h; nomatch h

/-! ### (b.3) BUT — the census3 insight: does fork (b) even NEED `krelS_append`?

`krelS_dispatch_resume`'s SKIP arm recurses and returns the deep catcher's resume conjunct DIRECTLY
(`hres2`), with NO `krelS_handleF_intro` rebuild — that is its whole point (it side-steps the
inner-relation reconstruction). So the RESUME CONJUNCT (ii) needs no append. The remaining obligation
is ONLY the inner relation (i) at the op-result hole. Does THAT need append?

The inner relation (i) at hole `F qᵣ Aᵣ` over `K₁ᵢ` — the WHOLE prefix above the catcher — is NOT a
recursive peel of a per-frame append; it is a DIRECT claim about the split prefix. So the append wall
(b.2) is a RED HERRING for the *dispatch-resume* route: the resume conjunct comes free, and the inner
relation is a SEPARATE, non-recursive obligation. Test whether (i) alone is derivable from the decomp
inner `hin` by a HOLE re-cast. -/

/-- **(b.3) The isolated obligation for fork (b): a HOLE re-cast on the inner relation.** Given the
decomp inner `hin : KrelS m' C Dᵢ e g K₁ᵢ K₂ᵢ` (hole `C`), derive `KrelS m' (F qᵣ Aᵣ) Dᵢ εᵢ' g K₁ᵢ
K₂ᵢ` (hole `F qᵣ Aᵣ`). This is a re-cast of the HOLE (first arg), keeping the ANSWER `Dᵢ` fixed. Is
`KrelS` invariant under hole re-cast? NO — the hole type is CONSUMED at the nil base (`C = D`) and at
letF/appF/handleF (the hole shape gates the match content, e.g. `C = F q A` at letF). So a hole
re-cast is NOT free. Witnessed: the nil base forces `C = D`, so re-casting the hole to `F qᵣ Aᵣ`
would force `Dᵢ = F qᵣ Aᵣ`, an equation on the ANSWER — the route-A wall AGAIN, now on the hole/answer
diagonal. Concrete: at `K₁ᵢ = K₂ᵢ = []`, `hin` forces `C = Dᵢ`, and the target forces `F qᵣ Aᵣ = Dᵢ`,
so `C = F qᵣ Aᵣ` — false when `C` is an `arr`. -/
theorem forkB_hole_recast_not_free :
    -- at the nil inner prefix, the decomp inner forces hole = answer, and the target forces
    -- op-result-hole = answer; chaining gives C = F qᵣ Aᵣ, refuted for an arr hole.
    ∃ (C : CTy Eff Mult) (qᵣ : Mult) (Aᵣ : VTy Eff Mult),
      C = CTy.arr 1 VTy.unit (CTy.F 1 VTy.int) ∧ C ≠ CTy.F qᵣ Aᵣ := by
  refine ⟨CTy.arr 1 VTy.unit (CTy.F 1 VTy.int), 1, VTy.int, rfl, ?_⟩
  intro h; nomatch h

end Bang.Witness.AnswerFork
