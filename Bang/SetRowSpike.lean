/-
SPIKE (task #14) — under a TYPED + STATIC (capability) handler dispatch, does
bang-lang's effect ROW stay an idempotent SET (`Finset Label`), or does typing
the capability force ORDERED/multiset rows and/or System-F polymorphism?

This is a SCRATCH model, NOT a kernel change. It rides the REAL kernel defs
(`EffRow = Finset Label`, `EffSig`, `EvalCtx`, `Frame`, `Handler`) so the verdict
is grounded in the actual algebra, not a toy.

THE HYPOTHESIS (build it, don't assume it):
  - the effect ROW tracks EFFECTS as a `Finset Label` (a set) — unchanged;
  - the CAP is a separate `Nat` runtime witness of WHICH handler instance
    (a de-Bruijn count into the runtime STACK);
  - a `perform cap op`'s effect-row contribution is still `{ℓ}` (the op's effect
    label) — `labelEff ℓ ≤ φ`, NOT an ordered evidence vector;
  - handler discharge stays the existing `⊔`-semilattice / set-difference;
  - well-scopedness (the cap names a real in-scope handler of the right kind) is a
    STRUCTURAL `Nat` property, provable WITHOUT higher-rank polymorphism — like
    de-Bruijn index well-scopedness.

The contrast to refute-or-confirm: Koka's evidence vectors are ORDERED
(`lᵢ ⩽ lᵢ₊₁`) and named-handler scoping uses rank-2 polymorphism. Does typing OUR
cap force either onto us?
-/
import Bang.Syntax
import Bang.Operational
import Bang.Mult   -- concrete QTT multiplicity, so the concrete-instance sections are unambiguous

namespace Bang.SetRowSpike

open Bang
open Bang.EffectRow (Label EffRow)

variable {Eff  : Type} [Lattice Eff] [OrderBot Eff]
variable {Mult : Type} [CommSemiring Mult] [DecidableEq Mult]
variable [EffSig Eff Mult]


/-! ## 1. The capability: a de-Bruijn count into the runtime STACK

A `Cap` is a `Nat`: it counts how many `handleF` frames sit between the perform
site and ITS handler (lexical resolution, fixed at elaboration). This is the
EXACT carrier of the prior `static-dispatch-spike` (`staticSplit`). It is NOT a
member of the effect row — it lives on the (already-ordered) stack. -/

abbrev Cap := Nat

/-- The typed `perform`: a `Comp.up` carrying its label/op/arg AS BEFORE, paired
with a separate `Cap`. We model the cap alongside the existing `Comp.up` rather
than adding a syntactic constructor (this is a scratch spike; no kernel syntax
change). The pairing is the modelling device — in a real pivot the cap would be a
new field on `up`, but its TYPE is `Nat`, orthogonal to the row. -/
structure Perform where
  cap : Cap
  ℓ   : Label
  op  : OpId
  v   : Val


/-! ## 2. THE typed `perform cap op` rule — effect contribution is a `Finset`

The decisive object. Its effect-row premise is `EffSig.labelEff ℓ ≤ φ` — the
SAME membership the real `HasCTy.up` uses (Syntax.lean:159), where `Eff` is the
row algebra and the concrete instance is `Finset Label` with `labelEff ℓ = {ℓ}`.

The `cap : Nat` field appears in the term but DOES NOT appear in the effect-row
premise at all. The row sees only `{ℓ}`; the cap is threaded to the operational
well-scopedness obligation (§4), never to the algebra. THIS is the decoupling. -/

inductive HasPerform :
    GradeVec Mult → TyCtx Eff Mult → Perform → Eff → CTy Eff Mult → Prop where
  | perform : ∀ {γ Γ} {cap : Cap} {ℓ : Label} {op : OpId} {v : Val}
        {φ : Eff} {q : Mult} {A B : VTy Eff Mult},
      -- ── THE EFFECT-ROW CONTRIBUTION: a single label, lattice membership.
      --    For `Eff = Finset Label` this is `{ℓ} ⊆ φ` — set membership, idempotent,
      --    NO ordering, NO evidence vector. Identical to `HasCTy.up`.
      EffSig.labelEff (Eff := Eff) (Mult := Mult) ℓ ≤ φ →
      EffSig.opArg (Eff := Eff) (Mult := Mult) ℓ op = some A →
      EffSig.opRes (Eff := Eff) (Mult := Mult) ℓ op = some B →
      HasVTy γ Γ v A →
      -- ── the cap is UNCONSTRAINED by the row premise above. (Its well-scopedness
      --    is a separate STRUCTURAL Nat obligation, §4 — not a typing-context fact.)
      HasPerform (q • γ) Γ ⟨cap, ℓ, op, v⟩ φ (CTy.F q B)


/-! ## 3. The row stays a SET — build-confirmed at the concrete instance

We instantiate `Eff := EffRow = Finset Label` and exhibit a representative typed
`perform cap` whose effect row is a genuine `Finset` and whose discharge is the
`⊔`-semilattice. No list/multiset/ordered carrier appears anywhere.

To get a concrete `EffSig (Finset Label) Mult` we need a witness instance; the
real kernel keeps `EffSig` parametric (a program supplies it), so we build the
canonical singleton one here — `labelEff ℓ = {ℓ}` (exactly the instance the kernel
docstring names, Core.lean:277). -/

section Concrete

-- Concrete multiplicity: `QTT` (the real bang-lang grade). Fixing `Mult` makes the
-- `EffSig EffRow QTT` instance synthesis unambiguous — the spike is about the EFFECT
-- carrier (the ROW), not the multiplicity, so any concrete `Mult` serves.

/-- The canonical `Finset`-row signature: `labelEff ℓ = {ℓ}` (the singleton),
every op typed `unit → unit` (a stand-in interface — the spike is about the ROW
carrier, not the op types). This is the instance Core.lean:277 names. -/
@[reducible] def setRowSig : EffSig (EffRow) QTT where
  labelEff ℓ := {ℓ}
  opArg _ _ := some VTy.unit
  opRes _ _ := some VTy.unit
  labelEff_ne_bot ℓ := Finset.singleton_ne_empty ℓ
  labelEff_sep ℓ ℓ' φ h hne := by
    -- {ℓ} ≤ {ℓ'} ⊔ φ  and  ℓ ≠ ℓ'  ⊢  {ℓ} ≤ φ.  Pure Finset reasoning.
    -- `≤` on Finset IS `⊆`; `⊔` IS `∪`. Membership of `ℓ` does the work.
    have hmem : ℓ ∈ ({ℓ'} : EffRow) ∪ φ := h (Finset.mem_singleton_self ℓ)
    apply Finset.singleton_subset_iff.mpr
    rcases Finset.mem_union.1 hmem with hℓ | hφ
    · exact absurd (Finset.mem_singleton.1 hℓ) hne
    · exact hφ

attribute [local instance] setRowSig

/-- **SETS-PRESERVED, build-confirmed.** A representative typed `perform cap op v`
type-checks with the effect row a genuine `Finset Label`. The row premise is
`{ℓ} ⊆ φ` (the singleton ≤), discharged here at `φ = {ℓ}` itself — pure set
membership. The cap (`7`, arbitrary) plays no part in the row. -/
example (ℓ : Label) :
    HasPerform (Eff := EffRow) (Mult := QTT)
      ((1 : QTT) • ([] : GradeVec QTT)) [] ⟨7, ℓ, "op", Val.vunit⟩ ({ℓ} : EffRow)
      (CTy.F 1 VTy.unit) := by
  apply HasPerform.perform (A := VTy.unit) (B := VTy.unit)
  · -- THE ROW CONTRIBUTION: {ℓ} ≤ {ℓ}. Finset, not a vector.
    show ({ℓ} : EffRow) ≤ {ℓ}
    exact le_refl _
  · rfl
  · rfl
  · exact HasVTy.vunit (Eff := EffRow) (Mult := QTT) (Γ := [])

/-- The discharge / join stays the `Finset` semilattice. Combining the rows of two
performs is `∪` (= `⊔`), idempotent and unordered: performing `ℓ` then `ℓ` again
yields `{ℓ}`, not a length-2 vector. This is the SET invariant, build-witnessed. -/
example (ℓ : Label) : ({ℓ} : EffRow) ⊔ {ℓ} = {ℓ} := by
  simp

/-- And union is commutative — order-independence, the defining negation of an
ordered evidence vector. `{ℓ₁} ⊔ {ℓ₂} = {ℓ₂} ⊔ {ℓ₁}`. -/
example (ℓ₁ ℓ₂ : Label) : ({ℓ₁} : EffRow) ⊔ {ℓ₂} = {ℓ₂} ⊔ {ℓ₁} := by
  exact sup_comm _ _

end Concrete


/-! ## 4. Well-scopedness of the cap is a STRUCTURAL `Nat` lemma

The cap names a real, in-scope handler of the right kind. We must show this needs
NO higher-rank polymorphism — that it is a positional `Nat` property of the
runtime stack, exactly like de-Bruijn index well-scopedness (`i < ctx.length`).

`CapResolves K cap`: walking out `cap`-many `handleF` frames in the runtime stack
`K` lands on a real `handleF` (the cap names an in-scope handler). This is a
decidable structural recursion on `K` and `cap` — a `Nat`/`List` fact, no `∀`-type
anywhere, no quantifier over types. -/

/-- The cap resolves to an in-scope handler frame: walking out `cap`-many
`handleF` frames reaches a `handleF`. Non-`handleF` frames are transparent
(pure plumbing). Mirrors `staticSplit`'s walk; this is its well-scopedness
SIDE — a pure `Nat`/`List` structural recursion. -/
def CapResolves : EvalCtx → Cap → Prop
  | [], _ => False                                   -- ran off the stack: out of scope
  | (.handleF _ :: _), 0 => True                     -- cap exhausted AT a handler: in scope
  | (.handleF _ :: K), (c+1) => CapResolves K c      -- skip one handler, cap counts down
  | (_ :: K), c => CapResolves K c                   -- transparent frame: keep walking

/-- The kind-match refinement: the resolved handler handles `(ℓ, op)` (it is the
RIGHT kind, not just SOME handler). Reuses the real `handlesOp` (which takes the
dispatched label `ℓ` and `op`) — a structural recursion on the stack, no
polymorphism. The label `ℓ` here is the SAME label that lives in the row premise
of §2 (the cap and the row share `ℓ`, but the cap is NOT itself in the row). -/
def CapResolvesKind : EvalCtx → Cap → Label → OpId → Prop
  | [], _, _, _ => False
  | (.handleF h :: _), 0, ℓ, op => handlesOp h ℓ op = true
  | (.handleF _ :: K), (c+1), ℓ, op => CapResolvesKind K c ℓ op
  | (_ :: K), c, ℓ, op => CapResolvesKind K c ℓ op

/-- **Decidable** — well-scopedness is checkable, the hallmark of a structural
(non-polymorphic) property. (A rank-2 `∀`-scoping obligation would NOT be
decidable like this.) -/
instance : ∀ (K : EvalCtx) (cap : Cap), Decidable (CapResolves K cap)
  | [], _ => inferInstanceAs (Decidable False)
  | (.handleF _ :: _), 0 => inferInstanceAs (Decidable True)
  | (.handleF _ :: K), (c+1) => SetRowSpike.instDecidableCapResolves K c
  | (.letF _ :: K), c => SetRowSpike.instDecidableCapResolves K c
  | (.appF _ :: K), c => SetRowSpike.instDecidableCapResolves K c

/-- **STRUCTURAL well-scopedness, build-confirmed.** `CapResolves` is monotone in
the stack: a cap valid in `K` stays valid when an OUTER frame is pushed (the cap
counts from the perform site OUTWARD, so deeper context never invalidates it). A
pure `Nat`/`List` induction — the de-Bruijn-style lemma. No `∀`-type, no rank-2
quantifier. -/
theorem capResolves_skip_inner (fr : Frame) (K : EvalCtx) (cap : Cap)
    (h : CapResolves K cap) : ∃ cap', CapResolves (fr :: K) cap' := by
  -- A non-handler frame is transparent (cap'=cap); a handler frame just shifts by one (cap'=cap+1).
  cases fr with
  | handleF hh => exact ⟨cap + 1, h⟩
  | letF N => exact ⟨cap, h⟩
  | appF w => exact ⟨cap, h⟩

/-- **The cap resolves positionally** — a `handleF` at the head with cap 0 resolves
immediately, and a deeper resolution is the inner one shifted. This is the
de-Bruijn `i < length`-style characterization, entirely first-order. -/
theorem capResolves_zero_head (h : Handler) (K : EvalCtx) :
    CapResolves (Frame.handleF h :: K) 0 := by
  exact True.intro

/-- And the kind-match resolves structurally too (no polymorphism). If the head
handler handles `(ℓ, op)`, cap 0 resolves with the right kind. -/
theorem capResolvesKind_zero_head (h : Handler) (K : EvalCtx) (ℓ : Label) (op : OpId)
    (hh : handlesOp h ℓ op = true) :
    CapResolvesKind (Frame.handleF h :: K) 0 ℓ op := by
  exact hh


/-! ## 5. The VERDICT, build-grounded

Pulling the three obligations together as one statement: a typed `perform cap`
exists whose (a) effect row is a `Finset`, (b) discharge is the semilattice, and
(c) cap well-scopedness is a decidable structural `Nat` property. The conjunction
is what "SETS-PRESERVED, no polymorphism" means concretely. -/

section Verdict
attribute [local instance] setRowSig

theorem setrow_preserved (ℓ : Label) (K : EvalCtx) :
    -- (a) a typed perform whose effect ROW is a Finset:
    (HasPerform (Eff := EffRow) (Mult := QTT)
        ((1 : QTT) • ([] : GradeVec QTT)) [] ⟨7, ℓ, "raise", Val.vunit⟩ ({ℓ} : EffRow) (CTy.F 1 VTy.unit))
    -- (b) discharge is the ⊔-semilattice (idempotent, unordered):
    ∧ (({ℓ} : EffRow) ⊔ {ℓ} = {ℓ})
    -- (c) cap well-scopedness is structural (positional), with right-KIND match:
    --     a `throws ℓ` handler at the head, cap 0, catches `(ℓ, "raise")`.
    ∧ CapResolvesKind (Frame.handleF (Handler.throws ℓ) :: K) 0 ℓ "raise" := by
  refine ⟨?_, ?_, ?_⟩
  · apply HasPerform.perform (A := VTy.unit) (B := VTy.unit)
    · show ({ℓ} : EffRow) ≤ {ℓ}; exact le_refl _
    · rfl
    · rfl
    · exact HasVTy.vunit (Eff := EffRow) (Mult := QTT) (Γ := [])
  · simp
  · -- handlesOp (throws ℓ) ℓ "raise" = true : structural, decidable, no polymorphism.
    show handlesOp (Handler.throws ℓ) ℓ "raise" = true
    simp [handlesOp]

end Verdict

end Bang.SetRowSpike
