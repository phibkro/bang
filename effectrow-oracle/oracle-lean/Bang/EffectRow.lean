import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Lattice

/-!
# bang-lang effect rows, in Lean 4 + Mathlib

Port of `oracle/src/Bang.EffectRow.fst`. The model is identical (idempotent sets
of labels with an optional polymorphic tail), but representing the label set as
`Finset` collapses two things that were real work in F*:

* `canon_unique` (the keystone: extensional equality ⇒ syntactic equality on the
  canonical form) is now **definitional** — `Finset.ext` IS that statement.
* the semilattice laws are **inherited** from Mathlib's `Finset` lattice
  instance (`(· ∪ ·)` is `⊔`, `∅` is `⊥`), not proved by hand.

Honesty note: faithful in shape; not compiled in-sandbox. Spots that may need a
nudge (a lemma rename or a one-line `by ext x; simp` fallback) are marked NUDGE.
`tools/selfcheck.mjs` exercises this exact algorithm a third time and stays
green, so the design is de-risked independent of the proofs.
-/

namespace Bang.EffectRow

abbrev Label := Nat
abbrev RVar  := Nat

/-- A canonical row's label set. `Finset` is canonical by construction: there is
no sorted/duplicate-free invariant to carry, and equality is extensional. -/
abbrev RowC := Finset Label

structure Row where
  labels : RowC
  tail   : Option RVar
deriving DecidableEq
-- NOTE: `Repr` was dropped here: `Finset.instRepr` is an `unsafe` declaration, so
-- `deriving Repr` on a structure containing a `Finset` fails the kernel check
-- (`uses unsafe declaration 'Finset.instRepr'`). Repr is unused — Main.lean
-- serialises via the custom `rowToJson`. This was a real NUDGE spot; it is fixed.

abbrev Subst := List (RVar × Row)

/-! ## The algebra is Mathlib's Finset join-semilattice -/

/-- Concretely: the row-union algebra already has the lattice + bottom instances.
This is the "instantiate the Mathlib semilattice" win, made explicit. -/
example : Lattice RowC  := inferInstance
example : OrderBot RowC := inferInstance   -- ⊥ = ∅

/-- The four laws the F* version proved by hand, here inherited as Mathlib
lemmas. NUDGE: if any name has drifted, each is also closed by
`by ext x; simp [or_comm]` / `[or_assoc]` etc. -/
theorem union_comm  (a b : RowC)   : a ∪ b = b ∪ a            := Finset.union_comm a b
theorem union_assoc (a b c : RowC) : a ∪ b ∪ c = a ∪ (b ∪ c)  := Finset.union_assoc a b c
theorem union_self  (a : RowC)     : a ∪ a = a                := Finset.union_self a
theorem union_empty (a : RowC)     : a ∪ ∅ = a                := Finset.union_empty a
theorem empty_union (a : RowC)     : ∅ ∪ a = a                := Finset.empty_union a

/-- The F* keystone `canon_unique`, now a one-liner: extensional equality is
equality for `Finset`. -/
theorem canon_unique (a b : RowC) (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b :=
  Finset.ext h

/-! ## The unifier (Rémy/Pottier specialised to idempotent set-rows) -/

def lookupVar (r : RVar) (s : Subst) : Option Row :=
  (s.find? (fun b => b.1 = r)).map (·.2)

/-- Apply a substitution to a row. Fuel guarantees termination; well-formed
oracle output is acyclic and resolves within `s.length + 1`. -/
def applyR (fuel : Nat) (s : Subst) (r : Row) : Row :=
  match r.tail with
  | none   => r
  | some v =>
    match fuel with
    | 0          => r
    | Nat.succ f =>
      match lookupVar v s with
      | none    => r
      | some r' =>
        let rr := applyR f s r'
        { labels := r.labels ∪ rr.labels, tail := rr.tail }
termination_by fuel

/--
closed/closed : succeed iff label sets are equal
open/closed   : closed side can't grow, so the open side's fixed labels must be a
                subset; bind the open tail to the missing labels, closed
open/open     : one fresh tail var; each tail absorbs the other side's exclusive
                labels plus the shared fresh tail
-/
def unify (fresh : RVar) (r1 r2 : Row) : Option Subst :=
  match r1.tail, r2.tail with
  | none, none =>
      if r1.labels = r2.labels then some [] else none
  | some v1, none =>
      if r1.labels ⊆ r2.labels
      then some [(v1, { labels := r2.labels \ r1.labels, tail := none })]
      else none
  | none, some v2 =>
      if r2.labels ⊆ r1.labels
      then some [(v2, { labels := r1.labels \ r2.labels, tail := none })]
      else none
  | some v1, some v2 =>
      if v1 = v2 then
        (if r1.labels = r2.labels then some [] else none)
      else
        some [ (v1, { labels := r2.labels \ r1.labels, tail := some fresh }),
               (v2, { labels := r1.labels \ r2.labels, tail := some fresh }) ]

/-! ## Soundness

Row equality is `Finset` equality (decidable, extensional), so the statement is
cleaner than the F* `row_eq`. We prove SOUNDNESS only (if `unify` says yes, the
substitution makes the rows denote the same set and agree on tail). Principality
is deferred to the differential test, exactly as in the F* version. -/

/-- NUDGE: prove by `rcases r1.tail`/`r2.tail` mirroring `unify`, then in each
branch `simp only [unify, ...] at h`, substitute, and `simp [applyR, lookupVar]`.
The label-set goals reduce to `Finset` `sdiff`/`union`/`subset` facts closable by
`simp` + `Finset.union_sdiff_of_subset` (open/closed) and
`Finset.union_comm`/`sdiff` lemmas (open/open). Replace `sorry` once it checks. -/
theorem unify_sound (fresh : RVar) (r1 r2 : Row) (s : Subst)
    (h : unify fresh r1 r2 = some s) :
    let f := s.length + 2
    (applyR f s r1).labels = (applyR f s r2).labels ∧
    (applyR f s r1).tail   = (applyR f s r2).tail := by
  sorry

end Bang.EffectRow
