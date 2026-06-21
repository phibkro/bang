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

/-- The concrete effect-row carrier: a `Finset Label`. Mathlib gives this
type `Lattice`, `OrderBot`, and `DistribLattice` instances natively (join
= union, bottom = empty), satisfying the `[Lattice Eff] [OrderBot Eff]`
constraints used in `Bang/Core.lean`'s variable block.

The spec stays parametric in any such `Eff`; this is THE bang-lang
default per ADR-0001.

The lattice (not semiring) choice is the SOTA abstraction, not an idiosyncrasy:
yoshioka-icfp24-abstracting-effect-systems proves `(E, ⊔)` a join-semilattice
is *exactly* the structure under which type-and-effect safety holds; and
balik-esop26-deciding-not-to-decide independently adopts the same set/join
semantics (Rocq-mechanized). The Q1 semiring→lattice switch moved toward
consensus. -/
abbrev EffRow := Finset Label

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
-- structurally recursive on `fuel` (each call uses `f < f+1`); no `termination_by`
-- needed, and the equation lemmas unfold cleanly under `simp` for `unify_sound`.

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

/-! Two `Finset` facts the soundness cases reduce to. -/

/-- For a subset, the open side's fixed labels plus the missing ones recover the
closed side: `a ⊆ b → a ∪ (b \ a) = b`. (open/closed case) -/
private theorem union_sdiff_subset {a b : RowC} (hab : a ⊆ b) : a ∪ (b \ a) = b := by
  ext x; simp only [Finset.mem_union, Finset.mem_sdiff]
  constructor
  · rintro (hx | ⟨hx, _⟩)
    · exact hab hx
    · exact hx
  · intro hx; by_cases hxa : x ∈ a
    · exact Or.inl hxa
    · exact Or.inr ⟨hx, hxa⟩

/-- **Soundness of the unifier.** If `unify` succeeds with substitution `s`, then
applying `s` to both rows makes their label sets and tails coincide. Requires that
`fresh` is genuinely fresh (not already either row's tail variable) — without it the
open/open case would bind a tail to a cyclic `some fresh`. Principality (MGU) is
deferred to the differential test, as documented. -/
theorem unify_sound (fresh : RVar) (r1 r2 : Row) (s : Subst)
    (hf1 : r1.tail ≠ some fresh) (hf2 : r2.tail ≠ some fresh)
    (h : unify fresh r1 r2 = some s) :
    (applyR (s.length + 2) s r1).labels = (applyR (s.length + 2) s r2).labels ∧
    (applyR (s.length + 2) s r1).tail   = (applyR (s.length + 2) s r2).tail := by
  rcases h1 : r1.tail with _ | v1 <;> rcases h2 : r2.tail with _ | v2 <;>
    simp only [unify, h1, h2] at h
  -- closed / closed
  · split at h
    · rename_i heq; obtain rfl := Option.some.inj h
      refine ⟨?_, ?_⟩ <;> simp [applyR, h1, h2, heq]
    · exact absurd h (by simp)
  -- closed / open  (r2 open; bind v2 ↦ r1 \ r2)
  · split at h
    · rename_i hsub; obtain rfl := Option.some.inj h
      refine ⟨?_, ?_⟩ <;>
        simp [applyR, lookupVar, h1, h2, List.find?, union_sdiff_subset hsub]
    · exact absurd h (by simp)
  -- open / closed  (r1 open; bind v1 ↦ r2 \ r1)
  · split at h
    · rename_i hsub; obtain rfl := Option.some.inj h
      refine ⟨?_, ?_⟩ <;>
        simp [applyR, lookupVar, h1, h2, List.find?, union_sdiff_subset hsub]
    · exact absurd h (by simp)
  -- open / open
  · split at h
    · -- v1 = v2: substitution is empty, both rows are returned unchanged
      rename_i hv; split at h
      · rename_i heq; obtain rfl := Option.some.inj h
        refine ⟨?_, ?_⟩ <;> simp [applyR, lookupVar, h1, h2, heq, hv]
      · exact absurd h (by simp)
    · -- v1 ≠ v2: each tail absorbs the other's exclusive labels, tail ↦ fresh
      rename_i hv; obtain rfl := Option.some.inj h
      have hv1 : v1 ≠ fresh := fun e => hf1 (by rw [h1, e])
      have hv2 : v2 ≠ fresh := fun e => hf2 (by rw [h2, e])
      refine ⟨?_, ?_⟩ <;>
        simp [applyR, lookupVar, h1, h2, List.find?, hv, hv1, hv2, Finset.union_comm]


end Bang.EffectRow
