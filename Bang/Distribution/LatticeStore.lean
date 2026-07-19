module

public import Mathlib.Order.Lattice
public import Mathlib.Order.BoundedOrder.Basic

/-!
# A join-only lattice store

This is the concrete, deliberately small distribution core that the replicated-KV examples were
missing. A `LatticeStore α` owns one lattice value. Its only update is `JoinUpdate.join x`, interpreted
as `current ⊔ x`; replica repair is the same join. There is no conditional overwrite or
compare-and-swap constructor.

The theorems below establish only the algebra exercised by this fragment: updates are inflationary,
two updates commute, repeating one update is idempotent, and one symmetric anti-entropy exchange
leaves two replicas equal. They do **not** prove trace-level permutation invariance, the general CALM
conjecture in `Bang.Distribution`, network liveness, or convergence without an eventual exchange.
-/

namespace Bang.Distribution

@[expose] public section

/-- The complete update language of the first lattice-store fragment. Every representable update
joins one payload into the current value. A CAS-like conditional replacement is intentionally absent. -/
inductive JoinUpdate (α : Type) where
  | join : α → JoinUpdate α
  deriving Repr, DecidableEq

/-- A single state-based replica. The update discipline lives in `JoinUpdate`; `current` is exposed
for observation and for the small convergence statements below. -/
@[ext] structure LatticeStore (α : Type) where
  current : α
  deriving Repr, DecidableEq

namespace LatticeStore

variable {α : Type}

/-- Start at the lattice bottom. -/
def empty [SemilatticeSup α] [OrderBot α] : LatticeStore α := ⟨⊥⟩

/-- Interpret the fragment's only update form by joining its payload into the current state. -/
def apply [SemilatticeSup α] (store : LatticeStore α) : JoinUpdate α → LatticeStore α
  | .join value => ⟨store.current ⊔ value⟩

/-- Convenience spelling for one join update. -/
def join [SemilatticeSup α] (store : LatticeStore α) (value : α) : LatticeStore α :=
  store.apply (.join value)

/-- Apply a delivery trace. The pairwise commutation and one-update idempotence laws proved below
are the deliberately smaller algebraic floor; no trace-level invariance theorem is claimed. -/
def applyAll [SemilatticeSup α] (store : LatticeStore α)
    (updates : List (JoinUpdate α)) : LatticeStore α :=
  updates.foldl apply store

/-- State-based anti-entropy is the same join as a local update. -/
def merge [SemilatticeSup α] (left right : LatticeStore α) : LatticeStore α :=
  left.join right.current

@[simp] theorem current_empty [SemilatticeSup α] [OrderBot α] :
    (empty : LatticeStore α).current = ⊥ := rfl

@[simp] theorem current_apply [SemilatticeSup α] (store : LatticeStore α) (value : α) :
    (store.apply (.join value)).current = store.current ⊔ value := rfl

@[simp] theorem current_join [SemilatticeSup α] (store : LatticeStore α) (value : α) :
    (store.join value).current = store.current ⊔ value := rfl

@[simp] theorem current_merge [SemilatticeSup α] (left right : LatticeStore α) :
    (left.merge right).current = left.current ⊔ right.current := rfl

/-- Join-only updates never retract an existing fact. -/
theorem le_join [SemilatticeSup α] (store : LatticeStore α) (value : α) :
    store.current ≤ (store.join value).current :=
  le_sup_left

/-- Delivery order is irrelevant for two join updates. -/
theorem join_commutes [SemilatticeSup α] (store : LatticeStore α) (x y : α) :
    (store.join x).join y = (store.join y).join x := by
  ext
  simp only [current_join]
  ac_rfl

/-- Redelivering the same join update has no effect. -/
theorem join_idempotent [SemilatticeSup α] (store : LatticeStore α) (x : α) :
    (store.join x).join x = store.join x := by
  ext
  simp

/-- One anti-entropy exchange computes the same joined state at both replicas.

This is the convergence law actually established by this core: it assumes both replicas
participate in this exchange. It is not a liveness theorem about a lossy network. -/
theorem pair_converges_after_exchange [SemilatticeSup α] (left right : LatticeStore α) :
    left.merge right = right.merge left := by
  ext
  simp [sup_comm]

/-- Exhausting the update type proves the fragment boundary: every accepted update is a join.
CAS is not assigned a hidden approximation; adding it would require a new update constructor and
new semantics rather than silently entering this theorem's scope. -/
theorem updates_are_join_only (update : JoinUpdate α) : ∃ value, update = .join value := by
  cases update with
  | join value => exact ⟨value, rfl⟩

end LatticeStore

end

end Bang.Distribution
