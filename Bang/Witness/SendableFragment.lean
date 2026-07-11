module

public import Bang.Core.Semantics
public import Bang.Core.Freshness

/-!
  Bang/Witness/SendableFragment.lean — the ACTOR-SEND (`!`) sendable fragment (G7, design-ahead).
  ─────────────────────────────────────────────────────────────────────────────────
  Actors are POST-V1; this feeds the concurrency-model ADR (see `docs/notes/actor-sendable-design.md`).
  No surface implementation — this is the KERNEL-side theorem the design rests on.

  THE FRAGMENT: `Sendable v` = a first-order, deep-immutable value — vunit/vint and the value
  formers `inl/inr/pair/fold` closed over sendables, EXCLUDING `vthunk` (a closure: code + captured
  env, which the canonical ABI cannot express) and `vcap` (a handler identity: meaningless across a
  component boundary, and a cap crossing actors is a cap ESCAPING its handler — ADR-0063). `vvar`
  cannot occur in a *closed* value; we exclude it here so `Sendable ⇒ Val.Closed` holds on the nose.

  THE THEOREM (`copy ≡ share`, syntactic core): a `Sendable` value is a FIXED POINT of every
  substitution and shift (`sendable_substFrom_eq` / `sendable_shiftFrom_eq`), hence `Val.Closed`
  (`Sendable.closed`). Because a sendable value contains no `vthunk` and no `vcap`, NO `Source.step`
  arm can force code through it or dispatch an effect through it — so whether the machine holds a
  single SHARED reference or a fresh COPY is invisible to `Source.eval`. The full CONTEXTUAL
  form (observational equivalence of copy vs share) is `lr` territory and rides the PARKED binary LR;
  what is PROVEN here is the syntactic backbone that contextual result would consume:
    • closure under the value formers + inversion (the fragment is well-formed as an inductive)
    • cap-freeness  (`sendable_capsV_nil`)  ⇒ a sendable value can never ESCAPE (ADR-0063 tie-in)
    • shift/subst inertness (`sendable_shiftFrom_eq` / `sendable_substFrom_eq`) ⇒ closed + inert
    • the copy≡share demo (`copy_eq_share_demo`): substituting a sendable into a body vs binding it
      through a `letC` reach the SAME `Source.eval` outcome.
  All axiom-clean (`#print axioms` at the foot). CarrierFork-style small leaf file.
-/

@[expose] public section

namespace Bang.SendableFragment
open Bang (Val Comp)

/-! ## §1 — the fragment: `Sendable : Val → Prop` (structural, first-order, deep-immutable). -/

/-- `Sendable v` — the actor-send payload fragment (G7). First-order data closed over sendables;
NO `vthunk` (closure), NO `vcap` (handler identity), NO `vvar` (so a sendable is CLOSED). The
type-level mirror (which surface `Ty` are sendable: `unit`/`int` + `sum`/`prod`/`mu` over
sendables, NOT `U`/`arr`/`cap`) is a plain predicate on `Ty`, not a row/grade citizen — see the
design note; sendability is a *value-shape* property, exactly the "closed value of ground type"
the CLI's `runYieldsInt` convention already uses, generalized from `int` to sums/products/μ. -/
inductive Sendable : Val → Prop where
  | vunit : Sendable .vunit
  | vint  : ∀ n, Sendable (.vint n)
  | inl   : ∀ {v}, Sendable v → Sendable (.inl v)
  | inr   : ∀ {v}, Sendable v → Sendable (.inr v)
  | pair  : ∀ {a b}, Sendable a → Sendable b → Sendable (.pair a b)
  | fold  : ∀ {v}, Sendable v → Sendable (.fold v)

/-! ## §2 — closure + inversion (the fragment is a well-formed inductive over the value formers). -/

theorem Sendable.inl_inv {v : Val} (h : Sendable (.inl v)) : Sendable v := by cases h; assumption
theorem Sendable.inr_inv {v : Val} (h : Sendable (.inr v)) : Sendable v := by cases h; assumption
theorem Sendable.fold_inv {v : Val} (h : Sendable (.fold v)) : Sendable v := by cases h; assumption
theorem Sendable.pair_inv {a b : Val} (h : Sendable (.pair a b)) : Sendable a ∧ Sendable b := by
  cases h with | pair ha hb => exact ⟨ha, hb⟩

/-- The excluded formers are NOT sendable — the two heap-escapers the ABI cannot copy. -/
theorem Sendable.not_vthunk {M : Comp} : ¬ Sendable (.vthunk M) := fun h => by cases h
theorem Sendable.not_vcap {n ℓ : Nat} : ¬ Sendable (.vcap n ℓ) := fun h => by cases h
theorem Sendable.not_vvar {i : Nat} : ¬ Sendable (.vvar i) := fun h => by cases h

/-! ## §3 — cap-freeness: a sendable value carries NO capability ⇒ it can never ESCAPE (ADR-0063). -/

/-- A `Sendable` value contains no `vcap` (nor a `vthunk` that could bury one): `capsV v = []`.
This is the escape tie-in — the escape machinery (`capsC`/`VcapFree`, ADR-0063) fails loud on a cap
dispatched past its handler; a sendable payload has NO cap to escape, so `!` over the fragment is
escape-free BY CONSTRUCTION. -/
theorem sendable_capsV_nil {v : Val} (h : Sendable v) : Bang.Model.capsV v = [] := by
  induction h with
  | vunit | vint => simp [Bang.Model.capsV]
  | inl _ ih => simpa [Bang.Model.capsV] using ih
  | inr _ ih => simpa [Bang.Model.capsV] using ih
  | fold _ ih => simpa [Bang.Model.capsV] using ih
  | pair _ _ iha ihb => simp [Bang.Model.capsV, iha, ihb]

/-! ## §4 — the syntactic `copy ≡ share` core: a sendable value is a FIXED POINT of shift/subst. -/

/-- A sendable value is fixed by `shiftFrom` at every cutoff — it has no free `vvar` to lift. -/
theorem sendable_shiftFrom_eq {v : Val} (h : Sendable v) : ∀ c, Val.shiftFrom c v = v := by
  induction h with
  | vunit | vint => intro c; rfl
  | inl _ ih => intro c; simp [Val.shiftFrom, ih c]
  | inr _ ih => intro c; simp [Val.shiftFrom, ih c]
  | fold _ ih => intro c; simp [Val.shiftFrom, ih c]
  | pair _ _ iha ihb => intro c; simp [Val.shiftFrom, iha c, ihb c]

/-- Hence a sendable value is `Val.Closed` (fixed by `shiftFrom` at every cutoff — the repo's
closed-value predicate, `Subst.lean §1.3c`). The SSoT link: sendability ⊆ closedness. -/
theorem Sendable.closed {v : Val} (h : Sendable v) : Val.Closed v :=
  fun k => sendable_shiftFrom_eq h k

/-- THE FIXED-POINT LEMMA (`copy ≡ share`, syntactic form): a sendable value is INERT under
substitution — `substFrom k w v = v` for any level `k` and filler `w`. There is no free variable
to replace, so substituting a COPY of a sendable in for a bound occurrence is the same term as
leaving the SHARED reference; the machine cannot tell them apart. This is the kernel fact the
in-process-shares / component-copies backends both preserve. -/
theorem sendable_substFrom_eq {v : Val} (h : Sendable v) :
    ∀ (k : Nat) (w : Val), Val.substFrom k w v = v := by
  induction h with
  | vunit | vint => intro k w; rfl
  | inl _ ih => intro k w; simp [Val.substFrom, ih k w]
  | inr _ ih => intro k w; simp [Val.substFrom, ih k w]
  | fold _ ih => intro k w; simp [Val.substFrom, ih k w]
  | pair _ _ iha ihb => intro k w; simp [Val.substFrom, iha k w, ihb k w]

/-! ## §5 — the copy≡share demo: substitute a sendable in vs bind it shared, SAME `Source.eval`. -/

/-- A representative sendable value: `fold (pair (inl unit) (int 7))` — a μ/product/sum/int nest,
no thunk, no cap. (Shape of `μX. (1+1) × Int` inhabitant; the fragment the design targets.) -/
def sVal : Val := .fold (.pair (.inl .vunit) (.vint 7))

theorem sVal_sendable : Sendable sVal := by
  apply Sendable.fold; apply Sendable.pair
  · exact Sendable.inl Sendable.vunit
  · exact Sendable.vint 7

/-- (demo) The two ways a `!`-backend can deliver a sendable payload agree:
    SHARE  — the payload flows through the machine as one reference: `letC (ret sVal) (unfold (vvar 0))`
    COPY   — the payload is substituted in eagerly: `unfold sVal`
both reach the SAME `Source.eval` outcome. The equality holds because `sVal` is subst-inert
(`sendable_substFrom_eq`): the `letC`/`ret` REDUCE step substitutes `sVal` unchanged. -/
def shareProg : Comp := .letC (.ret sVal) (.unfold (.vvar 0))
def copyProg  : Comp := .unfold sVal

theorem copy_eq_share_demo : Source.eval 20 shareProg = Source.eval 20 copyProg := by rfl

/-- Both sides deliver the underlying `pair` (unfold erases the μ) — a concrete positive value. -/
theorem copy_share_result :
    Source.eval 20 shareProg = Result.done (.pair (.inl .vunit) (.vint 7)) := by rfl

/-! ## §6 — axiom hygiene: every headline is axiom-clean (⊆ {propext, Classical.choice, Quot.sound}). -/

#print axioms sendable_capsV_nil
#print axioms sendable_shiftFrom_eq
#print axioms sendable_substFrom_eq
#print axioms Sendable.closed
#print axioms copy_eq_share_demo
#print axioms copy_share_result

end Bang.SendableFragment

end -- @[expose] public section
