/-
  Bang/LWRegress.lean — ADR-0045 R1 permanent regression suite for the KERNEL `LWT`.
  ─────────────────────────────────────────────────────────────────────────────────
  Carries the cap-assignment spike's decisive splits forward onto the PROMOTED kernel `LWT`
  (Operational.lean), as permanent build-gated checks:
    1. case A (capMigrate) — WELL-TYPED under `LWT` + `done 5`/`done 9` (compiled `#guard`).
    2. case B (escapeM/progB) — ILL-TYPED under `LWT` (the capability-escape) + `stuck`.
    3. cap>0 (resume-into-outer) — WELL-TYPED (the ADR-0045 KEEP case — a perform reaching PAST an
       inner handler to an enclosing one is legal; only ESCAPE out of a handler is illegal).

  GATING: every behavioural claim is a COMPILED `#guard` (a failing build = a false `#guard`); never
  `lake env lean` (`Source.eval` does not reduce interpreted — memory `lean-eval-reliable-only-compiled`).
  Imports ONLY `Bang.Operational` + `Bang.Mult`.
-/
import Bang.Operational
import Bang.Mult

namespace Bang.LWRegress

open Bang
open Bang.EffectRow (Label EffRow)

/-- The concrete `EffSig`: label `1` is a `state`-label (ops `get`/`put`, `unit → unit`). -/
@[reducible] def sigU : EffSig EffRow QTT where
  labelEff ℓ := {ℓ}
  opArg ℓ op := if ℓ = 1 ∧ (op = "get" ∨ op = "put") then some VTy.unit else none
  opRes ℓ op := if ℓ = 1 ∧ (op = "get" ∨ op = "put") then some VTy.unit else none
  labelEff_ne_bot ℓ := Finset.singleton_ne_empty ℓ
  labelEff_sep ℓ ℓ' φ h hne := by
    have hmem : ℓ ∈ ({ℓ'} : EffRow) ∪ φ := h (Finset.mem_singleton_self ℓ)
    apply Finset.singleton_subset_iff.mpr
    rcases Finset.mem_union.1 hmem with hℓ | hφ
    · exact absurd (Finset.mem_singleton.1 hℓ) hne
    · exact hφ

attribute [local instance] sigU

/-- The author-site fact every case-A perform needs: `state 1`'s nearest-handler resolves `(1, get)`. -/
theorem state1_resolves_get (s : Val) :
    CapResolvesKind [Frame.handleF (.state 1 s)] 0 1 "get" := rfl

/-! ### 1. case A — WELL-TYPED under the kernel `LWT` + terminates under the cap-shift. -/

private def capMigrate1 : Comp :=
  .handle (.state 1 (.vint 5))
    (.letC (.ret (.vthunk (.perform 0 1 "get" .vunit)))
      (.handle (.throws 2) (.force (.vvar 0))))
private def capMigrate1_done5 : Bool :=
  match Source.eval 200 capMigrate1 with | .done (.vint n) => n == 5 | _ => false
#guard capMigrate1_done5

private def capMigrate2 : Comp :=
  .handle (.state 1 (.vint 9))
    (.letC (.ret (.vthunk (.perform 0 1 "get" .vunit)))
      (.handle (.throws 2) (.handle (.throws 3) (.force (.vvar 0)))))
private def capMigrate2_done9 : Bool :=
  match Source.eval 300 capMigrate2 with | .done (.vint n) => n == 9 | _ => false
#guard capMigrate2_done9

/-- case A is LEXICALLY WELL-TYPED under the kernel `LWT` (the `ret {get}` is a `letC`'s M, return-ctx
= S = [state], so the perform resolves). -/
theorem capMigrate1_LWT : LWT [] [] capMigrate1 := by
  simp only [capMigrate1, LWT, LWVal, LWHandler]
  exact ⟨trivial, ⟨state1_resolves_get _, trivial⟩, trivial, trivial⟩

theorem capMigrate2_LWT : LWT [] [] capMigrate2 := by
  simp only [capMigrate2, LWT, LWVal, LWHandler]
  exact ⟨trivial, ⟨state1_resolves_get _, trivial⟩, trivial, trivial, trivial⟩

/-! ### 2. case B — ILL-TYPED under the kernel `LWT` (the capability escape) + stuck. -/

private def escapeM : Comp :=
  .handle (.state 1 .vunit) (.ret (.vthunk (.perform 0 1 "get" .vunit)))
private def progB : Comp :=
  .letC escapeM (.handle (.state 1 .vunit) (.force (.vvar 0)))
private def progB_stuck : Bool := match Source.eval 300 progB with | .stuck => true | _ => false
#guard progB_stuck

/-- case B's escape is ILL-TYPED under the kernel `LWT`: the handle body `ret {get}` is checked with
return-ctx = OLD S = [], so `perform 0` must resolve against [] — `CapResolvesKind [] 0 1 "get" = False`.
The capability cannot escape its handler. -/
theorem escapeM_ill_typed : ¬ LWT [] [] escapeM := by
  simp only [escapeM, LWT, LWVal, LWHandler, CapResolvesKind]; tauto

theorem progB_ill_typed : ¬ LWT [] [] progB := by
  intro h; simp only [progB, LWT] at h; exact escapeM_ill_typed h.1

/-! ### 3. cap>0 — the ADR-0045 KEEP case: resume-into-an-outer-handler is WELL-TYPED.

A `perform 1` reaching PAST an inner `throws` to the enclosing `state` is LEGAL (the cap counts the
skipped handler). This is what distinguishes legal deep-dispatch (cap>0) from illegal escape (case B). -/
theorem capResume_outer_LWT :
    LWT [] [] (.handle (.state 1 .vunit) (.handle (.throws 2) (.perform 1 1 "get" .vunit))) := by
  simp only [LWT, LWVal, LWHandler, CapResolvesKind, handlesOp]; tauto

/-! ### 4. Discrimination — the kernel `LWT` is not vacuous either way. -/

/-- An in-scope direct perform is ACCEPTED (not vacuously rejecting). -/
theorem inscope_perform_LWT :
    LWT [] [] (.handle (.state 1 .vunit) (.perform 0 1 "get" .vunit)) := by
  simp only [LWT, LWVal, LWHandler, CapResolvesKind, handlesOp]; tauto

/-- A top-level handler-less perform is REJECTED (not vacuously accepting). -/
theorem toplevel_perform_ill_typed : ¬ LWT [] [] (.perform 0 1 "get" .vunit) := by
  simp only [LWT, CapResolvesKind]; tauto

end Bang.LWRegress
