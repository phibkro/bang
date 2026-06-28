/-
U5b DETERMINISM-SHORTCUT SPIKE (inc-6) — refute-first: can `evalD_complete_gen`'s ~70-lemma
Sim block be AVOIDED for `compile_forward_sim`?

The shortcut (team-lead rec #1): `Source.eval c = done v ⟹ ∃n, evalD n c = some(ret v)`
(completeness) might follow from
  (A) evalD-TOTALITY on terminating inputs: Source.eval terminates ⟹ evalD terminates, and
  (B) determinism: evalD's value agrees with Source.eval (soundness, U3) + Source.eval determinism.
If (A) is a SMALL induction, U5b collapses (delete the 1500-line Sim block). If (A) needs the
same step-correspondence as the Sim block, the shortcut DOESN'T help.

This spike: (B) FULLY PROVEN (free, from Config.run_done_add); the shortcut SKELETON build-confirmed
(totality+determinism+soundness+compile_correct ⟹ Source.eval ⟹ exec); (A) ATTEMPTED to verdict.
-/
import Bang.CalcVM

namespace Bang.U5DetShortcut
open Bang
open Bang.CalcVM

/-! ### (B) Source.eval DETERMINISM — fully proven, free (from `Config.run_done_add`). -/
theorem source_determinism {c : Comp} {a b : Val} {F1 F2 : Nat} :
    Source.eval F1 c = .done a → Source.eval F2 c = .done b → a = b := by
  intro h1 h2
  unfold Source.eval at h1 h2
  have e1 : Config.run (F1 + F2) (0, [], c) = .done a := Config.run_done_add F2 F1 _ _ h1
  have e2 : Config.run (F2 + F1) (0, [], c) = .done b := Config.run_done_add F1 F2 _ _ h2
  rw [Nat.add_comm] at e2
  rw [e1] at e2
  exact (Result.done.injEq _ _).mp e2

/-! ### (A) evalD-TOTALITY — THE OPEN QUESTION (sorry'd; attempted in §commentary below). -/
theorem evalD_total : ∀ (F : Nat) (c : Comp) (v : Val),
    Source.eval F c = .done v →
    ∃ n v' g' σ' τ', evalD n 0 [] [] c = some (.term (.ret v'), g', σ', τ') := by
  sorry

/-! ### THE SHORTCUT SKELETON — build-confirms the LOGIC is valid IF (A) holds.
Combines (A) totality + (B) determinism + U3 soundness (`evalD_agrees_source`) +
U2 `compile_correct`. If this elaborates (modulo the `evalD_total` sorry), the shortcut
is SOUND and `evalD_complete_gen` + the whole Sim block is UNNECESSARY — provided (A). -/
theorem source_to_exec_shortcut (c : Comp) (v : Val) (F : Nat)
    (hvf : Bang.Model.VcapFree c)
    (h : Source.eval F c = .done v) :
    ∃ G, exec G 0 (compile c []) [] [] = some [.ret v] := by
  obtain ⟨n, v', g', σ', τ', hev⟩ := evalD_total F c v h
  -- U3 soundness: evalD = ret v' ⟹ Source.eval = done v'
  obtain ⟨F', hsrc'⟩ := evalD_agrees_source n c v' g' σ' τ' hvf hev
  -- (B) determinism: v' = v
  have hvv : v' = v := source_determinism hsrc' h
  subst hvv
  -- U2 compile_correct: evalD ⟹ exec
  exact compile_correct n c (.ret v') g' σ' τ' hev

end Bang.U5DetShortcut
