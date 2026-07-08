import Bang.Backend.AbstractMachine
import Bang.Core.Freshness

/-! # Refutation witness: `Source.eval … = done` does NOT imply `VcapFree c` (capsC c = []).

If this builds, it machine-proves the frozen `compile_forward_sim`/`evalD_complete_gen` are
unsound-AS-STATED for non-VcapFree c: a program with a BURIED (never-performed) capability literal
still evaluates to `done`, yet its `capsC` is non-empty. So the cap-free precondition is
STATEMENT-necessary, not merely proof-necessary — the hypothesis must be added (option 1/3), or
the statement is wrong. Kept as a do-not-weaken regression witness. -/

namespace Bang.VcapFreeRefute
open Bang (Val Comp)

/-- A closed program that BINDS a thunk carrying a free `vcap 99 0` but NEVER forces it, then
returns `vunit`. The buried cap never dispatches, so the run reaches `done`. -/
def cWitness : Comp :=
  .letC (.ret (.vthunk (.perform (.vcap 99 0) "get" .vunit))) (.ret .vunit)

/-- (1) It EVALUATES to done vunit — a well-defined terminating run. -/
example : Source.eval 20 cWitness = Result.done .vunit := by rfl

/-- (2) Yet it is NOT VcapFree — `capsC cWitness` contains the buried `(99, 0)`. -/
example : ¬ Bang.Model.VcapFree cWitness := by
  simp only [Bang.Model.VcapFree, cWitness, Bang.Model.capsC, Bang.Model.capsV]
  intro h
  simp at h

/-- (3) THE REFUTATION, as a hypothesis (independent of any in-file sorry): if the frozen
`evalD_complete_gen`-shaped implication held UNCONDITIONALLY (for all c, no VcapFree premise), it
would be applied to cWitness — but FreshCfg(0,[],cWitness) is FALSE (the buried cap 99 ≥ g=0), so
the completeness proof's precondition cannot be met. This pins the hypothesis as STATEMENT-necessary. -/
example : ¬ Bang.Model.FreshCfg (0, ([] : Bang.EvalCtx), cWitness) := by
  simp only [Bang.Model.FreshCfg, cWitness, Bang.Model.capsC, Bang.Model.capsV]
  rintro ⟨_, hcaps, _, _⟩
  have := hcaps (99, 0) (by simp)
  simp at this

end Bang.VcapFreeRefute
