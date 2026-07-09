import Bang.Backend.Wasm
import Bang.Core.Freshness

/-! # Witness: `Source.eval … = done` does NOT imply `VcapFree c` (capsC c = []).

PRECISE CLAIM (corrected — does NOT overclaim "unsound-as-stated"): a program with a BURIED
(never-forced) capability literal evaluates to `done`, yet its `capsC` is non-empty AND
`FreshCfg (0,[],c)` is FALSE. So the cap-free premise is **premise-necessary for the evalD-bridge
proof ARCHITECTURE / BRIDGE ROUTE** (its only known route cannot reach such c — FreshCfg fails). It
does NOT show `compile_forward_sim` is FALSE on cWitness: the thunk is never forced, and check (4)
below CONFIRMS the WASM side ALSO completes cWitness — so the HEADLINE is TRUE-but-UNPROVABLE-
WITHOUT-THE-PREMISE on this class (headline truth on the vcap class: plausibly-true, here confirmed
for this witness). Do-not-weaken regression witness. -/

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

/-- (3) The PROOF-ARCHITECTURE bound: `FreshCfg(0,[],cWitness)` is FALSE (the buried cap 99 ≥ g=0),
so the evalD-bridge completeness proof's precondition cannot be met for this c — the premise is
PROOF-ARCHITECTURE-necessary (NOT a proof that the headline is false). -/
example : ¬ Bang.Model.FreshCfg (0, ([] : Bang.EvalCtx), cWitness) := by
  simp only [Bang.Model.FreshCfg, cWitness, Bang.Model.capsC, Bang.Model.capsV]
  rintro ⟨_, hcaps, _, _⟩
  have := hcaps (99, 0) (by simp)
  simp at this

/-- (4) THE HEADLINE-TRUTH CHECK (manager's request): does the WASM side ALSO complete cWitness?
YES — `Wasmfx.run 100 (compileC cWitness) = done unit` (compiled rfl). So `compile_forward_sim`
is TRUE on cWitness (both sides reach done unit) — it is TRUE-BUT-UNPROVABLE-WITHOUT-THE-PREMISE,
NOT false. This is the evidence for the "premise an unprovable statement" reframing (vs "repair a
false one"): the never-forced thunk is dead code both sides discard. -/
example : Wasmfx.run 100 (compileC cWitness) = Result.done .unit := by rfl

end Bang.VcapFreeRefute
