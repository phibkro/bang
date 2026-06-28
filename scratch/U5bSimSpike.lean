import Bang.CalcVM

/-! # U5b refute-watch — the completeness `Sim`-congruence architecture does NOT survive route-B

## VERDICT: WALL FOUND — re-scope, NOT a mechanical mirror.

The route-A reverse completeness bridge (`Bang/Compile.lean` 1595-3170) lifts a focus
simulation through a frame stack `K` via `evalD_plug_sim`, whose `handleF` case uses
  `Sim.handle : Sim cx cy → Sim (handle hh cx) (handle hh cy)`.

In **route-A**, `evalD (handle hh cy)` ran `cy` DIRECTLY at pushed stores, so `h : Sim cx cy`
applied as-is. In **route-B** (ADR-0052), `evalD (handle hh cy)` MINTS `id := g`, SUBSTITUTES
`vcap g ℓ` for the handle-bound var into the body, and runs `subst (vcap g ℓ) cy` at `g+1`.
So `Sim.handle` would require
  `Sim cx cy → Sim (subst (vcap g ℓ) cx) (subst (vcap g ℓ) cy)`,
i.e. SUBSTITUTION-CLOSURE of `Sim`.  `Sim` is a BLACK-BOX behavioral relation between two
SPECIFIC terms; it does NOT transport across `subst`.  Build-confirmed below: after unfolding
the route-B handle, the body hypothesis is about `Comp.subst (Val.vcap g ℓ) cy`, but `h`
only transfers `cy` — they do not unify (the `rw [ha]` in the route-A proof fails to find the
pattern; see the U5b report).

The forward `sim` (`Bang/CalcVM.lean:1559`) avoided this by being a FUEL induction — its IH
applies to substituted bodies at lower fuel directly. The completeness congruence architecture
has no such escape.

## WHY the gate is NOT blocked
The gated Audit headline `Bang.source_eval_to_exec` routes ONLY through the PURE bridge
`evalD_complete_gen_pure` (PureCtx forbids `handleF`). The wall lives entirely in the
`.handle` congruences (`Sim.handle`, `SimOn.handle`, `SimShift(T).handle`, the `sim_*_handle`
dispatch lemmas, `evalD_plug_dispatch`, full `evalD_complete_gen`) — the HANDLER fragment that
feeds the non-pure `compile_forward_sim` branch. A PureCtx-restricted `evalD_plug_sim_pure`
(handleF VACUOUS) decouples the gate from the wall. See the U5b report for the corrected map.

## DO-NOT-RETRY
Re-keying `Sim.handle` (and the other `.handle` congruences) by g-threading ALONE is
build-disproven. The handler fragment needs the fuel-induction re-architecture (Route 1,
mirror the proven forward `sim`) OR a substitution-stable `Sim` (Route 2). Do NOT re-attempt
the mechanical g-thread on the `.handle` congruences. -/

open Bang CalcVM

namespace U5bSpike

/-- Route-B `Sim`: threads the global counter `g`; outcome is `(Outcome × Nat × SStore × THeap)`. -/
def Sim (cx cy : Comp) : Prop :=
  ∀ g σ τ b r, CalcVM.evalD b g σ τ cy = some r → ∃ a, CalcVM.evalD a g σ τ cx = some r

-- NOTE: the reduce-sims and the `letC`/`app` congruences re-key MECHANICALLY (they run the
-- focus at the SAME g/σ/τ — no cap mint), so they are NOT the wall. Only the `.handle`
-- congruence below is. (The full `Sim.letC` also threads its continuation match — see the
-- route-A proof at `Bang/Compile.lean:1765`; omitted here, not load-bearing for the verdict.)

/-- ATTEMPT: route-B `Sim.handle`, state arm (the load-bearing case). The route-A proof shape
g-threaded — does NOT close: the body runs `Comp.subst (Val.vcap g ℓ) cy`, and `h` only
transfers `cy`. The `sorry` marks exactly the substitution-closure gap. -/
theorem Sim.handle_state {cx cy : Comp} (h : Sim cx cy) (ℓ : Bang.EffectRow.Label) (s : Val) :
    Sim (.handle (.state ℓ s) cx) (.handle (.state ℓ s) cy) := by
  intro g σ τ b r hb
  cases b with
  | zero => simp [CalcVM.evalD] at hb
  | succ b =>
      simp only [CalcVM.evalD] at hb
      -- hb : (evalD b (g+1) (σ.push g s) τ (Comp.subst (Val.vcap g ℓ) cy)).bind … = some r
      -- `h` transfers `cy`, NOT `subst (vcap g ℓ) cy`.  No way to bridge from `Sim cx cy`.
      sorry

end U5bSpike
