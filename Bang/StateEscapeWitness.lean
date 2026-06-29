module

-- `#guard stateEscape_escaped` runs `Source.eval` (compiled Operational) at the META
-- phase → `meta import` Operational alongside the runtime import.
meta import Bang.Semantics
public import Bang.Semantics
public import Bang.Soundness
public import Bang.Grade

/-! # State-escape probe — the ③ verdict: BLOCKED by the closed-state discipline (task #50)

⚠ The candidate soundness hole (a capability escaping via a `state` cell, since B-occ guards the handler
ANSWER type `A`, not the state type `S`) is **CLOSED by the type system**, NOT a real hole.

`stateEscape` (below) is the would-be witness: VcapFree, and behaviourally STUCK (`#guard`) — it `put`s an
inner-handler cap into an outer `state 1` cell typed to hold a `cap 2`, then `get`s it back after the
inner handler pops and performs on the dangling cap (`splitAtId … = none`). The escape is REAL behaviour.

BUT it is **UNTYPEABLE** (`stateEscape_not_typeable`): `HasCTy.handleState` requires the initial state to
be a CLOSED value `HasVTy [] [] s₀ S` (ADR-0025 D2, the grade discipline). A cap-typed state `S = cap ℓ`
is inhabited ONLY by a `vcap` (the sole closed `cap`-value) — which **VcapFree forbids** — so a cap-holding
`state` cell is uninstantiable in the diagonal's VcapFree precondition. (`vvar`-initialised state, as here,
fails the `HasVTy [] []` closedness directly.) Hence reachable configs never have caps in stored state, so
`FreshCfg`/`CapsBelow` not bounding state caps is SOUND. The closed-state premise is the guard. -/

namespace Bang.StateEscapeWitness
open Bang
open Bang.EffectRow (Label EffRow)

/-- The would-be escape: outer `state 2` (id 0) binds cap_a:cap 2 used as the `state 1` cell's initial
value; `state 1` (id 1) holds a `cap 2`; inner `state 2` (id 2) binds cap_b:cap 2, `put` into the id-1
cell, then pops; `get` the id-1 cell back (= cap_b, now dangling) and perform ⇒ dispatch to popped id 2
⇒ STUCK. VcapFree (caps only minted by handlers). -/
def stateEscape : Comp :=
  .handle (.state 2 .vunit)
    (.handle (.state 1 (.vvar 0))
      (.letC
        (.handle (.state 2 .vunit)
          (.perform (.vvar 1) "put" (.vvar 0)))
        (.letC
          (.perform (.vvar 1) "get" .vunit)
          (.perform (.vvar 0) "get" .vunit))))

/-- BEHAVIOUR (compiled `#guard`): the escape is real — `stateEscape` runs to the DEFINED
capability-escape fail-loud `.escapedCap` (ADR-0063; was `.stuck` before the reclassification). -/
private def stateEscape_escaped : Bool :=
  match Source.eval 500 stateEscape with | .escapedCap => true | _ => false
#guard stateEscape_escaped

/-- **THE VERDICT: `stateEscape` is HasCTy-UNTYPEABLE** — for ANY `EffSig` (structural, no instance
facts). Peeling the two outer `state` handles, the `state 1` cell's initial value `s₀ = vvar 0` must be
CLOSED (`HasVTy [] [] (vvar 0) S`, the ADR-0025 D2 discipline) — impossible (`[][0]? = none`). More
broadly: a cap-typed state `S = cap ℓ` needs a closed `cap`-value = a `vcap`, which VcapFree forbids. So
the ③ candidate hole is the type system already excluding it (answer (a)), NOT a freshness-model leak. -/
theorem stateEscape_not_typeable [EffSig EffRow QTT] :
    ¬ ∃ (γ : GradeVec QTT) (Γ : TyCtx EffRow QTT) (e : EffRow) (C : CTy EffRow QTT),
        HasCTy (Eff := EffRow) (Mult := QTT) γ Γ stateEscape e C := by
  rintro ⟨γ, Γ, e, C, h⟩
  simp only [stateEscape] at h
  -- peel the outer `state 2` (id 0): its body (the `state 1` handle) types under `cap 2 :: Γ`.
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hbodyA, _, _⟩ := h.handleState_inv
  -- peel the `state 1` (id 1): its closed-state premise is `HasVTy [] [] (vvar 0) S` — and `vvar 0`
  -- has no type in the empty context.
  obtain ⟨_, _, _, S1, _, _, _, _, _, _, _, hs1, _, _, _⟩ := hbodyA.handleState_inv
  -- `hs1 : HasVTy [] [] (vvar 0) S1` — but `vvar 0` has no type in the empty context. Generalise the
  -- grade index to a variable so the `vvar` elimination unifies (`basis 0 0` vs the literal `[]`).
  suffices hcontra : ∀ (γg : GradeVec QTT),
      HasVTy (Eff := EffRow) (Mult := QTT) γg [] (Val.vvar 0) S1 → False from hcontra [] hs1
  intro γg hg
  cases hg with | vvar hget => exact absurd hget (by simp)

end Bang.StateEscapeWitness
