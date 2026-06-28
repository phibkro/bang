/-
U3 SHADOW-WITNESS SPIKE (inc-6, task #55) — refute-first de-risk of CalcVM route-B (ADR-0052).

Claim under test: a cap-keyed (IDENTITY-dispatched) denotational `evalD'` AGREES with the kernel
`Source.eval` on the programs that motivate route-B — where the STALE label-keyed `evalD` diverges.

SPIKE only: a MINIMAL denotational machine over the REAL AST, just enough to run the witnesses.
`evalD'` (route-B) and `evalDold` (route-A, the current CalcVM behaviour) are IDENTICAL except the
store KEY — `evalD'` keys/looks-up by capability IDENTITY `n` (mirroring `splitAtId`/`idDispatch`),
`evalDold` by LABEL `ℓ` (nearest). BOTH mint+substitute `vcap g h.label` at `handle` threading `g`,
exactly like the kernel (Operational.lean:471). So the ONLY semantic variable is the dispatch key.

Coverage (the de-risk ladder):
  §1 GET shadow      — the original ADR-0052 witness (value read through the OUTER cap).
  §2 PUT-threading   — mutation through the OUTER cap, then read; the σ-update the get-only spike missed.
  §3 return-only     — vacuous `throws`/`state` handler (the ADR-0052 retained-feature risk).
  §4 multi-frame     — heterogeneous nested frames (distinct labels, throws+state) — store coherence.

Gate per case: `#guard evalD' ≡ kernel` (+ `≠ evalDold` where the regimes diverge). No bridge, no Corr
proof — that is still U3. Green across all ⟹ the mutation + retained-feature semantic core is de-risked.
-/
import Bang.Operational

namespace RouteBShadowProbe
open Bang

/-! ## The two minimal denotational machines (identical but for the store KEY).

Both thread a store and a fresh-id counter `g`, MINT `id := g` + SUBSTITUTE `vcap id ℓ` at `handle`,
and pop the frame on return — the kernel's discipline. `evalD'` keys by IDENTITY; `evalDold` by LABEL. -/

abbrev IStore := List (Nat × Val)                       -- route-B: keyed by capability IDENTITY n
abbrev LStore := List (Bang.EffectRow.Label × Val)      -- route-A: keyed by effect LABEL ℓ

def istoreGet : IStore → Nat → Option Val
  | [],          _ => none
  | (m, v) :: σ, n => if m = n then some v else istoreGet σ n
def istoreSet : IStore → Nat → Val → Option IStore
  | [],          _, _ => none
  | (m, v) :: σ, n, w => if m = n then some ((m, w) :: σ) else (istoreSet σ n w).map ((m, v) :: ·)

def lstoreGet : LStore → Bang.EffectRow.Label → Option Val   -- NEAREST matching label
  | [],          _ => none
  | (m, v) :: σ, ℓ => if m = ℓ then some v else lstoreGet σ ℓ
def lstoreSet : LStore → Bang.EffectRow.Label → Val → Option LStore   -- NEAREST matching label
  | [],          _, _ => none
  | (m, v) :: σ, ℓ, w => if m = ℓ then some ((m, w) :: σ) else (lstoreSet σ ℓ w).map ((m, v) :: ·)

/-- route-B: IDENTITY-keyed. perform resolves the cap's identity `n`; state lives at key `n`. -/
def evalD' : Nat → Nat → IStore → Comp → Option (Val × Nat × IStore)
  | 0,     _, _, _ => none
  | _ + 1, g, σ, .ret v => some (v, g, σ)
  | f + 1, g, σ, .letC M N =>                                   -- sequence: thread store + counter
      match evalD' f g σ M with
      | some (v, g', σ') => evalD' f g' σ' (Comp.subst v N)
      | none             => none
  | f + 1, g, σ, .handle (.state ℓ s) M =>
      let id := g
      match evalD' f (g + 1) ((id, s) :: σ) (Comp.subst (.vcap id ℓ) M) with
      | some (v, g', σ') => some (v, g', σ'.filter (·.1 ≠ id))  -- pop THIS handler's cell (by id)
      | none             => none
  | f + 1, g, σ, .handle (.throws ℓ0) M =>                      -- vacuous/return-only: throws-return = id
      evalD' f (g + 1) σ (Comp.subst (.vcap g ℓ0) M)
  | _ + 1, g, σ, .perform (.vcap n _ℓ) "get" _ =>               -- DISPATCH BY IDENTITY n
      match istoreGet σ n with
      | some s => some (s, g, σ)
      | none   => none
  | _ + 1, g, σ, .perform (.vcap n _ℓ) "put" w =>               -- DISPATCH BY IDENTITY n
      match istoreSet σ n w with
      | some σ' => some (.vunit, g, σ')
      | none    => none
  | _,     _, _, _ => none

/-- route-A: LABEL-keyed (the stale CalcVM behaviour) — IDENTICAL but for the lookup key. -/
def evalDold : Nat → Nat → LStore → Comp → Option (Val × Nat × LStore)
  | 0,     _, _, _ => none
  | _ + 1, g, σ, .ret v => some (v, g, σ)
  | f + 1, g, σ, .letC M N =>
      match evalDold f g σ M with
      | some (v, g', σ') => evalDold f g' σ' (Comp.subst v N)
      | none             => none
  | f + 1, g, σ, .handle (.state ℓ s) M =>
      match evalDold f (g + 1) ((ℓ, s) :: σ) (Comp.subst (.vcap g ℓ) M) with
      | some (v, g', σ') => some (v, g', σ'.tail)               -- pop the most-recent (head) frame
      | none             => none
  | f + 1, g, σ, .handle (.throws ℓ0) M =>
      evalDold f (g + 1) σ (Comp.subst (.vcap g ℓ0) M)
  | _ + 1, g, σ, .perform (.vcap _n ℓ) "get" _ =>              -- DISPATCH BY LABEL ℓ (nearest)
      match lstoreGet σ ℓ with
      | some s => some (s, g, σ)
      | none   => none
  | _ + 1, g, σ, .perform (.vcap _n ℓ) "put" w =>              -- DISPATCH BY LABEL ℓ (nearest)
      match lstoreSet σ ℓ w with
      | some σ' => some (.vunit, g, σ')
      | none    => none
  | _,     _, _, _ => none

/-! ### Observation helpers. -/
def d'Int  (r : Option (Val × Nat × IStore)) : Option Int := match r with | some (.vint n, _, _) => some n | _ => none
def oldInt (r : Option (Val × Nat × LStore)) : Option Int := match r with | some (.vint n, _, _) => some n | _ => none
def kInt   (r : Bang.Result Val) : Option Int := match r with | .done (.vint n) => some n | _ => none

/-! ## §1 — GET shadow (the original ADR-0052 witness).
`handle (state 1 10) (handle (state 1 20) (perform <outer-cap> 1 "get"))`. Inside the inner body
var 1 = OUTER cap ⟹ lexical 10; nearest-label = 20. -/
def wGet : Comp :=
  .handle (.state 1 (.vint 10)) (.handle (.state 1 (.vint 20)) (.perform (.vvar 1) "get" .vunit))

#guard oldInt (evalDold 50 0 [] wGet) == some 20          -- route-A: inner shadow (the bug)
#guard d'Int  (evalD'   50 0 [] wGet) == some 10          -- route-B: the OUTER named handler
#guard kInt   (Source.eval 50 wGet)   == some 10          -- kernel oracle
#guard d'Int  (evalD' 50 0 [] wGet) == kInt (Source.eval 50 wGet)
#guard d'Int  (evalD' 50 0 [] wGet) != oldInt (evalDold 50 0 [] wGet)

/-! ## §2 — PUT-threading (the σ-update the get-only spike didn't exercise).

de Bruijn inside the inner body, under the `letC` (binds the put's unit result at var 0):
  · in M (the put, pre-binder):   var0 = inner cap, var1 = OUTER cap
  · in N (post-binder):           var0 = unit,  var1 = inner cap, var2 = OUTER cap

§2a PUT outer ; GET outer  — proves the mutation THREADS to the outer cell (both regimes → 99). -/
def wPutGetOuter : Comp :=
  .handle (.state 1 (.vint 10)) (.handle (.state 1 (.vint 20))
    (.letC (.perform (.vvar 1) "put" (.vint 99))    -- put via OUTER (var1 in M)
           (.perform (.vvar 2) "get" .vunit)))       -- get via OUTER (var2 in N)

#guard d'Int (evalD' 50 0 [] wPutGetOuter) == some 99            -- put threaded to outer cell
#guard d'Int (evalD' 50 0 [] wPutGetOuter) == kInt (Source.eval 50 wPutGetOuter)

/-! §2b PUT outer ; GET inner — proves the put landed on the IDENTITY-correct (outer) cell:
identity reads inner=20 (untouched); label put+get both hit inner ⟹ 99. Divergence + threading. -/
def wPutGetInner : Comp :=
  .handle (.state 1 (.vint 10)) (.handle (.state 1 (.vint 20))
    (.letC (.perform (.vvar 1) "put" (.vint 99))    -- put via OUTER (var1 in M)
           (.perform (.vvar 1) "get" .vunit)))       -- get via INNER (var1 in N)

#guard d'Int  (evalD' 50 0 [] wPutGetInner) == some 20           -- inner cell untouched by the outer put
#guard oldInt (evalDold 50 0 [] wPutGetInner) == some 99         -- route-A: put+get both hit inner
#guard d'Int  (evalD' 50 0 [] wPutGetInner) == kInt (Source.eval 50 wPutGetInner)
#guard d'Int  (evalD' 50 0 [] wPutGetInner) != oldInt (evalDold 50 0 [] wPutGetInner)

/-! ## §3 — return-only / vacuous handlers (ADR-0052 retained-feature risk).
A handler over a body that never performs must evaluate cleanly (pop the unused frame). -/
def wReturnThrows : Comp := .handle (.throws 0) (.ret (.vint 7))           -- the canonical return-only witness
def wReturnState  : Comp := .handle (.state 1 (.vint 5)) (.ret (.vint 7))  -- unused state frame

#guard d'Int (evalD' 50 0 [] wReturnThrows) == some 7
#guard d'Int (evalD' 50 0 [] wReturnThrows) == kInt (Source.eval 50 wReturnThrows)
#guard d'Int (evalD' 50 0 [] wReturnState)  == some 7
#guard d'Int (evalD' 50 0 [] wReturnState)  == kInt (Source.eval 50 wReturnState)

/-! ## §4 — multi-frame coherence (heterogeneous nested frames).
§4a distinct labels: read the OUTER (label 1) through its cap past an inner label-2 frame.
  inside inner body: var1 = outer cap (label 1) ⟹ 10. (No shadow; tests the store stays coherent
  across a heterogeneous frame.) -/
def wTwoLabels : Comp :=
  .handle (.state 1 (.vint 10)) (.handle (.state 2 (.vint 20)) (.perform (.vvar 1) "get" .vunit))

#guard d'Int (evalD' 50 0 [] wTwoLabels) == some 10
#guard d'Int (evalD' 50 0 [] wTwoLabels) == kInt (Source.eval 50 wTwoLabels)

/-! §4b throws OVER state: a return-only throws wrapping a state-get through the inner cap.
  inside the state body: var0 = state cap (label 1); the throws above is the outer binder, so from the
  perform's view var0 = state cap ⟹ 10. Tests state-under-throws frame interleaving. -/
def wThrowsOverState : Comp :=
  .handle (.throws 9) (.handle (.state 1 (.vint 10)) (.perform (.vvar 0) "get" .vunit))

#guard d'Int (evalD' 50 0 [] wThrowsOverState) == some 10
#guard d'Int (evalD' 50 0 [] wThrowsOverState) == kInt (Source.eval 50 wThrowsOverState)

end RouteBShadowProbe
