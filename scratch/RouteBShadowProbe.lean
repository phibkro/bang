/-
U3 SHADOW-WITNESS SPIKE (inc-6, task #55) — refute-first de-risk of CalcVM route-B (ADR-0052).

Claim under test: a cap-keyed (IDENTITY-dispatched) denotational `evalD'` AGREES with the kernel
`Source.eval` on the exact program that motivated route-B — the same-label-shadowing witness where
the STALE label-keyed `evalD` diverges. Today: kernel 10, stale evalD 20 (ADR-0052, both `rfl`).

This is a SPIKE, not the port: a MINIMAL get-only denotational machine over the REAL AST, just enough
to run the witness. `evalD'` (route-B) and `evalDold` (route-A, the current CalcVM behaviour) are
IDENTICAL except the dispatch key — `evalD'` looks up the store by capability IDENTITY `n`, `evalDold`
by LABEL `ℓ` (nearest). Both mint+substitute `vcap g h.label` at `handle` exactly like the kernel
(Operational.lean:471), so the ONLY semantic variable is the dispatch key. The triptych isolates it.

Outcome (decisive both ways):
  · #guards green ⟹ route-B's hardest semantic claim (identity-keyed evalD ≡ kernel on the shadow case)
    is de-risked → commission the U2/U3 grind.
  · a #guard fails ⟹ the refutation, surfaced before the multi-session sink.
-/
import Bang.Operational

namespace RouteBShadowProbe
open Bang

/-! ### The witness (ADR-0052), in the REAL AST.

`handle (state 1 10) (handle (state 1 20) (perform <outer-cap> 1 "get"))`. Both handlers carry LABEL 1
(the shadow). Inside the inner body, de Bruijn: var 0 = inner cap (just bound), var 1 = OUTER cap
(bound by the outer handle, shifted past the inner binder). The `perform` names var 1 ⟹ the OUTER
handler ⟹ lexical answer 10. The label-keyed machine instead finds the NEAREST label-1 store = 20. -/
def witness : Comp :=
  .handle (.state 1 (.vint 10))
    (.handle (.state 1 (.vint 20))
      (.perform (.vvar 1) "get" .vunit))

/-! ### route-B: identity-keyed denotational `evalD'` (the CalcVM reference, cap-keyed).

Store keyed by capability IDENTITY `n`. `handle` MINTS `id := g`, pushes `(id, s)`, SUBSTITUTES
`vcap id ℓ` for the handle-bound var 0, recurses with `g+1`, and pops its entry on return — mirroring
the kernel's global-fresh mint (Operational.lean:471) and `splitAtId` identity lookup (:284). -/
abbrev IStore := List (Nat × Val)

def istoreGet : IStore → Nat → Option Val
  | [],          _ => none
  | (m, v) :: σ, n => if m = n then some v else istoreGet σ n

def evalD' : Nat → Nat → IStore → Comp → Option (Val × Nat × IStore)
  | 0,      _, _, _ => none
  | _ + 1,  g, σ, .ret v => some (v, g, σ)
  | f + 1,  g, σ, .handle (.state ℓ s) M =>
      let id := g
      match evalD' f (g + 1) ((id, s) :: σ) (Comp.subst (.vcap id ℓ) M) with
      | some (v, g', σ') => some (v, g', σ'.filter (fun p => p.1 ≠ id))   -- pop this handler's entry
      | none             => none
  | _ + 1,  g, σ, .perform (.vcap n _ℓ) "get" _ =>   -- DISPATCH BY IDENTITY n
      match istoreGet σ n with
      | some s => some (s, g, σ)
      | none   => none
  | _,      _, _, _ => none

/-! ### route-A: label-keyed denotational `evalDold` (the STALE CalcVM behaviour, nearest-label).

IDENTICAL mint+subst to `evalD'` — so the perform receives the SAME `vcap g ℓ` — but the store is keyed
by LABEL and lookup is NEAREST. This is what the current `evalD` computes (the dynamic dispatch). -/
abbrev LStore := List (Bang.EffectRow.Label × Val)

def lstoreGet : LStore → Bang.EffectRow.Label → Option Val
  | [],          _ => none
  | (m, v) :: σ, ℓ => if m = ℓ then some v else lstoreGet σ ℓ   -- nearest matching LABEL

def evalDold : Nat → Nat → LStore → Comp → Option Val
  | 0,     _, _, _ => none
  | _ + 1, _, _, .ret v => some v
  | f + 1, g, σ, .handle (.state ℓ s) M =>
      evalDold f (g + 1) ((ℓ, s) :: σ) (Comp.subst (.vcap g ℓ) M)   -- mint+subst (same as evalD')
  | _ + 1, _, σ, .perform (.vcap _n ℓ) "get" _ => lstoreGet σ ℓ      -- DISPATCH BY LABEL ℓ (ignores n)
  | _,     _, _, _ => none

/-! ### Observation helpers — extract the Int from each rep's terminal. -/
def d'Int  (r : Option (Val × Nat × IStore)) : Option Int :=
  match r with | some (.vint n, _, _) => some n | _ => none
def oldInt (r : Option Val) : Option Int :=
  match r with | some (.vint n) => some n | _ => none
def kInt   (r : Bang.Result Val) : Option Int :=
  match r with | .done (.vint n) => some n | _ => none

/-! ## The triptych — kernel ≡ route-B ≠ route-A, all on the SAME witness term. -/

-- route-A (label / nearest, the STALE behaviour): reads the inner shadow = 20  (the bug)
#guard oldInt (evalDold 50 0 [] witness) == some 20

-- route-B (identity / cap-keyed, the re-derivation): reads the OUTER named handler = 10  (the fix)
#guard d'Int (evalD' 50 0 [] witness) == some 10

-- the kernel ORACLE (real `Source.eval`): 10 — route-B AGREES, route-A does NOT
#guard kInt (Source.eval 50 witness) == some 10

-- the agreement stated directly: route-B ≡ kernel, and route-B ≠ route-A on this program
#guard d'Int (evalD' 50 0 [] witness) == kInt (Source.eval 50 witness)
#guard d'Int (evalD' 50 0 [] witness) != oldInt (evalDold 50 0 [] witness)

end RouteBShadowProbe
