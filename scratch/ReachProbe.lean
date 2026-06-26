/-
  scratch/ReachProbe.lean — DE-RISK SPIKE for opt-2 (focus-reachability-refined invariant), task #38.
  ─────────────────────────────────────────────────────────────────────────────────────────────
  THE WALL (Model.lean:507 `wsCfg_step`, POP arm): the ADR-0057 deep-modulo-non-performability
  invariant `WSV` (Model.lean:214) gates a cap by its AMBIENT ROW — a cap under a thunk `U φ B`
  with `ℓ ∈ φ` is required to resolve. The sibling-pinned counterexample
      v := vthunk( app (lam (ret vunit)) (vthunk (perform (vcap g_h) "get" vunit)) )
  carries a `g_h`-cap under an arg-thunk of row `labelEff 1`; the gate fires, yet the cap is
  OPERATIONALLY DEAD (the `lam (ret vunit)` discards its argument → the inner perform is never
  forced). After POP of `handleF g_h`, `splitAtId K g_h = none` ⇒ `WSV` FALSE ⇒ not preserved.

  OPT-2 IDEA: gate a cap only if it can REACH a focus-perform position. Model "reachable" as a
  liveness flag `live : Bool` threaded into the invariant: the gate fires only at live caps; a
  value STORED (app-arg) or RETURNED (ret) is checked DORMANT (`live := false`, no obligation),
  so the dead arg-thunk cap is excluded BY CONSTRUCTION and POP closes for it trivially.

  THIS PROBE BUILDS the refined invariant and pins, build-checked, the two facts that decide the
  option:
    §1  POP closes trivially for the dead cap  (the win — `rwsv_dormant_deadcap`, NO sorry).
    §2  PRESERVATION needs a DORMANT→LIVE promotion that is build-REFUTABLY FALSE
        (`promotion_is_false`, NO sorry) — the force/β arm forces a value that was stored dormant,
        and no structural fact supplies its now-required resolution. That promotion is exactly the
        operational-reachability fact ("the forced thunk's handler is still live") = the soundness
        theorem itself ⇒ it can only come from a step-indexed `▷` (opt-1), not first-order.
-/
import Bang.Model

namespace Bang.ReachProbe

open Bang
open Bang.Model (ResolvesLabel)
open Bang.EffectRow (Label)

variable {Eff Mult : Type} [Lattice Eff] [OrderBot Eff] [CommSemiring Mult]
  [DecidableEq Mult] [EffSig Eff Mult]

/-! ## The reachability-refined invariant — `live : Bool` replaces the ambient row `ρ`. -/

mutual
/-- `RWSV K live v A`: every cap in `v` that can REACH a focus-perform resolves. `live` is the
reachability flag — `true` means "the evaluator will force this position". The gate fires ONLY at
a live `vcap`. A thunk PROPAGATES the flag unchanged (a forced thunk's body is live; a dormant
thunk's body stays dormant) — NO row reset, the whole point of opt-2 over ADR-0057. -/
inductive RWSV (K : EvalCtx) : Bool → Val → VTy Eff Mult → Prop where
  | vunit {b} : RWSV K b Val.vunit VTy.unit
  | vint {b n} : RWSV K b (Val.vint n) VTy.int
  | vvar {b i A} : RWSV K b (Val.vvar i) A
  -- LIVE cap: must resolve. DORMANT cap: no obligation (the reachability weakening).
  | vcap_live {n ℓ} (h : ResolvesLabel K n ℓ) : RWSV K true (Val.vcap n ℓ) (VTy.cap ℓ)
  | vcap_dormant {n ℓ} : RWSV K false (Val.vcap n ℓ) (VTy.cap ℓ)
  | vthunk {b c φ B} (h : RWSC K b c φ B) : RWSV K b (Val.vthunk c) (VTy.U φ B)
  | inl {b v A B} (h : RWSV K b v A) : RWSV K b (Val.inl v) (VTy.sum A B)
  | inr {b v A B} (h : RWSV K b v B) : RWSV K b (Val.inr v) (VTy.sum A B)
  | pair {b a c A B} (h1 : RWSV K b a A) (h2 : RWSV K b c B) : RWSV K b (Val.pair a c) (VTy.prod A B)
  | fold {b v A} (h : RWSV K b v (VTy.unrollMu A)) : RWSV K b (Val.fold v) (VTy.mu A)
/-- `RWSC K live c φ C`: companion for computations. The flag flows to eliminator positions:
`force v` and `perform cv` FORCE their value (live); `app M v` STORES `v` (dormant); `ret v`
RETURNS `v` — its liveness is the CONSUMER's to decide, but the consumer is in the STACK, not
here, so `ret` must commit to one flag with no consumer in view (the structural dilemma). -/
inductive RWSC (K : EvalCtx) : Bool → Comp → Eff → CTy Eff Mult → Prop where
  | ret {b v A q} (h : RWSV K false v A) : RWSC K b (Comp.ret v) ⊥ (CTy.F q A)   -- DORMANT choice
  | letC {b M N φ₁ φ₂ q1 A B} (h1 : RWSC K b M φ₁ (CTy.F q1 A)) (h2 : RWSC K b N φ₂ B) :
      RWSC K b (Comp.letC M N) (φ₁ ⊔ φ₂) B
  -- FORCES `v` WHEN this computation runs ⇒ `v` inherits THIS computation's flag `b` (a force under a
  -- dormant thunk is itself dormant). This propagation is what lets a dormant arg-thunk's inner
  -- perform be dormant — the opt-2 win — while a LIVE force still demands `RWSV K true v`.
  | force {b v φ B} (h : RWSV K b v (VTy.U φ B)) : RWSC K b (Comp.force v) φ B
  | lam {b M φ q A B} (h : RWSC K b M φ B) : RWSC K b (Comp.lam M) φ (CTy.arr q A B)
  | app {b M v φ q A B} (h1 : RWSC K b M φ (CTy.arr q A B)) (h2 : RWSV K false v A) :  -- STORES: dormant
      RWSC K b (Comp.app M v) φ B
  -- the cap is performed WHEN this computation runs ⇒ cap inherits flag `b`; the payload is passed
  -- to the handler ⇒ dormant here.
  | perform {b cv op v φ q A B ℓ} (h1 : RWSV K b cv (VTy.cap ℓ)) (h2 : RWSV K false v A) :
      RWSC K b (Comp.perform cv op v) φ (CTy.F q B)
end

/-! ## §1 — THE WIN: POP closes trivially for the dead arg-thunk cap.

A DORMANT cap carries no obligation, so the counterexample value `v` (whose `g_h`-cap lives under a
dormant arg-thunk) is `RWSV K false v A` for ANY stack `K` — including the popped `K` with
`splitAtId K g_h = none`. The carry-drop DISSOLVES: nothing to re-establish. -/

/-- The dead-cap fragment of the counterexample, `vthunk (perform (vcap g_h ℓ) op vunit)` in
DORMANT position, is `RWSV` over ANY stack (even one where `g_h` no longer resolves). This is the
POP-arm win: a dormant cap is vacuously well-scoped. -/
theorem rwsv_dormant_deadcap (K : EvalCtx) (g_h : Nat) (ℓ : Label) (op : OpId) (φ : Eff) (q : Mult) :
    RWSV (Eff := Eff) (Mult := Mult) K false
      (Val.vthunk (Comp.perform (Val.vcap g_h ℓ) op Val.vunit))
      (VTy.U φ (CTy.F q VTy.unit)) :=
  .vthunk (.perform .vcap_dormant .vunit)

/-! ## §2 — THE WALL: preservation needs a DORMANT→LIVE promotion that is FALSE.

The force/β arm: `(g, appF v :: K, lam M) ↦ (g, K, subst v M)`. If the lam body `M` FORCES var 0
(e.g. `M = force (vvar 0)`), the reduct contains `v` in a `force` position ⇒ `RWSC` of the reduct
needs `RWSV K true v` (the `force` rule). But the pre-state stored `v` DORMANT (`RWSV K false v`,
the `app` rule). So preservation requires the promotion `RWSV K false v A → RWSV K true v A`.

It is FALSE: a cap whose handler was popped satisfies the dormant form vacuously but the live form
is unprovable (`ResolvesLabel` fails). Build-refuted below. The promotion holds ONLY when the
cap's handler is live on `K` — an operational-reachability fact that is the soundness theorem
itself, available only behind a step-index `▷` (= opt-1). -/

/-- **BUILD-REFUTED.** The dormant→live promotion that the force/β preservation arm requires is
false. Witness: empty stack (handler popped), bare cap `vcap 0 ℓ`. Dormant holds; live forces
`ResolvesLabel [] 0 ℓ`, and `splitAtId [] 0 = none`. -/
theorem promotion_is_false (ℓ : Label) :
    ¬ (∀ (K : EvalCtx) (v : Val) (A : VTy Eff Mult),
        RWSV (Eff := Eff) (Mult := Mult) K false v A → RWSV K true v A) := by
  intro hpromote
  -- feed it the popped-handler dormant cap.
  have hlive : RWSV (Eff := Eff) (Mult := Mult) [] true (Val.vcap 0 ℓ) (VTy.cap ℓ) :=
    hpromote [] (Val.vcap 0 ℓ) (VTy.cap ℓ) .vcap_dormant
  -- invert: live demands `ResolvesLabel [] 0 ℓ`, i.e. `splitAtId [] 0 = some …` — impossible.
  cases hlive with
  | vcap_live h =>
      obtain ⟨Kᵢ, hh, Kₒ, hsplit, _⟩ := h
      rw [show splitAtId ([] : EvalCtx) 0 = none from rfl] at hsplit
      exact absurd hsplit (by simp)

end Bang.ReachProbe

#print axioms Bang.ReachProbe.rwsv_dormant_deadcap
#print axioms Bang.ReachProbe.promotion_is_false
