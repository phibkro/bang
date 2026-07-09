/-
CUSTOM-ARM SHADOW-WITNESS PROBE (#44 Stage 4) — refute-first de-risk of the DERIVED evalD custom arm.

Claim under test: an identity-keyed denotational `evalDc` whose custom arm INLINE-SERVICES a
`perform` by running the op's clause body (`subst p (subst (shift v) clause.2)`) as a sub-eval AGREES
with the kernel `Source.eval` on the Stage-2 witness class (customResume → 106, customAbortCoexist → 42).

This mirrors the kernel's `dispatchOn` custom arm (Dispatch.lean:177): resume Kᵢ with the clause's
result, reinstall a deep `handleF n (custom ℓ p clauses)` frame, param UNCHANGED (read-only v1).
In big-step: the frame stays in the store across the service (nested ops handled), so the clause runs
against the SAME store with the custom entry live.

SPIKE only: a MINIMAL denotational machine over the REAL AST + REAL Handler.custom, just enough to run
the witnesses. The store carries per-identity frame payloads (state Val | throws | custom (param,clauses)).
Green ⟹ the inline-clause-service design is the right custom-arm shape; a red is a finding that
redirects the derivation BEFORE the multi-file grind.
-/
import Bang.Core.Semantics.Eval

namespace CustomArmShadowProbe
open Bang

/-- A store frame payload keyed by identity. -/
inductive FP where
  | st  : Val → FP                       -- state param
  | thr : FP                             -- throws (catch)
  | cus : Val → List (OpId × Comp) → FP  -- custom (param, clauses)

abbrev CStore := List (Nat × FP)

def cget : CStore → Nat → Option FP
  | [],          _ => none
  | (m, fp) :: σ, n => if m = n then some fp else cget σ n

/-- outcome: term value, or a raised (identity, op, payload) en route to its handler. -/
inductive Out where
  | term   : Val → Out
  | raised : Nat → OpId → Val → Out

/-- Identity-keyed denotational eval with a DERIVED custom arm (inline clause-service). -/
def evalDc : Nat → Nat → CStore → Comp → Option (Out × Nat × CStore)
  | 0,     _, _, _ => none
  | _ + 1, g, σ, .ret v  => some (.term v, g, σ)
  | _ + 1, g, σ, .lam M  => some (.term (.vthunk M), g, σ)  -- (probe: treat lam as a value carrier)
  | f + 1, g, σ, .letC M N =>
      match evalDc f g σ M with
      | some (.term v, g', σ')       => evalDc f g' σ' (Comp.subst v N)
      | some (.raised n op w, g', σ') => some (.raised n op w, g', σ')
      | none                          => none
  | f + 1, g, σ, .binop op a b =>
      match a, b with
      | .vint x, .vint y => some (.term (op.eval x y), g, σ)
      | _, _ => none
  | f + 1, g, σ, .perform (.vcap n _ℓ) op v =>
      match cget σ n with
      | some (.cus p clauses) =>
          -- INLINE CLAUSE-SERVICE: run the op's clause against the SAME store (frame stays live),
          -- resume with its terminal value. Focus = subst p (subst (shift v) clause.2).
          match clauses.find? (·.1 == op) with
          | some clause =>
              evalDc f g σ (Comp.subst p (Comp.subst (Val.shift v) clause.2))
          | none => some (.raised n op v, g, σ)   -- unserviced op ⇒ raise
      | some (.st s) =>
          if op = "get" then some (.term s, g, σ)
          else some (.raised n op v, g, σ)         -- (probe skips put-threading; not in witness class)
      | _ => some (.raised n op v, g, σ)           -- throws / no frame ⇒ raise toward n
  | f + 1, g, σ, .handle h M =>
      let id := g
      let M' := Comp.subst (.vcap id h.label) M
      match h with
      | .state ℓ s =>
          match evalDc f (g+1) ((id, .st s) :: σ) M' with
          | some (o, g', σ') => some (o, g', σ'.filter (·.1 ≠ id))
          | none => none
      | .custom ℓ p cls =>
          match evalDc f (g+1) ((id, .cus p cls) :: σ) M' with
          | some (o, g', σ') => some (o, g', σ'.filter (·.1 ≠ id))
          | none => none
      | .throws ℓ =>
          match evalDc f (g+1) ((id, .thr) :: σ) M' with
          | some (.term v, g', σ') => some (.term v, g', σ'.filter (·.1 ≠ id))
          | some (.raised n op w, g', σ') =>
              if n = id ∧ op = "raise" then some (.term w, g', σ'.filter (·.1 ≠ id))
              else some (.raised n op w, g', σ'.filter (·.1 ≠ id))
          | none => none
      | .transaction _ _ => none  -- out of witness class
  | _ + 1, _, _, _ => none

/-- Run to a terminal int. -/
def yieldsIntC (fuel : Nat) (M : Comp) (n : Int) : Bool :=
  match evalDc fuel 0 [] M with
  | some (.term (.vint m), _, _) => m == n
  | _ => false

-- The exact Stage-2 witnesses (copied from Eval.lean).
private def readerClauses : List (OpId × Comp) :=
  [("read", .binop .add (.vvar 0) (.vvar 1))]

private def customResume : Comp :=
  .handle (.custom 1 (.vint 100) readerClauses)
    (.letC (.perform (.vvar 0) "read" (.vint 5))
      (.binop .add (.vvar 0) (.vint 1)))

private def customAbortCoexist : Comp :=
  .handle (.throws 2)
    (.handle (.custom 1 (.vint 100) readerClauses)
      (.letC (.perform (.vvar 1) "raise" (.vint 42))
        (.perform (.vvar 0) "read" (.vint 5))))

-- REFUTE-FIRST GATES: the derived custom arm must AGREE with the kernel witnesses
-- (kernel side already gated in Bang/Core/Semantics/Eval.lean: customResume→106, abort→42).
#guard yieldsIntC 200 customResume 106
#guard yieldsIntC 200 customAbortCoexist 42

/-! ## §2 — stress the run_evalD-side risks (nested custom + clause-performs-effect).

The run_evalD induction, once NoCustomFrame drops, must handle a custom frame SITTING IN K under a
perform deep in a sub-eval, and the NoResume 5th conjunct (a raise never resumes) must survive a
custom frame forwarding it. Probe both against the kernel. -/

/-- (c) NESTED custom: an inner custom (label 3, param 10) whose clause reads via an OUTER custom
(label 1, param 100). Tests: the clause body itself performs an effect serviced by a DIFFERENT live
custom frame (deep-handler recursion at the residual row). Kernel: read3 x = (read1 x) ... let's keep
it simple — inner clause resumes with arg+param, outer likewise; two frames coexist. -/
private def innerClauses : List (OpId × Comp) :=
  [("tick", .binop .add (.vvar 0) (.vvar 1))]   -- tick a = a + param

-- indices: in the letC continuation (under +1 binder), letC-result=var0, inner-cap=var1, outer-cap=var2.
private def nestedCustom : Comp :=
  .handle (.custom 1 (.vint 100) readerClauses)              -- outer: read, cap ⤳ var1 in body
    (.handle (.custom 3 (.vint 10) innerClauses)             -- inner: tick, cap ⤳ var0 in body
      (.letC (.perform (.vvar 0) "tick" (.vint 5))           -- tick 5 ⤳ 5+10 = 15
        (.perform (.vvar 2) "read" (.vvar 0))))              -- read 15 ⤳ 15+100 = 115

#guard yieldsIntC 200 nestedCustom 115

/-- (d) custom frame FORWARDS a raise (NoResume risk): a raise (label 2, throws) targeting an OUTER
throws must propagate PAST a live custom frame unresumed. Same as customAbortCoexist but the custom
frame is BETWEEN and the throws is OUTERMOST — verifies the custom `handle` arm forwards a raised
outcome (pop entry) without accidentally servicing/resuming it. -/
-- indices: in the letC continuation, custom-cap=var1, throws-cap=var2.
private def customForwardsRaise : Comp :=
  .handle (.throws 2)
    (.handle (.custom 1 (.vint 100) readerClauses)
      (.letC (.perform (.vvar 0) "read" (.vint 5))    -- read 5 ⤳ 105 (custom services)
        (.perform (.vvar 2) "raise" (.vint 77))))     -- THEN raise 77 ⤳ abort past custom to throws
#guard yieldsIntC 200 customForwardsRaise 77

/-- kernel-side confirmation the §2 witnesses are the real ones (Source.eval is public). -/
private def kInt (fuel : Nat) (c : Comp) (n : Int) : Bool :=
  match Source.eval fuel c with | .done (.vint m) => m == n | _ => false
#guard kInt 200 nestedCustom 115
#guard kInt 200 customForwardsRaise 77

end CustomArmShadowProbe
