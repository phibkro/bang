/-
  scratch/hang61/SizeProbe2.lean — issue #61, curve confirmation + error-vs-size disambiguation.

  SizeProbe.lean showed a LINEAR size curve (321/375/429, +54/sibling) — refuting
  geometric elaboration blowup. This file (a) confirms the sib programs ELABORATE
  (not silently error → size 0), (b) extends N to 4,5 to confirm linearity holds,
  (c) prints the exact per-sibling delta, (d) sizes the ACTUAL json main.bang.
-/
import Bang.Frontend.TypeCheck
import Bang.Core.IR

namespace Bang.Hang61b
open Bang Bang.TypeCheck

mutual
def sizeV : Val → Nat
  | .vunit | .vint _ | .vvar _ | .vcap _ _ => 1
  | .vthunk c => 1 + sizeC c
  | .inl v | .inr v | .fold v => 1 + sizeV v
  | .pair a b => 1 + sizeV a + sizeV b
termination_by v => sizeOf v
def sizeC : Comp → Nat
  | .ret v | .force v | .unfold v => 1 + sizeV v
  | .letC m n => 1 + sizeC m + sizeC n
  | .lam m => 1 + sizeC m
  | .app m v => 1 + sizeC m + sizeV v
  | .perform c _ v => 1 + sizeV c + sizeV v
  | .handle h m => 1 + sizeH h + sizeC m
  | .case v a b => 1 + sizeV v + sizeC a + sizeC b
  | .split v n => 1 + sizeV v + sizeC n
  | .binop _ a b => 1 + sizeV a + sizeV b
  | .oom | .wrong _ => 1
termination_by c => sizeOf c
def sizeH : Handler → Nat
  | .state _ v => 1 + sizeV v
  | .throws _ => 1
  | .transaction _ vs => 1 + sizeVL vs
  | .custom _ v cls => 1 + sizeV v + sizeCl cls
termination_by h => sizeOf h
def sizeVL : List Val → Nat
  | [] => 0 | v :: vs => sizeV v + sizeVL vs
termination_by vs => sizeOf vs
def sizeCl : List (OpId × Comp) → Nat
  | [] => 0 | (_, c) :: ps => sizeC c + sizeCl ps
termination_by ps => sizeOf ps
end

/-- Report `.ok size` or `.error` distinctly: returns `(isOk, size)`. -/
def elabReport (src : String) : Bool × Nat :=
  match checkAndLower src with
  | .ok c => (true, sizeC c)
  | .error _ => (false, 0)

#eval elabReport (include_str "sib1.bang")   -- expect (true, 321)
#eval elabReport (include_str "sib2.bang")   -- expect (true, 375)
#eval elabReport (include_str "sib3.bang")   -- expect (true, 429)
#eval elabReport (include_str "sib4.bang")
#eval elabReport (include_str "sib5.bang")

/-- The real dogfood program (the checked-in scoped-down main.bang). -/
#eval elabReport (include_str "../../examples/json/main.bang")

end Bang.Hang61b
