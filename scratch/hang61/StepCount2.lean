/-
  scratch/hang61/StepCount2.lean — issue #61, step-count for the arrN battery.

  Pairs with the CLI wall-times (arr1..arr5 = 1.05/1.46/1.97/2.60/2.80s). If step
  COUNT is ~linear in N while wall-time is ~linear in N, then cost-per-step is a
  large CONSTANT — the whole-body `Comp.subst` per knot unfold. That confirms the
  cost is STEP-COST (each step walks the large knot body), not step-count blowup.
-/
import Bang.Frontend.TypeCheck
import Bang.Core.Semantics.Eval

namespace Bang.Hang61Steps2
open Bang Bang.TypeCheck

def ladder : List Nat := (List.range 100).map (fun i => (i + 1) * 500)   -- 500 … 50000

def firstDone (c : Comp) : String :=
    match ladder.find? (fun f => match Bang.Source.eval f c with | .done _ => true | _ => false) with
    | some f => s!"done at {f} steps"
    | none   => "NOT done by 50000"

def report (tag src : String) : IO Unit := do
  match checkAndLower src with
  | .error e => IO.println s!"{tag}: ELAB-ERROR {e.1}"
  | .ok c    => IO.println s!"{tag}: {firstDone c}"
  (← IO.getStdout).flush

def main : IO Unit := do
  report "arr1" (include_str "arr1.bang")
  report "arr2" (include_str "arr2.bang")
  report "arr3" (include_str "arr3.bang")
  report "arr5" (include_str "arr5.bang")

end Bang.Hang61Steps2

def main : IO Unit := Bang.Hang61Steps2.main
