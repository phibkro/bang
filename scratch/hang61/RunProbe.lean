/-
  scratch/hang61/RunProbe.lean — issue #61, RUNTIME step-cost curve.

  Term size was LINEAR (SizeProbe) — so the cost is at RUNTIME. This probe runs
  `Source.eval` at a LADDER of fuel bounds on the minimal sib programs and reports
  the outcome (done / outOfFuel) at each. A COMPILED harness (`def main` + native run) —
  the repo gotcha bans `lake env lean` #eval for fuel recursion; a compiled exe is
  the reliable measurement.

  Reports, per program, the SMALLEST fuel at which it terminates (or "outOfFuel@F" if it
  is still out of fuel at bound F) — the step count to completion. A geometric
  step-count in N (sibling count) or in input length localizes the cliff.

  Build+run: nix develop -c lake env lean --run scratch/hang61/RunProbe.lean
  (--run compiles then executes `main`, reliable for fuel recursion).
-/
import Bang.Frontend.TypeCheck
import Bang.Core.Semantics.Eval

namespace Bang.Hang61Run
open Bang Bang.TypeCheck

/-- Run one source at a fuel bound, report a compact outcome tag. -/
def runAt (src : String) (fuel : Nat) : String :=
  match checkAndLower src with
  | .error _ => "ELAB-ERROR"
  | .ok c =>
    match Bang.Source.eval fuel c with
    | .done _     => s!"done@{fuel}"
    | .outOfFuel  => s!"outOfFuel@{fuel}"
    | .escapedCap => s!"escaped@{fuel}"
    | .stuck      => s!"stuck@{fuel}"

/-- Find the smallest fuel in `ladder` at which the program is `done`; else report the
last (largest) outcome. -/
def firstDone (src : String) (ladder : List Nat) : String :=
  match ladder.find? (fun f =>
    match checkAndLower src with
    | .ok c => match Bang.Source.eval f c with | .done _ => true | _ => false
    | _ => false) with
  | some f => s!"DONE at fuel {f}"
  | none   => s!"NOT done by fuel {ladder.getLast!} → {runAt src ladder.getLast!}"

def ladder : List Nat := [10, 50, 100, 500, 1000, 5000, 20000, 100000]

def s1 : String := include_str "sib1.bang"
def s2 : String := include_str "sib2.bang"
def s3 : String := include_str "sib3.bang"

def main : IO Unit := do
  IO.println s!"sib1 (1 nested): {firstDone s1 ladder}"
  IO.println s!"sib2 (2 nested): {firstDone s2 ladder}"
  IO.println s!"sib3 (3 nested): {firstDone s3 ladder}"

end Bang.Hang61Run

def main : IO Unit := Bang.Hang61Run.main
