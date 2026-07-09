/-
  scratch/hang61/StepCount.lean — issue #61, STEP-COUNT vs STEP-COST separation.

  Runtime is steep (r1=2s, r2=6s, r3=12s, super-linear) at TINY term size (4047).
  This probe finds the SMALLEST fuel (step count) at which each real repro
  terminates — separating "many steps" from "few but expensive steps". Combined
  with wall-time (measured via the CLI), it tells us cost = steps × step-cost.

  Compiled run (`--run`, reliable for fuel recursion).
-/
import Bang.Frontend.TypeCheck
import Bang.Core.Semantics.Eval

namespace Bang.Hang61Steps
open Bang Bang.TypeCheck

def r1 : String := include_str "r1.bang"
def r2 : String := include_str "r2.bang"
def r3 : String := include_str "r3.bang"
def rp : String := include_str "rp.bang"

/-- Binary-search-free linear scan up a fine fuel ladder → first fuel that `done`s. -/
def ladder : List Nat :=
  (List.range 60).map (fun i => (i + 1) * 2000)   -- 2000, 4000, …, 120000

def firstDone (c : Comp) : String :=
    match ladder.find? (fun f => match Bang.Source.eval f c with | .done _ => true | _ => false) with
    | some f => s!"done at fuel {f}"
    | none   => "NOT done by 120000"

def report (tag src : String) : IO Unit := do
  match checkAndLower src with
  | .error e => IO.println s!"{tag}: ELAB-ERROR {e.1}"
  | .ok c    => IO.println s!"{tag}: {firstDone c}"
  (← IO.getStdout).flush

def main : IO Unit := do
  report "r1 (1 parse)    " r1
  report "r2 (2 parse)    " r2
  report "r3 (3 parse)    " r3
  report "rp (parse+print)" rp

end Bang.Hang61Steps

def main : IO Unit := Bang.Hang61Steps.main
