import Bang.Frontend.TypeCheck
import Bang.Core.Semantics

/-! # PROBE (task #29, lane ctr-g1): does the ⊥-row COMPUTING clause body actually RUN?

The G1/tracer question: a pure compute-then-return custom clause body `fetch(n) => n * 10`,
performed twice and summed, should evaluate to `10 + 20 = 30` under `Source.eval` — the TESTED
oracle. If it does, the ONLY gap for G1 is kernel-soundness COVERAGE (`custom_program_safe`),
not runnability. This is the differential evidence: the surface accepts it, it lowers to a
`Comp.letC` body, and it RUNS to the right answer against the kernel `Source.eval`. -/

namespace Bang.CtrTracerRuns

open Bang Bang.Surface

-- lower + run the tracer; expect 30.
open Bang.TypeCheck in
def runTracer (src : String) : Except String (Result Val) := do
  let prog ← Bang.Surface.parseProg src
  let c ← Bang.TypeCheck.checkAndLowerProg prog
  .ok (Source.eval 10000 c)

-- TRACER 1: `n * 10` on fetch(1)+fetch(2) = 10+20 = 30.
#guard (match runTracer
    "effect Net { fetch : Int -> Int } handle (net.fetch(1)) + (net.fetch(2)) with Net as net { fetch(n) => n * 10 }"
  with
  | .ok (.done (.vint 30)) => true
  | _ => false)

-- TRACER 2 (the G1 shape one size up): `let m = n * 2 in m + 1` — a letC-of-letC-of-binop body.
-- On fetch(5): m = 10, m+1 = 11. Single perform.
#guard (match runTracer
    "effect Net { fetch : Int -> Int } handle net.fetch(5) with Net as net { fetch(n) => let m = n * 2 in m + 1 }"
  with
  | .ok (.done (.vint 11)) => true
  | _ => false)

end Bang.CtrTracerRuns
