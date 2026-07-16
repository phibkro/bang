import Bang.Backend.Wasm

/-! # Refute-first probe: does frozen `compile_forward_sim` hold on CUSTOM handles? (ADR-0085 Stage-1)

Manager's deciding experiment. `compile_forward_sim` is about `Wasmfx.run ∘ compileC` (the WASM
machine), NOT `evalD` — `evalD` custom = none is an INTERMEDIATE (CalcVM) gap the completeness PROOF
routes through, but the WASM HANDLE instruction is handler-AGNOSTIC. VERDICT (compiled `by rfl`):
NO custom counterexample exists — the frozen headline is NOT false on custom; custom-stage1 is a
PROOF gap (evalD=none blocks the completeness route), not a statement falsehood. -/

namespace Bang.CustomStage1Refute
open Bang (Val Comp Handler)

/-- (A) custom handle, body RETURNS: BOTH sides succeed with 5 (source `done`, abstract target
`some`; the WASM HANDLE mints+pops generically, matching the kernel). Frozen headline HOLDS here
— not a refutation. -/
def cTrivial : Comp := .handle (Handler.custom 0 .vunit (fun _ => none)) (.ret (.vint 5))
example : Source.eval 50 cTrivial = Result.done (.vint 5) := by rfl
example : Wasmfx.run 100 (compileC cTrivial) = some (.int 5) := by rfl

/-- (B) custom handle, body PERFORMS a custom op: the kernel does NOT reach done — custom dispatch is
INERT (handlesOp custom = false ⇒ idDispatch none ⇒ the perform ESCAPES). So the frozen headline's
HYPOTHESIS `Source.eval = done` is FALSE ⇒ the implication is VACUOUS, not violated. -/
def cPerform : Comp :=
  .handle (Handler.custom 0 .vunit (fun op => if op == "myop" then some (.ret (.vint 7)) else none))
    (.perform (.vvar 0) "myop" .vunit)
example : Source.eval 50 cPerform = Result.escapedCap := by rfl

end Bang.CustomStage1Refute
