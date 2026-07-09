module

-- Witness examples run `Source.eval`/`Wasmfx.run` (compiled) at the META phase → `meta import`.
meta import Bang.Backend.Wasm
public import Bang.Backend.Wasm

/-! # Refute-first probe: does frozen `compile_forward_sim` hold on CUSTOM handles? ADR-0085 Stage-1.

`compile_forward_sim` is about `Wasmfx.run ∘ compileC` (the WASM machine), NOT `evalD` — `evalD`
custom = none is an INTERMEDIATE (CalcVM) gap the completeness PROOF routes through, but the WASM
HANDLE instruction is handler-AGNOSTIC. VERDICT (compiled `by rfl`): NO custom counterexample
exists — the frozen headline is NOT false on custom; custom-stage1 is a PROOF gap (evalD=none blocks
the completeness route), not a statement falsehood. This is why ADR-0086 premises `CustomFree`
(true-but-unprovable) rather than repairing a false statement. Do-not-weaken regression witness. -/

@[expose] public section

namespace Bang.CustomStage1Refute
open Bang (Val Comp Handler)

/-- (A) custom handle, body RETURNS: BOTH sides reach done 5 (WASM HANDLE mints+pops generically,
matching the kernel). Frozen headline HOLDS here — not a refutation. -/
def cTrivial : Comp := .handle (Handler.custom 0 .vunit []) (.ret (.vint 5))
example : Source.eval 50 cTrivial = Result.done (.vint 5) := by rfl
example : Wasmfx.run 100 (compileC cTrivial) = Result.done (.int 5) := by rfl

/-- (B) custom handle, body PERFORMS a custom op: with STAGE-2 dispatch REAL (ADR-0087), the `myop` clause
services the op and RESUMES — the perform (the whole body) resolves to the clause result `7`, so
`Source.eval = done 7`. (Stage-1 this ESCAPED — `handlesOp custom = false`; the finite rep + real dispatch
is exactly what changed. Kept as the Stage-1→Stage-2 behaviour-shift witness.) -/
def cPerform : Comp :=
  .handle (Handler.custom 0 .vunit [("myop", .ret (.vint 7))])
    (.perform (.vvar 0) "myop" .vunit)
example : Source.eval 50 cPerform = Result.done (.vint 7) := by rfl

end Bang.CustomStage1Refute

end -- @[expose] public section
