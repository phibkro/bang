-- Bang library root
-- Re-exports every module of the `Bang` Lean library so `lake build` knows
-- what to compile. Keep this file in sync when adding / removing modules.

-- K1: effect-row algebra (sound unifier)
import Bang.EffectRow

-- K2: definitional reference interpreter (un-graded CBN K2 source)
import Bang.Eval

-- K3: calculated machines (collapsing into one graded-CBPV machine at ◊3
-- per ADR-0017; currently un-graded artifacts)
import Bang.Calc
import Bang.CalcHO
import Bang.CalcCBN
import Bang.CalcEff
import Bang.CalcSt
import Bang.CalcCBNEff
import Bang.CalcCBNSt
import Bang.CalcCBNEffSt
import Bang.CalcReify
import Bang.CalcReifyRef
import Bang.CalcReifySim

-- wasmfx spec (graded-CBPV + LR + WasmFX target)
import Bang.Spec
import Bang.Compat
import Bang.Distribution
import Bang.Audit
