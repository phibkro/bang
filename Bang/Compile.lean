/-
  Bang/Compile.lean — WasmFX target + compilation primitives.
  ─────────────────────────────────────────────────────────────
    §7 Wasmfx.* — Module, Val, Ty, run, WellTyped, MentionsLocal,
                  HandlerLawful, Wasmfx.HandlerEquiv
    §7 compileC, compileV, compileHandler

  Theorem STATEMENTS (compile_well_typed, compile_forward_sim,
  handler_compiles, zero_grade_no_code) live in Bang/Spec.lean.

  Phase B PROOF_ORDER #3 (the contribution): replace these axioms with
  real defs against a concrete WasmFX module type (Lexa OOPSLA'24 style). -/

import Bang.Core
import Bang.Syntax
import Bang.Operational

namespace Bang

axiom Wasmfx.Module        : Type
axiom Wasmfx.Val           : Type
axiom Wasmfx.Ty            : Type
axiom Wasmfx.run           : Nat → Wasmfx.Module → Result Wasmfx.Val
axiom Wasmfx.WellTyped     : Wasmfx.Module → Prop
axiom Wasmfx.MentionsLocal : Wasmfx.Module → Nat → Prop
axiom HandlerLawful        : Handler → Prop
axiom Wasmfx.HandlerEquiv  : Wasmfx.Module → Handler → Prop

axiom compileC       : Comp → Wasmfx.Module
axiom compileV       : Val  → Wasmfx.Val
axiom compileHandler : Handler → Wasmfx.Module

end Bang
