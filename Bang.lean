-- Bang library root
-- Re-exports every module of the `Bang` Lean library so `lake build` knows
-- what to compile. Keep this file in sync when adding / removing modules.

-- K1: effect-row algebra (sound unifier)
import Bang.EffectRow

-- Spec spine (Phase A part 2 split — Spec re-exports the rest)
import Bang.Core
import Bang.Mult         -- concrete QTT instance of [Semiring Mult]
import Bang.Syntax
import Bang.Operational
import Bang.LR
import Bang.Compile
import Bang.Spec

-- Syntactic metatheory: weakening + graded substitution (backs subst_value)
import Bang.Metatheory

-- Phase B targets and the audit gate
import Bang.Compat
import Bang.Distribution
import Bang.Audit

-- Tracer bullet: surface → graded-CBPV Comp → Source.eval → value
-- (PATH-tracer-bullet; additive surface layer, outside the verification spine).
import Bang.Surface

-- K3: the calculated machine. The K2 matrix of per-feature machines (Calc/CalcHO/
-- CalcCBN/CalcEff/CalcSt/CalcCBNEff/CalcCBNSt/CalcCBNEffSt) + the untyped CBN reference
-- (Eval) collapsed into the one graded-CBPV `CalcVM` at ◊3 (ADR-0017) and were moved to
-- `archive/` (out of the build — inert proven-evidence, machine-checked in git history).
-- The paused reification frontier (ADR-0015) stays live below.
import Bang.CalcReify
import Bang.CalcReifyRef
import Bang.CalcReifySim
import Bang.CalcVM
