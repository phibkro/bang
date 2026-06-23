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

-- K2: legacy untyped CBN reference (Bang.Eval namespace; no clash with Bang)
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
import Bang.CalcVM
