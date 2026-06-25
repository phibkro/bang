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
-- Laws-as-algebraic-interfaces surface (ADR-0040): trait/impl + the proof-first
-- discharge ladder. In the build graph so its #guards GATE (proof-first default,
-- visible descent, no-silent-pass enforced by construction).
import Bang.Surface.Trait
-- Frontend (the human/agent-facing edge of the V — depends on Core, never on Backend).
-- The canonical core made WRITABLE (ADR-0046 ①): named-explicit S-expression IR with a
-- print/read round-trip gate + name→de-Bruijn elaboration. The plugin/LSP surface (ADR-0047).
import Bang.Frontend.NamedCore

-- K3: the calculated machine. The K2 matrix of per-feature machines (Calc/CalcHO/
-- CalcCBN/CalcEff/CalcSt/CalcCBNEff/CalcCBNSt/CalcCBNEffSt) + the untyped CBN reference
-- (Eval) collapsed into the one graded-CBPV `CalcVM` at ◊3 (ADR-0017); the matrix is
-- retired to git history (`87d5aeb`; the `archive/` corpus was removed 2026-06-25 — git is
-- the single source). The paused reification frontier (ADR-0015) stays live below.
import Bang.CalcReify
import Bang.CalcReifyRef
import Bang.CalcReifySim
import Bang.CalcVM
