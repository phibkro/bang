# ADR-0067 · Integer semantics: unbounded ℤ in v1 — width is a verified optimization behind the oracle

<!-- adr-frontmatter -->

- **Status**: Accepted
- **Summary**: v1 `Int` denotes unbounded ℤ — the oracle's existing δ-rule (ADR-0065 `Comp.binop` over Lean `Int`) IS the spec, so the decision costs zero proof rework. Overflow is never undefined (vacuous under ℤ; binding on any future width). Width, if ever introduced, enters through the ORACLE via a new K-ADR — never backend-decided. The Wasm model's misnamed `i32` constructor is renamed; real-Wasm emission (post-v1) ships bignum first, i64 as a later verified optimization.
- **Resolves**: Q25
- **Depends-on**: 0065, 0016

- **Status:** Accepted
- **Date:** 2026-07-05
- **Layer:** K (kernel — pins base-type semantics; constrains the ◊5 backend). **Tag: K-ADR** (semantic).
- **Resolves:** Q25 (`docs/notes/OPEN_QUESTIONS.md`) · the decision half of GitHub **#34** (the
  `i32` rename is the implementation half; #34 closes when it lands).
- **Builds on:** ADR-0065 (`Comp.binop` δ-rules — the oracle's arithmetic this ADR ratifies as spec).
  ADR-0016 (two-hop architecture — invariant #1 "proof rides the reference" is what forces width to
  live in the oracle or nowhere). ADR-0063 (defined fail-loud terminals — the UB-set-is-empty
  discipline extended here to overflow).

## Context — a decision hiding inside a proved theorem

`Val.vint : Int → Val` (`Bang/Core/IR.lean`) carries Lean's arbitrary-precision `Int`, and the Wasm
model's `Val.i32 : Int → Val` (`Bang/Backend/Wasm.lean`) **also** carries an unbounded `Int` — the
constructor name promises 32 bits, the semantics deliver bignum. The ◊5 forward simulation is
therefore proven against an idealized bignum machine. Nothing decided this; it fell out of using the
metalanguage's `Int`. Real WasmFX emission (#6's eventual hardening) that silently emitted `i64.add`
against this spec would be an unsound compiler — exactly the drift the two-hop architecture exists to
make unrepresentable. GitHub #34 / Q25 surfaced the fork; this ADR closes it.

## Decision

1. **v1 `Int` = ℤ, unbounded.** The oracle's δ-rule (ADR-0065) is already this; the spec now *says*
   it instead of implying it. Zero proof rework; headline census untouched.
2. **Width lives in the oracle or nowhere.** Any future fixed-width type (`i64`, wrap or trap) enters
   as a kernel decision — a new K-ADR changing `Comp.binop`'s δ-rule (or adding a sibling base type)
   with the spine re-derived against it. The backend NEVER picks a width the oracle doesn't have.
3. **Overflow is never undefined.** Vacuous under ℤ; binding constraint on any future width ADR
   (wrap or a defined fail-loud terminal — the UB set stays ∅, cf. ADR-0063).
4. **Rename `Wasmfx.Val.i32` → `Wasmfx.Val.int`** (10 sites, one file) so the name stops asserting a
   width nobody decided. Mechanical; census must stay byte-identical.
5. **Real-Wasm emission (post-v1, ◊5+) ships bignum arithmetic first**; an i64 fast path arrives
   later as a *verified optimization* (range-analysis-gated or dynamically guarded), priced when
   performance is actually observable.

## Alternatives rejected

- **Fixed-width i64, wrapping** (the mainstream systems answer). ℤ/2⁶⁴ is a commutative ring, so the
  additive laws survive — but: (a) it forces the δ-rule change + re-derivation of the ~50 binop arms
  across the spine NOW, for performance nobody observes yet (inverts invariant #7's ordering);
  (b) it breaks the *ordered*-ring laws (`<` vs wrap) exactly where the lawful-algebra layer (#24,
  ADR-0040) wants to state them; (c) literal semantics need width normalization. Deferred, not
  refuted — this is the likely shape of the future width ADR if perf demands it.
- **Fixed-width, trap → defined terminal.** Keeps fail-loud but *partializes* arithmetic:
  associativity holds only up to definedness — the worst carrier for #24's total first-class laws.
  Same re-derivation bill as wrapping, plus a new terminal.

## Consequences

- **#6 (compiled path) is unblocked at zero cost** — `bang run --compiled` is `exec∘compile` inside
  Lean, where `Int` is native ℤ.
- **#24 states its laws over true ℤ**: `AddCommGroup Int` etc. are Mathlib instances, dischargeable
  proof-first at ADR-0040's top rung with no width caveats.
- The real cost (bignum at actual Wasm emission) is deferred past v1 and will be priced by a
  measurement, not a guess.
