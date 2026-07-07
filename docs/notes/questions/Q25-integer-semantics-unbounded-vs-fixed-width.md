---
type: design-question
title: "Integer semantics: unbounded Int vs fixed-width (width + overflow)"
description: "spec Int = unbounded ℤ v1 (matches the oracle); width lives behind the oracle, a later verified opt"
status: decided
area: type-system
resolved-by: ["ADR-0067"]
ties: ["ADR-0063", "ADR-0065", "ADR-0067"]
see-also: ["#34", "#6", "Bang/Backend/Wasm.lean"]
---
**Question**: what is the *specified* semantics of `Int` — arbitrary precision (what the kernel oracle
computes today) or fixed-width (i32/i64) with a defined overflow behavior?

**Why it matters**: the decision is currently *hiding inside a proved theorem*. `Val.vint : Int → Val`
is Lean's unbounded `Int`, and the Wasm model's `Val.i32` (`Bang/Backend/Wasm.lean`) ALSO carries an
unbounded `Int` — the constructor name promises 32 bits, the semantics deliver bignum. So the ◊5
forward sim is proven against an idealized bignum machine; real WasmFX emission (#6) that emitted
`i64.add` against this spec would be an unsound compiler. GitHub **#34** tracks the work.

**Detail**: whichever way it goes, width lives in the ORACLE or nowhere — `Source.eval`'s δ-rule
(`Comp.binop`, ADR-0065) defines arithmetic, and invariant #1 (proof rides the reference) forbids the
backend from quietly deciding it. Overflow may never be *undefined*: the UB set is empty by
construction (fail-loud invariant, cf. `escapedCap` ADR-0063).

**Options**: (1) **spec Int = unbounded**; the Wasm runtime ships bignum arithmetic — matches the
oracle by construction, zero proof rework now; an i64 fast path becomes a later *verified
optimization* (slow-but-correct, invariant #7). (2) **fixed-width i64, wrapping** (two's complement)
— the mainstream systems answer; requires changing the kernel δ-rule to wrap + re-deriving the
spine's binop arms + the sim. (3) **fixed-width, trap → defined terminal** — overflow becomes a
fail-loud terminal like `escapedCap`; same proof rework as (2) plus a new terminal.

**Recommended**: (1) for v1 — correct by construction against the existing census; defer width to a
verified-optimization decision when #6 makes performance observable. Immediate cheap step regardless:
rename the Wasm constructor `i32` → `int` so the name stops asserting an undecided width.

**Blocked on**: nothing — an ADR closes it. Must land before #6 (compiled path) starts.

**Revisit signal**: starting #6; or perf pressure on arithmetic benchmarks; or the lawful-algebra
layer (#24) wanting `Int` instances whose laws depend on width (overflow breaks associativity-with-
bounds claims).
