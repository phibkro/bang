# PATH-resource-contract-tracer — one resource description from source to evidence

> Make one quantitative obligation user-visible and preserve it through checking, lowering,
> concrete execution, and machine-readable evidence before generalizing an ownership system.

## Seam

- **From checkpoint**: completed semantic contracts + stateful handler policy — effects have named
  contracts, laws, swappable realizations, row ceilings, and handler-owned value policy
- **To checkpoint**: one-shot permit tracer — a source program states a value quantity and the
  concrete realization exposes its resource consequence
- **Contract preserved**: effect rows remain sets; quantities live beside rows; the kernel gains no
  primitive; every executable route retains an oracle

## Layer

- [ ] Kernel  [x] Compiler  [x] Surface  [x] Meta (docs/process)

## Feeds the constraint

- **Binding constraint now**: the kernel enforces `0/1/ω`, but the surface defaults every returner,
  arrow, and variable to `ω` (`Bang/Frontend/TypeCheck.lean`); `zero_usage_erasable` remains flagged,
  and the deprecated `zero_grade_no_code` alias explicitly provides no concrete grade-directed
  evidence (`Bang/Spec.lean`, `Bang/Backend/Wasm.lean`).
- **How this path feeds it**: let one unforgeable permit consumer demand one opt-in value-grade
  annotation, then connect its accepted/refused source behavior to concrete Wasm and a generated
  contract/realization/evidence view.

## Acceptance matrix

| Obligation | Required observation |
|---|---|
| consume once | checks and returns the same value on oracle, environment, compiled, and Wasm routes |
| duplicate | rejected statically with a stable diagnostic code |
| forget grade-1 | rejected statically; explicit `drop` is outside the first slice |
| grade-0 | concrete Wasm contains no representation/read for the erased input or binding, and still agrees with the oracle |
| row orthogonality | the permit effect remains an ordinary set member; no weighted-row representation appears |
| realization independence | two named permit handlers satisfy the same contract law |
| evidence | one JSON query joins the contract, quantities, realizations, laws, and evidence level |

The refusal fixtures are written before syntax is chosen. An annotation must be local and opt-in;
unannotated programs keep the compatible `ω` default. Capability capture/lifetime is a separate axis:
the first tracer records the escaping-thunk witness but must not revive the refuted answer-type-shape
check from `docs/notes/scoped-cap-types-design.md`.

## Plan

1. [x] Adopt the semantic-description north star and refresh the product frontier around this consumer.
2. [x] Add accepted, duplicate, forgotten, and grade-0 source fixtures before choosing syntax.
3. [x] Probe binder/arrow placement through the real surface checker and choose the smallest annotation.
4. [x] Record the reversible syntax/checking choice in an ADR; keep rows ungraded and default `ω`.
5. [x] Implement parsing, formatting, checking, diagnostics, lowering, and reference documentation.
6. [x] Demonstrate grade-0 erasure in the concrete emitter with structural and differential gates.
7. [x] Extend the query fact model with a contract card and generate the public evidence view.
8. [ ] Run `just fitness`, `just verify`, the full battery set, and the proof-claim audit.

## Status

- [x] Started 2026-07-18
- [x] In flight: full repository verification
- [x] Blockers: none for this tracer; capability lifetime remains a deliberately separate downstream
  problem until a capture-aware checker design clears the scheduler falsifier
- [ ] Completed YYYY-MM-DD

## Owner

- Agent / human: operator + Codex

## Notes

This path makes the resource axis observable without claiming a general ownership, borrowing, or
session-type system. Grade-1 in-place reuse (Q30), scoped capability lifetime, and actor ownership
transfer are downstream consumers of the same axis, not bundled into this tracer.
