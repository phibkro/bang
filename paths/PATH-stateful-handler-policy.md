# PATH-stateful-handler-policy — quota and revocation as handler-owned state

> Test whether runtime handler policy can evolve after each operation while the plugin retains one
> stable capability contract and cannot forge the policy state.

## Seam

- **From checkpoint**: completed `PATH-semantic-contracts` — immutable host allowlists work through
  existing parameter-carrying handlers (ADR-0113)
- **To checkpoint**: a ruled and execution-complete semantic protocol for stateful custom-handler
  policy, followed by a deliberately separate surface-design rung
- **Contract preserved**: policy remains handler-owned; no frontend-only promise may diverge from
  source semantics, CalcVM, the environment machine, or Wasm execution

## Layer

- [x] Kernel  [x] Compiler  [x] Surface  [x] Meta (docs/process)

## Feeds the constraint

- **Binding constraint resolved at core**: `ClauseKey.updating` distinguishes transition envelopes
  from ordinary product results while retaining the ret-shaped, effect-free clause boundary.
- **How this path feeds it**: use a one-request quota as the consumer, choose the smallest semantic
  update protocol before touching the kernel, then derive rather than patch every execution route.

## Plan

1. [x] Trace custom parameter semantics through core typing/dispatch, CalcVM, environment machine,
   frontend lowering/checking, and existing ADR commitments.
2. [x] Pin the smallest external-state attempt through `bang check --json`; it rejects with `B005`
   because `quota.put(0)` makes the clause effectful before resume.
3. [x] Rule the architecture fork documented in
   `docs/notes/stateful-handler-policy-probe.md`: handler-local parameter update (recommended),
   general effectful clauses, or explicit deferral.
4. [x] Land ADR-0114's hand-built core quota witness and source transition before surface
   syntax; derive CalcVM/environment/Wasm behavior and re-establish the proof/audit gates.
5. [x] Add the surface protocol, a two-request quota example, diagnostics, reference material, and
   end-to-end differential regressions.

## Status

- [x] Started 2026-07-18
- [x] In flight: closed — all semantic routes and the public surface agree
- [x] Blockers: none
- [x] Completed 2026-07-18

## Owner

- Agent / human: operator + Codex

## Notes

The operator approved option A on 2026-07-18. ADR-0114 corrects the earlier pair-shape proposal:
plain product results and state-transition envelopes cannot be distinguished by value shape, so
the core clause key records `plain` versus `updating` explicitly. The ret-shaped first slice installs
the next parameter atomically; general effectful update computations remain out of scope. The
surface spelling is `update op(x) => (resumeValue, nextParam)`, with `op(x) => body` preserving
plain behavior. `examples/stateful-quota/` is the public two-request oracle (`10`), gated through
the oracle, environment and compiled machines, WasmGC differential emission, and the distributable
`bang build` binary-artifact path (`wasm-tools` validation + Wasmtime execution).
