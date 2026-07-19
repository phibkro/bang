# PATH-wgcexec-pure-state-floor — expose the first calculated GC helper slice without certifying it

> Extract the smallest theorem-visible code image from the WasmGC emitter, refute the scalar lifetime
> approximation, and land the separately approved exact helper representation without certifying the
> compiler or Wasm semantics.

## Seam

- **From checkpoint**: the GC backend is a differential-tested text emitter with no Lean machine at
  the emission seam; the early-bank plan assumes its scalar `$liveTop` gate images exact liveness.
- **To checkpoint**: the fixed capability-helper prelude is theorem-visible; its scalar counterexample,
  exact membership gate, and pop-through skipped-inner trace are axiom-clean; emitted Wasm uses the exact
  GC-linked live stack selected by ADR-0119.
- **Contract preserved**: helper signatures, frontend acceptance, env/oracle/compiled semantics, valid
  live access, all other escape refusals, and every correctness claim outside the helper/state-cell
  fragment remain unchanged. Emitted bytes intentionally change with the helper implementation.

## Layer

- [ ] Kernel  [x] Compiler  [ ] Surface  [x] Meta (proof boundary and gates)

## Actor journey / observable outcome

- **Actor / need**: a backend verifier needs a theorem-visible first object that is mechanically tied
  to emitted text, without treating differential evidence as general compiler adequacy.
- **Public starting point**: `Bang/Backend/WgcCapCode.lean` and `tools/emit-escape-diff.sh`.
- **Terminal observation**: focused Lean checking reports no axioms for the bounded witnesses; the
  escape gate reports all five cases fail loud, zero XFAILs, and its positive nested-state control prints
  `105` in both oracle and Wasmtime.
- **Adverse / recovery route**: a missing gate id or missing exit target traps. A skipped inner exit is
  cleaned when `$capExit(m)` pops through `m`, while older live frames remain present.
- **Downstream journey released**: the real pure+state `compileGC`/machine/reification simulation, priced
  separately from this helper-level correction.

## Feeds the constraint

- **Binding constraint now**: `scratch/cap-gc/surface-escape/stale-state-reentry.bang` refutes the old
  scalar gate; `exact_exit_pops_through_skipped_inner` additionally fixes unwind cleanup behavior.
- **How this path feeds it**: retain the scalar machine only as a counterexample, mechanically render the
  exact helper code, and keep both positive and negative real-engine differentials load-bearing.

## Prospective systemic review

| concern | horizon + evidence | likelihood / impact / late cost | disposition now | reopen trigger |
|---|---|---|---|---|
| bounded witnesses are advertised as compiler adequacy | no `Comp`, `Source.eval`, or Wasm semantics occurs in `WgcCapCode` | high / critical / high | state exclusions beside the theorems and in this PATH | a compositional reification theorem exists |
| scalar watermark is again called exact | stale reentry mints ids 0 then 1 and revives id 0 | high / critical / high | retain the scalar counterexample beside the exact model | exact representation is removed |
| pop semantics are weakened to strict-pop | throws/txn abort can skip inner exits | high / critical / high | theorem-pin `[inner,middle,outer] → [outer]` | control-flow lowering guarantees explicit cleanup |
| helper implementation false-fires | exact search/pop is new emitted code | medium / critical / high | positive `nested1=105` plus full effects corpus | a compositional helper/Wasm proof exists |
| partial proof displaces broad testing | theorem slice omits closures, throws, txn, custom effects, and Wasm execution | high / high / high | keep emission harnesses load-bearing | the omitted arms gain calculated semantics and proofs |

## Baseline, falsifier, and evidence

- **Baseline / red observation**: `id < liveTop` rejects immediate escape but accepts an older popped id
  after any later handler mint raises `liveTop`.
- **Smallest tracer bullet**: extract only `globals`/`mint`/`exit`/`gate`, render those exact strings
  from `WasmEmit.gcHelpers`, and calculate scalar and exact helper machines over one state box.
- **Positive evidence**: live get/put witnesses, exact gate membership, and the skipped-inner pop-through
  trace are decidable and axiom-clean.
- **Negative or recovery evidence**: the retained scalar stale trace returns `some 7`; exact membership
  returns `none`; env/oracle/compiled keep `5/3/5`, and Wasmtime now fails loud.
- **Broader convergence gate**: focused Lean build, `tools/emit-escape-diff.sh`, rung-5 effects corpus,
  browser artifact/provenance checks, `tools/check-paths.sh`, ADR/doc indexes, and diff hygiene.
- **Assumptions / exclusions**: natural-number ids exclude i64 overflow. There is no theorem here for
  `Comp`, closures, handlers, throws, transactions, custom effects, `Source.eval`, Wasm semantics,
  whole-module rendering, or general emitter correctness.

## Plan

1. [x] Confirm scalar stale reentry across env, oracle, compiled, and emitted engines.
2. [x] Extract the fixed helper text and calculate bounded scalar/exact state-cell models.
3. [x] Add axiom-clean positive and refutation witnesses without enrolling an adequacy headline.
4. [x] Record stale reentry as the tracer's explicit known-red, then remove the XFAIL only with the exact fix.
5. [x] Land the approved ADR-0119 GC-linked exact-live stack with pop-through exit and zero XFAILs.
6. [ ] Only then build `compileGC`/`WgcCode` for a real pure+state reification theorem.

## Status

- [x] Started 2026-07-19
- [x] In flight: bounded tracer and exact-liveness helper correction complete; real `Comp` floor remains
- [ ] Blockers: no helper-to-Wasm semantics or `Comp` reification relation exists yet
- [ ] Completed YYYY-MM-DD
- Retained failed gates / successors: no XFAIL remains in the five-witness gated catalog. Static
  throws tags still admit a potential same-site stale re-entry shape; retain `stale-throws-reentry`
  as a named candidate sixth witness. The next proof door is the real pure+state calculated machine
  and reification theorem.
- Reopen / observe: rerun the positive control, escape catalog, and full effects corpus on any helper or
  handler-control-flow change.

## Owner

- Agent / human: GPT-5.6 Sol engineer, `codex/exact-cap-liveness`

## Notes

The first tracer is intentionally smaller than the early-bank plan. It establishes a calculated helper
machine and executable state-cell witnesses, not the planned `wgcexec ≡ evalD ≡ Source.eval` bridge.
