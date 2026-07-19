# PATH-wgcexec-pure-state-floor — expose the first calculated GC helper slice without certifying it

> Extract the smallest theorem-visible code image from the WasmGC emitter, test its state-capability
> lifetime behavior against exact live membership, and preserve the emitted text byte-for-byte.

## Seam

- **From checkpoint**: the GC backend is a differential-tested text emitter with no Lean machine at
  the emission seam; the early-bank plan assumes its scalar `$liveTop` gate images exact liveness.
- **To checkpoint**: the fixed capability-helper prelude is theorem-visible, its bounded state-cell
  behavior and stale-reentry counterexample are axiom-clean, and the next exact-liveness fix has an
  explicit regression gate and proof obligation.
- **Contract preserved**: emitted Wasm text, frontend acceptance, env/oracle/compiled semantics, and
  every correctness claim outside the extracted helper/state-cell fragment remain unchanged.

## Layer

- [ ] Kernel  [x] Compiler  [ ] Surface  [x] Meta (proof boundary and gates)

## Actor journey / observable outcome

- **Actor / need**: a backend verifier needs a theorem-visible first object that is mechanically tied
  to emitted text, without treating differential evidence as general compiler adequacy.
- **Public starting point**: `Bang/Backend/WgcCapCode.lean` and `tools/emit-escape-diff.sh`.
- **Terminal observation**: focused Lean checking reports no axioms for six bounded witnesses; the
  escape gate confirms engines classify stale reentry as escaped while emitted Wasm prints `7` as one
  known-red; representative `.wat` files remain byte-identical across the extraction.
- **Adverse / recovery route**: if a later mint revives a popped capability, the XFAIL remains visible
  and explicitly allowlisted; it may be removed only when emitted Wasm fails loud and an exact-liveness argument
  replaces the refuted scalar equivalence.
- **Downstream journey released**: a separately priced exact-live-membership emitter design followed by
  the real pure+state `compileGC`/machine/reification simulation.

## Feeds the constraint

- **Binding constraint now**: `scratch/cap-gc/surface-escape/stale-state-reentry.bang` is `.escapedCap`
  in the oracle but prints `7` from emitted Wasm; `scalar_revives_stale_cap_after_reentry` and
  `exact_rejects_stale_cap_after_reentry` machine-check the representation mismatch.
- **How this path feeds it**: keep the concrete scalar helper code theorem-visible, distinguish it from
  an exact reference model, and require the differential witness until the emitter representation is
  changed and proved against exact membership.

## Prospective systemic review

| concern | horizon + evidence | likelihood / impact / late cost | disposition now | reopen trigger |
|---|---|---|---|---|
| bounded witnesses are advertised as compiler adequacy | no `Comp`, `Source.eval`, or Wasm semantics occurs in `WgcCapCode` | high / critical / high | state exclusions beside the theorems and in this PATH | a compositional reification theorem exists |
| scalar watermark is again called exact | stale reentry mints ids 0 then 1 and revives id 0 | high / critical / high | retain exact-membership contrast and known-red gate | an emitter representation rejects the witness |
| helper extraction changes output | four representative pre/post `.wat` pairs | low / critical / medium | require byte equality and existing emission differentials | renderer/helper text changes |
| partial proof displaces broad testing | theorem slice omits closures, throws, txn, custom effects, and Wasm execution | high / high / high | keep emission harnesses load-bearing | the omitted arms gain calculated semantics and proofs |

## Baseline, falsifier, and evidence

- **Baseline / red observation**: `id < liveTop` rejects immediate escape but accepts an older popped id
  after any later handler mint raises `liveTop`.
- **Smallest tracer bullet**: extract only `globals`/`mint`/`exit`/`gate`, render those exact strings
  from `WasmEmit.gcHelpers`, and calculate scalar and exact helper machines over one state box.
- **Positive evidence**: four decidable theorems cover live get, put-then-get, and immediate rejection;
  two more pin the stale scalar/exact disagreement. All six are axiom-clean.
- **Negative or recovery evidence**: the scalar stale trace returns `some 7`; exact membership returns
  `none`; env/oracle/compiled return `5/3/5`, while Wasmtime prints `7` with rc 0.
- **Broader convergence gate**: focused Lean build, `tools/emit-escape-diff.sh`, byte comparison,
  `tools/check-paths.sh`, doc pins, import/tool indexes, and diff hygiene.
- **Assumptions / exclusions**: natural-number ids exclude i64 overflow. There is no theorem here for
  `Comp`, closures, handlers, throws, transactions, custom effects, `Source.eval`, Wasm semantics,
  whole-module rendering, or general emitter correctness.

## Plan

1. [x] Confirm scalar stale reentry across env, oracle, compiled, and emitted engines.
2. [x] Extract the fixed helper text and calculate bounded scalar/exact state-cell models.
3. [x] Add axiom-clean positive and refutation witnesses without enrolling an adequacy headline.
4. [x] Keep stale reentry as an explicit allowlisted known-red and prove representative emitted bytes unchanged.
5. [ ] Separately price and approve an exact-live-membership emitter representation before changing it.
6. [ ] Only then build `compileGC`/`WgcCode` for a real pure+state reification theorem.

## Status

- [x] Started 2026-07-19
- [x] In flight: first bounded tracer complete; exact-liveness successor deliberately not implemented
- [ ] Blockers: scalar `$liveTop` is not exact membership; emitter correction requires a separate design
- [ ] Completed YYYY-MM-DD
- Retained failed gates / successors: `surface:stale-state-reentry` is the single known-red; next door is
  exact live-id membership (or another representation proved equivalent), then real fragment adequacy.
- Reopen / observe: rerun the witness on any capability-lifetime helper change; remove its XFAIL only
  when engine and emitted outcomes converge by failing loud.

## Owner

- Agent / human: GPT-5.6 Sol engineer, `codex/lane-wgcexec-floor`

## Notes

The first tracer is intentionally smaller than the early-bank plan. It establishes a calculated helper
machine and executable state-cell witnesses, not the planned `wgcexec ≡ evalD ≡ Source.eval` bridge.
