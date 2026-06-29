# PATH · Rung 4 — reactive cell (reactivity falls out of thunks)

> The LAST v1 MVP product rung (PRD §3.1). Status: **READY** (scoped 2026-06-23). The rung that **validates
> a thesis rather than adding a capability**: reactivity is emergent (ADR-0005), not a new kernel form.

## The thesis (ADR-0005) — already empirically confirmed

A reactive cell is an **unmemoized thunk over a State cell**; each `force` re-samples the current state =
**pull-based reactivity**. Confirmed in the current kernel (no new machinery), via the existing surface:
```
state 0 in (let c = {get} in (let a = put 5 in (let b = put 9 in $c)))   ⟶  9   (re-samples to latest)
state 0 in (let c = {get} in (let z = put 5 in $c))                      ⟶  5
```
So rung 4 **forces no new kernel capability** — it demonstrates the kernel already has it (ADR-0005:
"sampling = forcing in equate position"; PRD: "reactivity falls out"). **Push-based / glitch-free
propagation is the deferred dial** (PRD §6; out of scope).

## GOAL (verifiable)

1. A reactive-cell program runs from source and **re-samples**: `force c` reflects the *current* State
   after each `put` (promote the probe into durable `#guard`/`runYieldsInt` demos in `Surface.lean`).
2. A **liveness law**: a reactive cell always reflects the latest write — for arbitrary `v`,
   `state s in (let c = {get} in (… put v … $c))` yields `v`. **Prove if cheap, else `plausible`-test**
   (it should be a corollary of `get` reading the current threaded cell — the state-dispatch semantics).

## SCOPE — surface + law only (NO kernel, NO new ADR)

- **NO new kernel primitive** (the thesis: reactivity is emergent). If you find you NEED one, STOP and
  report — that would contradict ADR-0005 and is a kernel decision (orchestrator).
- **Surface (`Bang/Frontend/Surface.lean`)**: durable reactive-cell demos (the probe, as `#guard`/`runYieldsInt`).
  Optionally a small helper making "reactive cell" readable (a thunk-over-get), but the existing
  `let c = {get}` + `$c` already expresses it — don't over-build.
- **Law**: the liveness/freshness property. Prefer a Lean proof if it's a short corollary of the state
  semantics; else `plausible`-test it over arbitrary `v` (the rung-2 `#test` pattern). Either rung of the
  ADR-0026 ladder is fine — say which you used.
- The introduce(`:`)/equate(`=`) **surface glyph** distinction (ADR-0005) is **liquid/deferred** — not
  needed for the demo; `let … = {…}` + `$` suffices.

## OUT OF SCOPE

Push-based / glitch-free / scheduled reactivity (the deferred dial) · the `:`/`=` surface spelling ·
dependency-graph / subscription machinery · multi-cell reactive networks · the "silent subscription"
residue (ADR-0005, tracked).

## DELIVERABLE

- `Surface.lean`: reactive-cell demos (re-sampling shown), green via `Source.eval`.
- The liveness law: proven or `plausible`-tested green.
- `just verify` green; **`no_accidental_handling` stays 0-axiom** (◊2 gate — you're surface-only, it must
  not move).
- Finding appended here: was the liveness law cheap to prove, or tested? Did anything about "reactivity =
  unmemoized thunk over state" surprise you (e.g. memoization, fuel, re-entry semantics — ADR-0005
  Revisit-if flags loop/recursion re-entry as an open question; note if you hit it)?

## OWNER

**A single surface IC** (pragmatic-software-engineer) — this is the lightest rung (no kernel, no
metatheory triad). Proof-engineer only if the liveness law is worth proving and fights.

## POINTERS

- **ADR-0005** (reactivity = equation over thunks; sampling = forcing; the decision this rung demonstrates)
  · ADR-0006 (explicit capture) · ADR-0025 (state handler — the cell `get`/`put` read/write).
- PRD §3.1 rung 4 + §6 (reactivity falls out; the dial deferred).
- `Bang/Frontend/Surface.lean`: `runYieldsInt`/`runFrom`, the rung-1 `state`/`get`/`put` demos, the `{e}`/`$`
  thunk+force forms. Pattern: rung 1's State demos are the direct substrate.

## STATUS — ✓ DONE (2026-06-23), commit `b8c86cd`

`just verify` green; ◊2 gate held (surface-only). GOAL.1 (reactive cell runs + re-samples) ✓ ·
GOAL.2 (liveness law) ✓ **and PROVEN** (`cell_reflects_latest`, axioms `[propext]`, in `Audit.lean`) —
exceeded the prove-if-cheap bar. NO kernel edits — the thesis ("reactivity falls out") is validated.

## FINDING — reactivity is free, and it pins one invariant

- **Cheap to PROVE, not tested.** The written `v` only flows `vint v → cell → read back`, never inspected,
  so the machine reduces symbolically over both `s0` and `v`; `rfl` closes it at fuel 80. The verified
  rung was reachable — no `plausible` needed.
- **The thesis held with zero friction — *because the kernel thunk is genuinely unmemoized*.** There is no
  `Comp` memo cache, so `force` re-evaluates by construction. This makes **thunk non-memoization a
  load-bearing semantic invariant of reactivity** — now stated in **ADR-0005** (consequence + revisit-if).
  If thunk memoization were ever added (a perf optimization), this rung breaks silently (a reactive cell
  would freeze on its first sample); `cell_reflects_latest` is the regression test that catches it. This
  is invariant #7 (performance is second-class) earning its keep — a perf change here is a *correctness*
  change.
- **ADR-0005's re-entry open question (loop/recursion re-entry) — NOT hit.** The demos are straight-line,
  single-force. Still open; settle against a real ≥100-line module before final lock (ADR-0005 Revisit-if).
