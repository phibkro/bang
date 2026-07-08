# PATH — inc-6: CalcVM route-B — CORE LANDED; remaining = U5b-handler completeness

> **Status brief.** The ADR-0052 route-B re-derivation is **DONE and on main**: `evalD` is the
> big-step denotation of the IDENTITY kernel (mint+subst `vcap` at handle, `g`-threaded,
> identity-keyed stores), and the bridge headlines `run_evalD` / `sim` / `compile_correct` /
> `evalD_agrees_source` are **axiom-clean** (Audit census). What this PATH still owns is the ONE
> remaining unit: **U5b-handler** — the reverse completeness bridge over handlers, whose absence is
> `compile_forward_sim`'s documented sorryAx (the pure fragment `compile_forward_sim_pure` /
> `source_eval_to_exec` is clean). Deferred to a dedicated fresh increment (operator call
> 2026-06-28). Full unit-by-unit history: this file @ `9bcb5ec` and earlier (git); ADR-0052 + its
> amendment is the decision.

## Feeds the constraint
- **Binding constraint now**: `compile_forward_sim`'s sorryAx (proof-state @ `f826dbc`) is the ◊5
  completeness gap, and the machine coherence layer it rides gates #44 Stage 4 (ADR-0085 Amendment).
- **How this path feeds it**: closing U5b-handler un-flags `compile_forward_sim` +
  `handler_compiles` and hands #44 a fully-proven machine to derive the `custom` arm against.

## Module map (old name → current home)

| old (in git history) | current |
|---|---|
| `Bang/CalcVM.lean` (evalD · exec · bridge) | `Bang/Backend/AbstractMachine.lean` (ns `Bang.CalcVM`) |
| `Bang/Compile.lean` (WASM hop · `wexec`) | `Bang/Backend/Wasm.lean` |
| `Bang/Operational.lean` (kernel dispatch) | `Bang/Core/Semantics{,.Dispatch}.lean` |
| coherence carrier | `Bang/Core/CapCoh.lean` |

## Method grounding (the Bahr–Hutton stack — papers in `references/papers/2-calcvm/`)
- monadic '22 (partiality + strong bisimilarity) + garby '24 (effect interpretation decoupled) —
  both adopted; concurrency '23 (codensity for control) is the conceptual frame for dispatch.
- **garby §6 names first-class handlers as UNSOLVED — bang's calculated handler-dispatch compiler
  is the novel contribution** (invariant #4 made real). No template; the method transfers.

## What landed (each manager-gated on committed content; design moves that matter downstream)
- **U1–U3 + U5a** (branches `inc5-comp-grind`, `inc6-u3-bridge`, `inc6-u5-wasm`; landed via main):
  identity-keyed `evalD`/`compile`/`exec`, the full ~1800-line bridge, and the WASM forward lockstep.
- **HANDLE-defer-recompile**: `compile (handle h M)` carries the RAW body; exec mints `id:=g` and
  re-compiles `subst (vcap id ℓ) M` — the resolution of "compile can't statically read a vvar cap."
  The `custom` arm (#44 Stage 4) inherits this shape.
- **Kind-first stores** (skip non-matching kind, then id) — matches `evalD`'s per-kind store
  structurally; id-uniqueness lives in the bridge (`StratFresh`), not the calculation.
- **Coherence architecture**: thread the WEAK factor `WeakCoh`/`CapLabelCoh`/`FreshCfg`
  (`Bang/Core/CapCoh.lean`) per-step and reassemble full `CapResolves` at the perform seam —
  the AsmFX-precedented bridge across the typing-by-label/dispatch-by-identity gap. Verified 4/4
  by an independent adversarial pass. **This is the layer #44's opaque clause map breaks** —
  `capsH` can't enumerate `OpId → Option Comp` caps; fix = the `VcapFree`-clause invariant (ADR-0085).
- **NoResume as a 5th conjunct** of `run_evalD`'s RAISED conclusion (fold, not a standalone helper).

## Remaining unit — U5b-handler (fully de-risked, fresh-budget, ATOMIC)
The reverse completeness bridge `Source.eval ⟹ evalD` over handlers (~1000 lines = the
store-threaded CONVERSE of `run_evalD`, two-part term+raised, inducting on `Config.run` fuel).
De-risked: the 5 handler-kind `*_composes` lemmas + `perform_get_resolves` are proven axiom-clean
(`scratch/U5bHandlerSpike.lean`); the converse statement builds; frozen `evalD_complete_gen`
follows at `K=[]` via `run_plug_reshape`. Constraint: `compile_forward_sim_pure` /
`source_eval_to_exec` STAY clean. Atomicity: a half-done induction doesn't move the gate — do not
start half-depleted. Resume from branch `inc6-u5b-handler` + the spike trailer.

## Do-not-retry ledger (build-refuted)
- **Congruence-architecture completeness** (`Sim.handle`): route-B's mint+subst needs
  substitution-closure of a behavioral relation — build-disproven; the store-threaded converse is
  the architecture (witness `82cc585`).
- **Determinism shortcut** (soundness + determinism + totality ⇒ completeness): `evalD_total`
  needs the same Sim block; a VcapFree premise gap besides (`scratch/U5DetShortcut.lean` `7ed8da9`).
  `source_determinism` was salvaged and is reusable.
- **Standalone NoResume helper**: raised-`letC`/`app` sub-case needs `ihT` — not separable (fold only).
